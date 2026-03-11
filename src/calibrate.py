"""
ハイパースペクトル輝度キャリブレーションスクリプト
  calibrated = (scan - dark) / (white * x - dark)

実行するとGUIでファイル/フォルダを選択するダイアログが開く。
補正倍率 x は下の「設定」セクションで変更する。
"""

# =============================================================================
# 設定 — ここの値を適宜変更する
# =============================================================================

X          = 1.2   # 白参照輝度への補正倍率
CHUNK_LINES = 64   # 一度に処理するライン数（増やすと速く・メモリ消費大）

# =============================================================================

import re
import tkinter as tk
from pathlib import Path
from tkinter import filedialog, messagebox

import numpy as np
from PIL import Image
from tqdm import tqdm


# ---- ENVI ヘッダ読み書き -----------------------------------------------

def read_envi_header(hdr_path: Path) -> dict:
    with open(hdr_path, "r", encoding="utf-8", errors="replace") as f:
        content = f.read()
    content = re.sub(r"\{[^}]*\}", lambda m: m.group().replace("\n", " "), content)
    header = {}
    for line in content.splitlines():
        if "=" in line:
            key, _, val = line.partition("=")
            header[key.strip().lower()] = val.strip()
    return header


def write_envi_header(hdr_path: Path, header: dict) -> None:
    with open(hdr_path, "w", encoding="utf-8") as f:
        f.write("ENVI\n")
        for key, val in header.items():
            if key == "envi":
                continue
            f.write(f"{key} = {val}\n")


DTYPE_MAP = {
    "1": np.uint8,  "2": np.int16,   "3": np.int32,
    "4": np.float32, "5": np.float64,
    "12": np.uint16, "13": np.uint32,
}


def open_envi_memmap(raw_path: Path, hdr_path: Path):
    """RAW ファイルをメモリマップで開く（RAM に全展開しない）。
    戻り値: (memmap shape=(lines,bands,samples), hdr dict)
    """
    hdr     = read_envi_header(hdr_path)
    lines   = int(hdr["lines"])
    samples = int(hdr["samples"])
    bands   = int(hdr["bands"])
    offset  = int(hdr.get("header offset", "0"))
    dtype   = DTYPE_MAP[hdr.get("data type", "12").strip()]

    mm = np.memmap(raw_path, dtype=dtype, mode="r", offset=offset,
                   shape=(lines, bands, samples))
    return mm, hdr


# ---- TIF 参照画像の読み込み ---------------------------------------------

def load_ref_tif(tif_path: Path) -> np.ndarray:
    """float32 で読み込む（float64 は不要）"""
    arr = np.array(Image.open(tif_path), dtype=np.float32)
    if arr.ndim == 2:
        return arr
    elif arr.ndim == 3:
        return arr.mean(axis=0).astype(np.float32)
    raise ValueError(f"予期しない次元数: {arr.ndim}  ({tif_path})")


# ---- キャリブレーション (チャンク処理) ----------------------------------

EPS     = 1e-6   # ゼロ除算防止
MIN_WD  = 100.0  # 分母下限（S/N 低い → NaN）
MAX_REF = 1.1    # 反射率上限（異常値 → NaN）


def calibrate_chunked(scan_mm: np.ndarray, dark: np.ndarray, white: np.ndarray,
                      x: float, f_out, chunk_lines: int) -> None:
    """
    C# ApplyCalibration と同一アルゴリズム:
      wd  = white * x - dark
      sd  = max(raw - dark, 0)
      r   = sd / (wd + EPS)
      wd < MIN_WD  → NaN
      r  > MAX_REF → NaN
      r  > 1.0     → 1.0
    """
    lines = scan_mm.shape[0]

    # 分母を事前計算 (bands, samples) float32
    wd       = (white * np.float32(x) - dark).astype(np.float32)
    low_mask = wd < MIN_WD   # S/N 不足マスク (bands, samples)

    with tqdm(total=lines, unit="line", desc="calibrating") as pbar:
        for start in range(0, lines, chunk_lines):
            end = min(start + chunk_lines, lines)

            # sd = raw - dark, 負値は 0 にクランプ
            sd = np.maximum(scan_mm[start:end].astype(np.float32) - dark, 0.0)

            # r = sd / (wd + EPS)
            r = sd / (wd + EPS)

            # wd < MIN_WD → NaN
            r[:, low_mask] = np.nan

            # r > MAX_REF → NaN
            r[r > MAX_REF] = np.nan

            # r > 1.0 → 1.0
            np.minimum(r, 1.0, out=r)

            # float(0-1) → uint16(0-65535)  NaN は C# 同様 0 に
            r[np.isnan(r)] = 0.0
            out_u16 = (r * 65535.0).astype(np.uint16)
            out_u16.tofile(f_out)
            pbar.update(end - start)


# ---- サフィックス生成 ---------------------------------------------------

def x_suffix(x: float) -> str:
    return f"_x{x:.6g}"


# ---- GUI 入力 -----------------------------------------------------------

def select_inputs():
    """
    GUI でプロジェクトフォルダと補正倍率 x を取得して返す。
    キャンセル時は (None, None, None) を返す。

    期待するフォルダ構造:
      project/
        raw/scan.raw
        raw/scan.hdr
        ref/dark.tif
        ref/white.tif
    """
    from tkinter import simpledialog

    root = tk.Tk()
    root.withdraw()

    # --- プロジェクトフォルダ選択 ---
    project = filedialog.askdirectory(title="プロジェクトフォルダを選択 (raw/ と ref/ を含むフォルダ)")
    if not project:
        messagebox.showwarning("キャンセル", "フォルダが選択されませんでした。終了します。")
        root.destroy()
        return None, None, None

    project = Path(project)
    scan_raw = project / "raw" / "scan.raw"
    ref_dir  = project / "ref"

    # 必要ファイルの存在確認
    missing = [str(p) for p in [scan_raw, ref_dir / "dark.tif", ref_dir / "white.tif"] if not p.exists()]
    if missing:
        messagebox.showerror("ファイルが見つかりません", "\n".join(missing))
        root.destroy()
        return None, None, None

    # --- 補正倍率 x 入力 ---
    x = simpledialog.askfloat(
        "補正倍率",
        "白参照輝度への補正倍率 x を入力してください。",
        initialvalue=X,
        minvalue=0.0001,
    )
    if x is None:
        messagebox.showwarning("キャンセル", "補正倍率が入力されませんでした。終了します。")
        root.destroy()
        return None, None, None

    root.destroy()
    return scan_raw, ref_dir, x


# ---- メイン -------------------------------------------------------------

def main():
    scan_raw, ref_dir, x = select_inputs()
    if scan_raw is None:
        return

    scan_hdr = scan_raw.with_suffix(".hdr")
    suffix   = x_suffix(x)
    # with_suffix() を使わず文字列結合でパス生成（x=1.2 のとき .2 が拡張子と誤認されるのを防ぐ）
    out_raw  = scan_raw.parent / f"scan_calibrated{suffix}.raw"
    out_hdr  = scan_raw.parent / f"scan_calibrated{suffix}.hdr"

    print(f"[入力]  scan  : {scan_raw}")
    print(f"[入力]  dark  : {ref_dir / 'dark.tif'}")
    print(f"[入力]  white : {ref_dir / 'white.tif'}")
    print(f"[補正]  x = {x}")
    print(f"[出力]  {out_raw}")

    # 出力ファイルを先に開く（memmapより前に開くことでWindowsのファイルロック問題を回避）
    f_out = open(str(out_raw), "wb")

    # データ読み込み
    print("scan をメモリマップで開いています...")
    scan_mm, hdr = open_envi_memmap(scan_raw, scan_hdr)

    print("dark / white を読み込み中...")
    dark  = load_ref_tif(ref_dir / "dark.tif")
    white = load_ref_tif(ref_dir / "white.tif")

    lines, bands, samples = scan_mm.shape
    print(f"  scan : {scan_mm.shape}  dark : {dark.shape}  white : {white.shape}")

    if dark.shape != (bands, samples) or white.shape != (bands, samples):
        f_out.close()
        raise ValueError(
            f"参照画像の shape が不一致\n"
            f"  期待: ({bands}, {samples})\n"
            f"  dark : {dark.shape}\n"
            f"  white: {white.shape}"
        )

    # キャリブレーション & 保存 (チャンク処理)
    print(f"キャリブレーション実行中... (chunk={CHUNK_LINES} lines)")
    calibrate_chunked(scan_mm, dark, white, x, f_out, CHUNK_LINES)
    f_out.close()

    old_desc = hdr.get("description", "{}").strip("{} ")
    new_hdr = dict(hdr)
    new_hdr["data type"]   = "12"  # uint16（C# と同じ）
    new_hdr["description"] = f"{{calibrated from {scan_raw.name}, x={x}, {old_desc}}}"
    write_envi_header(out_hdr, new_hdr)
    print(f"保存中: {out_hdr}")

    root = tk.Tk()
    root.withdraw()
    messagebox.showinfo(
        "完了",
        f"キャリブレーション完了!\n\n"
        f"補正倍率 x = {x}\n"
        f"出力: {out_raw.name}"
    )
    root.destroy()
    print("完了!")


if __name__ == "__main__":
    main()
