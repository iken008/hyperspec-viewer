# Hyperspectral Viewer

[English version](README.md)

ハイパースペクトル画像データの可視化・解析のためのデスクトップアプリケーションです。

## 機能

- グレースケール・疑似カラー RGB ハイパースペクトル画像のインタラクティブな可視化
- 点およびポリゴンによるスペクトル抽出
- スペクトル前処理（メディアンフィルタ・Savitzky-Golay・SNV）
- Reflectance / Absorbance モード切替
- スペクトルプロット上へのバンド位置ライン表示（グレー：黒線、RGB：R/G/B色）
- プロジェクト状態の JSON 保存・読み込み（波長位置・カラーマップ・アクティブタブ・バンドライン状態）
- スペクトルの CSV エクスポート
- 効率的な操作のためのキーボードショートカット
- ヘルプメニューによるショートカット一覧表示（`F1`）

## 必要環境

- Python 3.8+
- numpy, scipy, matplotlib, spectral

```bash
pip install numpy scipy matplotlib spectral
```

注: tkinter は Windows / macOS の Python に同梱されています。Linux の場合: `sudo apt-get install python3-tk`

## 使い方

```bash
python spectral_viewer.py
```

### スタンドアロン実行ファイルのビルド

PyInstaller を使って `.exe` ファイルを作成できます：

```bash
pyinstaller .\src\spectral_viewer_v1.7.9.py --onefile --noconsole --icon=icon/original_mag_trsp_64x64.ico
```

ビルドされた実行ファイルは `dist/` フォルダに生成されます。

### クイックスタート

1. `O` キーで HDR ファイルを開く
2. 画像をクリックして点スペクトルを取得
3. `I` キーでポリゴンモードを有効にして領域を解析
4. `4` でメタデータ保存、`5` で画像保存、`6` で CSV エクスポート

### キーボードショートカット

| キー                       | 機能                                         |
| -------------------------- | -------------------------------------------- |
| `O`                      | HDR ファイルを開く                           |
| `L`                      | メタ JSON を読み込む                         |
| `4`                      | メタ JSON を保存                             |
| `5`                      | PNG を保存                                   |
| `6`                      | CSV をエクスポート                           |
| `7`                      | スペクトルをリセット                         |
| `M`                      | Reflectance / Absorbance モード切替          |
| `1` / `2` / `3`      | ノイズ除去 / スムージング / SNV の ON・OFF   |
| `A`                      | 画像タブを切替（グレー / 疑似カラー RGB）    |
| `T`                      | パネルタブを切替（Plot Range / Points List） |
| `I`                      | ポリゴン描画モードの ON・OFF                 |
| `V`                      | 全アノテーションの表示・非表示切替           |
| `W`                      | フルスクリーン切替                           |
| `Q`                      | キャンセル / ダイアログを閉じる              |
| `F1`                     | キーボードショートカット一覧を開く           |
| `BackSpace` / `Delete` | 最後に追加したマーカーを削除                 |
| `F2`                     | 選択中アイテムのラベルを編集（Points List）  |

## メタ JSON

プロジェクト状態は JSON ファイルとして保存され、以下の情報が含まれます：

- スペクトル前処理の設定
- プロット範囲（X 軸・Y 軸）
- グレー画像の波長とカラーマップ
- 疑似カラー RGB の各チャンネル波長
- アクティブな画像タブ（グレー / 疑似カラー RGB）
- バンドライン表示の ON・OFF 状態
- 点・ポリゴンのアノテーション（座標・ラベル名・表示状態）

## Tips

### 複数サンプルのスペクトルを重ねて比較する

異なるサンプルのメタ JSON ファイルを順次読み込むことで、複数の HDR ソースのスペクトルを同一グラフ上に重ね描きして比較できます。各メタファイルにはアノテーションとともに参照元 HDR のパスが記録されているため、ファイルを開き直すことなく異なるサンプル間の比較計測が可能です。

## ファイル形式

**入力**: ENVI 形式（`.hdr` + バイナリデータ）

**出力**:

- メタ JSON（プロジェクト状態）
- CSV（スペクトルデータ）
- PNG（画像）

## ライセンス

MIT License - Copyright (c) 2025 Kenya Iijima (iken008)

KLV 株式会社のスペクトルビューアチュートリアルをベースにしています。
https://www.klv.co.jp/corner/spectral-python-viewer.html

## 著者

Kenya Iijima ([@iken008](https://github.com/iken008))
