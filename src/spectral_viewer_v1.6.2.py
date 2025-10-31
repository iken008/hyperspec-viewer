# -*- coding: utf-8 -*-
"""
Hyperspectral Viewer — Enhanced Edition
Author: iken008 (Kenya Iijima)
Year: 2025

This software is an expanded and modified version based on the 
spectral viewer tutorial distributed at:
https://www.klv.co.jp/corner/spectral-python-viewer.html
© KLV Co., Ltd.  (original tutorial content)
No explicit license was provided for the sample code, so the
original viewer concept and initial structure are credited to KLV.
All extended functionality and modifications are © 2025 iken008.

Key extensions include:
- Multi-point & polygon annotation with persistence
- Polygon mean/std & export
- Spectral preprocessing (median, SG, SNV)
- Multi-HDR source support and meta JSON round-trip
- Range-limited processing for speed / caching
- CSV export with master-wavelength interpolation
- UI/UX improvements, hotkeys, color-phase stability, etc.

License: MIT (applies to modifications by iken008 only)
This program is provided as-is, without warranty of any kind.
"""

# “Tools should be kind to humans.”
#   — iken008, 2025

# === Setup & Imports =========================================================
from __future__ import annotations

import os
import json
import csv
from typing import Any, Dict, List, Optional, Sequence, Tuple

import tkinter as tk
from tkinter import ttk, filedialog, messagebox

import numpy as np
import spectral  # type: ignore

import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
from matplotlib.figure import Figure
from matplotlib.path import Path
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
from matplotlib.ticker import AutoMinorLocator

from scipy.signal import savgol_filter, medfilt


# === Constants (was magic numbers) ==========================================
APP_TITLE: str = "Hyperspectral Viewer (powered by KLV)"
APP_GEOMETRY: str = "1350x700"

DELETE_RADIUS_PX: int = 8
FIG_DPI: int = 100
SAVE_DPI: int = 150

PERCENTILE_LOW: int = 2
PERCENTILE_HIGH: int = 98

TAB10_CYCLE: int = 10

# SG smoothing defaults
SG_POLYORDER: int = 2
SG_BASE_WIN: int = 15
SG_MIN_WIN: int = 3

# Median (denoise) defaults
MED_BASE_WIN: int = 7
MED_MIN_WIN: int = 3


# === UI Root ================================================================
class HyperspecTk(tk.Tk):
    """
    Main Tk application. Refactor note:
    - Only layout/organization improved. Logic/behavior kept identical.
    """
    # --------------------------------------------------------------------- #
    # Construction
    # --------------------------------------------------------------------- #
    def __init__(self) -> None:
        super().__init__()
        self.title(APP_TITLE)
        self.geometry(APP_GEOMETRY)

        # --- State (unchanged) ---
        self.img = None
        self.data: Optional[np.ndarray] = None            # (H, W, B)
        self.wavelengths: Optional[np.ndarray] = None     # (B,)
        self.gray_band: int = 0
        self.rgb_bands: Dict[str, Optional[int]] = {"R": None, "G": None, "B": None}
        self.cmap_name = tk.StringVar(value="gray")
        self._snapping: bool = False
        # ---- Color palette (fixed 10) & separate indices ----
        self._palette10 = [plt.cm.tab10(i) for i in range(10)]

        # points: {"x","y","color","label","source"}
        self.points: List[Dict[str, Any]] = []
        self.external_spectra: List[Any] = []  # reserved
        self._pt_color_idx = 0      # 点用の色インデックス
        self.mode_var = tk.StringVar(value="Reflectance")  # "Reflectance" or "Absorbance"

        # caches
        self._hsi_cache: Dict[str, Tuple[Optional[np.ndarray], Optional[np.ndarray]]] = {}
        self._pt_raw_cache: Dict[Tuple[str, int, int], np.ndarray] = {}
        self._pt_proc_cache: Dict[Tuple, np.ndarray] = {}
        self._poly_idx_cache: Dict[Tuple[str, Tuple[Tuple[int, int], ...]], np.ndarray] = {}
        self._poly_proc_cache: Dict[Tuple, Tuple[np.ndarray, np.ndarray, np.ndarray, int]] = {}

        # polygons
        self.polygons: List[Dict[str, Any]] = []
        self._pg_color_idx = 0      # ポリゴン用の色インデックス
        self.poly_mode = tk.BooleanVar(value=False)
        self._poly_drawing_axes = None
        self._poly_temp_verts: List[Tuple[int, int]] = []

        # Build UI
        self._build_menu()
        self._build_topbar()
        self._build_panes()
        self._build_left_tabs()
        self._build_right_panel()
        self._set_sliders_state(tk.DISABLED)

        # Hotkeys
        self._setup_hotkeys()

    # --------------------------------------------------------------------- #
    # UI Builders
    # --------------------------------------------------------------------- #
    def _build_menu(self) -> None:
        m = tk.Menu(self)
        f = tk.Menu(m, tearoff=False)
        f.add_command(label="Load Meta JSON...", command=self.load_meta_json)
        f.add_command(label="Open HDR...", command=self.open_hdr)
        f.add_separator()
        f.add_command(label="Save Meta JSON...", command=self.on_save_meta_only)
        f.add_command(label="Save Images (PNG)...", command=self.on_save_figure)
        f.add_command(label="Export Spectra CSV...", command=self.on_export_csv_spectra_only)
        f.add_separator()
        f.add_command(label="Exit", command=self.destroy)
        m.add_cascade(label="File", menu=f)
        self.config(menu=m)

    def _build_topbar(self) -> None:
        top = ttk.Frame(self); top.pack(fill=tk.X, padx=8, pady=(6, 4))
        ttk.Button(top, text="Load Meta...", command=self.load_meta_json).pack(side=tk.LEFT)
        ttk.Button(top, text="Open HDR...", command=self.open_hdr).pack(side=tk.LEFT, padx=(8, 0))
        self.path_var = tk.StringVar(value="-")
        ttk.Label(top, textvariable=self.path_var).pack(side=tk.LEFT, padx=10)

    def _build_panes(self) -> None:
        self.pw = ttk.PanedWindow(self, orient=tk.HORIZONTAL)
        self.pw.pack(fill=tk.BOTH, expand=True, padx=6, pady=(0, 6))
        self.left = ttk.Frame(self.pw)
        self.right = ttk.Frame(self.pw)
        self.pw.add(self.left, weight=4)
        self.pw.add(self.right, weight=1)

        # Shortcuts for deletion
        self.bind('<BackSpace>', self.on_delete_last_marker)
        self.bind('<Delete>', self.on_delete_last_marker)

    def _build_left_tabs(self) -> None:
        self.nb = ttk.Notebook(self.left)
        self.nb.pack(fill=tk.BOTH, expand=True, padx=6, pady=0)

        # --- Gray tab ---
        self.tab_gray = ttk.Frame(self.nb)
        self.nb.add(self.tab_gray, text="Gray Image")

        row = ttk.Frame(self.tab_gray); row.pack(fill=tk.X, padx=6, pady=(6, 0))
        ttk.Label(row, text="Wavelength:").pack(side=tk.LEFT)
        self.gray_scale_var = tk.DoubleVar(value=0.0)
        self.gray_scale = tk.Scale(
            row, variable=self.gray_scale_var, command=self.on_gray_scale,
            orient=tk.HORIZONTAL, length=480, width=16, sliderlength=18,
            from_=0.0, to=0.0, resolution=1.0, showvalue=True
        )
        self.gray_scale.pack(side=tk.LEFT, padx=(8, 12))
        self.gray_sel_var = tk.StringVar(value="-")
        ttk.Label(row, textvariable=self.gray_sel_var).pack(side=tk.LEFT)

        row2 = ttk.Frame(self.tab_gray); row2.pack(fill=tk.X, padx=6, pady=6)
        ttk.Label(row2, text="Colormap:").pack(side=tk.LEFT)
        cmaps = ["gray", "viridis", "magma", "plasma", "inferno", "cividis", "jet", "turbo", "gnuplot2"]
        self.cmap_cb = ttk.Combobox(row2, state="readonly", values=cmaps, textvariable=self.cmap_name, width=12)
        self.cmap_cb.pack(side=tk.LEFT, padx=6)
        self.cmap_cb.bind("<<ComboboxSelected>>", lambda e: self._update_gray_image())

        # viewer (Gray)
        viewer_gray = ttk.Frame(self.tab_gray); viewer_gray.pack(fill=tk.BOTH, expand=True, padx=6, pady=(15, 0))
        self.gray_fig = Figure(figsize=(6, 6), dpi=FIG_DPI)
        self.ax_gray = self.gray_fig.add_subplot(111)
        self.ax_gray.set_xticks([]); self.ax_gray.set_yticks([])
        self.gray_canvas = FigureCanvasTkAgg(self.gray_fig, master=viewer_gray)
        self.toolbar_gray = NavigationToolbar2Tk(self.gray_canvas, viewer_gray, pack_toolbar=False)
        self.toolbar_gray.update(); self.toolbar_gray.pack(side=tk.BOTTOM, fill=tk.X)
        self.gray_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self.gray_fig.canvas.mpl_connect("button_press_event", self.on_image_click)

        # --- Pseudo RGB tab ---
        self.tab_rgb = ttk.Frame(self.nb)
        self.nb.add(self.tab_rgb, text="Pseudo RGB")

        def make_rgb_slider(parent, label, var):
            r = ttk.Frame(parent); r.pack(fill=tk.X, padx=6, pady=0)
            ttk.Label(r, text=f"{label} wavelength:").pack(side=tk.LEFT)
            sc = tk.Scale(
                r, variable=var, command=self.on_rgb_scale, orient=tk.HORIZONTAL,
                length=460, width=16, sliderlength=18, from_=0.0, to=0.0, resolution=1.0, showvalue=True
            )
            sc.pack(side=tk.LEFT, padx=8)
            lv = tk.StringVar(value=f"{label}: -")
            ttk.Label(r, textvariable=lv).pack(side=tk.LEFT)
            return sc, lv

        self.r_var, self.g_var, self.b_var = tk.DoubleVar(), tk.DoubleVar(), tk.DoubleVar()
        self.r_scale, self.r_label = make_rgb_slider(self.tab_rgb, "R", self.r_var)
        self.g_scale, self.g_label = make_rgb_slider(self.tab_rgb, "G", self.g_var)
        self.b_scale, self.b_label = make_rgb_slider(self.tab_rgb, "B", self.b_var)

        viewer_rgb = ttk.Frame(self.tab_rgb); viewer_rgb.pack(fill=tk.BOTH, expand=True, padx=6, pady=(15, 0))
        self.rgb_fig = Figure(figsize=(6, 6), dpi=FIG_DPI)
        self.ax_rgb = self.rgb_fig.add_subplot(111)
        self.ax_rgb.set_xticks([]); self.ax_rgb.set_yticks([])
        self.rgb_canvas = FigureCanvasTkAgg(self.rgb_fig, master=viewer_rgb)
        self.toolbar_rgb = NavigationToolbar2Tk(self.rgb_canvas, viewer_rgb, pack_toolbar=False)
        self.toolbar_rgb.update(); self.toolbar_rgb.pack(side=tk.BOTTOM, fill=tk.X)
        self.rgb_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self.rgb_fig.canvas.mpl_connect("button_press_event", self.on_image_click)

        self.nb.bind("<<NotebookTabChanged>>", self.on_tab_changed)

    def _build_right_panel(self) -> None:
        # Header
        hdr = ttk.Frame(self.right); hdr.pack(fill=tk.X, padx=6, pady=(6, 0))
        ttk.Label(hdr, text="Spectra", font=("", 11, "bold")).pack(side=tk.LEFT)
        ttk.Button(hdr, text="Reset Spectra", command=self.reset_spectra).pack(side=tk.RIGHT)

        # Tools row
        tools = ttk.Frame(self.right); tools.pack(fill=tk.X, padx=6, pady=(6, 2))
        ttk.Label(tools, text="Mode:").pack(side=tk.LEFT)
        self.mode_cb = ttk.Combobox(
            tools, state="readonly",
            values=["Reflectance", "Absorbance"],
            textvariable=self.mode_var, width=12
        )
        self.mode_cb.pack(side=tk.LEFT, padx=(4, 12))
        self.mode_cb.bind("<<ComboboxSelected>>", lambda e: self.on_mode_change())

        ttk.Separator(tools, orient="vertical").pack(side=tk.LEFT, fill=tk.Y, padx=8)

        self.noise_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(tools, text="Denoise (median)", variable=self.noise_var,
                        command=self.on_noise_toggle).pack(side=tk.LEFT, padx=(2, 10))
        self.smooth_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(tools, text="Smooth (SG)", variable=self.smooth_var,
                        command=self.on_smooth_toggle).pack(side=tk.LEFT, padx=(2, 10))
        self.snv_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(tools, text="SNV", variable=self.snv_var,
                        command=self.on_snv_toggle).pack(side=tk.LEFT, padx=(2, 10))

        ttk.Separator(tools, orient="vertical").pack(side=tk.LEFT, fill=tk.Y, padx=8)

        ttk.Button(tools, text="Save Meta", command=self.on_save_meta_only).pack(side=tk.LEFT, padx=(2, 6))
        ttk.Button(tools, text="Save PNG", command=self.on_save_figure).pack(side=tk.LEFT, padx=(2, 6))
        ttk.Button(tools, text="Export CSV", command=self.on_export_csv_spectra_only).pack(side=tk.LEFT, padx=(0, 0))

        # Plot range
        pr = ttk.Frame(self.right); pr.pack(fill=tk.X, padx=6, pady=(2, 4))
        ttk.Label(pr, text="Plot range:").pack(side=tk.LEFT)
        self.plot_min_var = tk.DoubleVar(value=0.0)
        self.plot_max_var = tk.DoubleVar(value=0.0)
        self.plot_min_scale = tk.Scale(
            pr, variable=self.plot_min_var, command=self.on_plot_range_change,
            orient=tk.HORIZONTAL, length=260, width=12, sliderlength=14,
            from_=0.0, to=0.0, resolution=1.0, showvalue=True
        )
        self.plot_min_scale.pack(side=tk.LEFT, padx=(6, 4))
        self.plot_max_scale = tk.Scale(
            pr, variable=self.plot_max_var, command=self.on_plot_range_change,
            orient=tk.HORIZONTAL, length=260, width=12, sliderlength=14,
            from_=0.0, to=0.0, resolution=1.0, showvalue=True
        )
        self.plot_max_scale.pack(side=tk.LEFT, padx=(4, 6))
        self.plot_rng_label = tk.StringVar(value="(-)")
        ttk.Label(pr, textvariable=self.plot_rng_label).pack(side=tk.LEFT, padx=8)

        # Points/Polygons panel (collapsible)
        bar = ttk.Frame(self.right); bar.pack(fill=tk.X, padx=6, pady=(4, 0))
        self._pts_visible = False
        self._pts_frame = ttk.LabelFrame(self.right, text="Points (current image)")
        self._pts_btn = ttk.Button(bar, text="Show points list", command=self._toggle_points_panel)
        self._pts_btn.pack(side=tk.LEFT)
        ttk.Checkbutton(bar, text="Polygon Avg", variable=self.poly_mode,
                        command=self._on_poly_mode_toggle).pack(side=tk.LEFT, padx=(10, 0))

        # Treeview in pts_frame
        cols = ("id", "label", "x", "y", "source")
        self.tree = ttk.Treeview(self._pts_frame, columns=cols, show="headings", height=4)
        for c, w in zip(cols, (70, 160, 80, 80, 240)):
            self.tree.heading(c, text=c.upper())
            self.tree.column(c, width=w, anchor="w")
        sb = ttk.Scrollbar(self._pts_frame, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscroll=sb.set)
        btns = ttk.Frame(self._pts_frame)
        ttk.Button(btns, text="Rename", command=self._rename_selected).pack(fill=tk.X, pady=(0, 6))
        ttk.Button(btns, text="Delete", command=self._delete_selected).pack(fill=tk.X)
        self.tree.grid(row=0, column=0, sticky="nsew", padx=(6, 0), pady=6)
        sb.grid(row=0, column=1, sticky="ns", padx=(0, 6), pady=6)
        btns.grid(row=0, column=2, sticky="ns", padx=6, pady=6)
        self._pts_frame.columnconfigure(0, weight=1)
        self._pts_frame.rowconfigure(0, weight=1)
        self.tree.bind("<Double-1>", self._on_tree_double_click)

        # Spectra viewer
        viewer_spec = ttk.Frame(self.right); viewer_spec.pack(fill=tk.BOTH, expand=True, padx=6, pady=(6, 0))
        self._viewer_spec = viewer_spec
        self.spec_fig = Figure(figsize=(6, 6), dpi=FIG_DPI)
        self.ax_spec = self.spec_fig.add_subplot(111)
        self._style_spec_axes()
        self.spec_canvas = FigureCanvasTkAgg(self.spec_fig, master=viewer_spec)
        tb = NavigationToolbar2Tk(self.spec_canvas, viewer_spec, pack_toolbar=False)
        tb.update(); tb.pack(side=tk.BOTTOM, fill=tk.X, pady=2)
        self.spec_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

    # --------------------------------------------------------------------- #
    # Hotkeys
    # --------------------------------------------------------------------- #
    def _setup_hotkeys(self) -> None:
        """Global hotkeys (disabled while editing Entry)."""
        def _busy_in_entry() -> bool:
            fg = self.focus_get()
            return isinstance(fg, (tk.Entry, ttk.Entry))

        def _set_mode(name: str) -> None:
            if _busy_in_entry(): return
            if name in ("Reflectance", "Absorbance"):
                self.mode_var.set(name)
                self.on_mode_change()

        def _toggle_bool(var: tk.BooleanVar, callback) -> None:
            if _busy_in_entry(): return
            var.set(not var.get())
            callback()

        def _toggle_poly() -> None:
            if _busy_in_entry(): return
            self.poly_mode.set(not self.poly_mode.get())
            self._on_poly_mode_toggle()

        for key in ("r", "R"):
            self.bind_all(key, lambda e: _set_mode("Reflectance"))
        for key in ("a", "A"):
            self.bind_all(key, lambda e: _set_mode("Absorbance"))
        for key in ("i", "I"):
            self.bind_all(key, lambda e: _toggle_poly())
        for key in ("d", "D"):
            self.bind_all(key, lambda e: self.reset_spectra())

        # Preprocessing toggles: 1=median, 2=SG, 3=SNV
        self.bind_all("1", lambda e: _toggle_bool(self.noise_var, self.on_noise_toggle))
        self.bind_all("2", lambda e: _toggle_bool(self.smooth_var, self.on_smooth_toggle))
        self.bind_all("3", lambda e: _toggle_bool(self.snv_var, self.on_snv_toggle))

    # --------------------------------------------------------------------- #
    # Helpers (paths, sources, debounce)
    # --------------------------------------------------------------------- #
    def _debounce(self, key: str, func, delay_ms: int = 1) -> None:
        """Run func once after a short delay per key."""
        if not hasattr(self, "_debouncers"):
            self._debouncers: Dict[str, Any] = {}
        prev = self._debouncers.get(key)
        if prev:
            try: self.after_cancel(prev)
            except Exception: pass
        self._debouncers[key] = self.after(delay_ms, func)

    def _norm_path(self, p: Any) -> str:
        try:
            return os.path.normcase(os.path.normpath(os.path.abspath(str(p))))
        except Exception:
            return str(p) if p is not None else ""

    def _same_source(self, a: Any, b: Any) -> bool:
        return self._norm_path(a) == self._norm_path(b)

    def _source_exists(self, sp: str) -> bool:
        try:
            sp = str(sp or "")
            return bool(sp and os.path.isfile(sp) and sp.lower().endswith(".hdr"))
        except Exception:
            return False
        
    # 既存に追加：クラス内（どこでもOK）
    def _norm_src(self, sp: str) -> str:
        try:
            return os.path.normcase(os.path.normpath(os.path.abspath(str(sp or ""))))
        except Exception:
            return str(sp or "")

    def _point_key(self, src: str, x: int, y: int) -> tuple:
        return (self._norm_src(src), int(x), int(y))

    def _canon_poly(self, verts) -> tuple:
        """ポリゴン頂点の表現を順序不変にする（回転＆向きの違いを吸収）"""
        V = tuple((int(x), int(y)) for x, y in (verts or []))
        if len(V) < 3:
            return V
        # 回転の違いを最小辞書順になる始点に合わせる
        rotations = [V[i:]+V[:i] for i in range(len(V))]
        # 逆順（反転）も候補に含め、最小を採用
        rev = V[::-1]
        rotations += [rev[i:]+rev[:i] for i in range(len(rev))]
        return min(rotations)

    def _poly_key(self, src: str, verts) -> tuple:
        return (self._norm_src(src), self._canon_poly(verts))

    def _existing_point_maps(self):
        """既存pointsをキー化して重複/ラベル比較に使う"""
        exact = set()      # (src,x,y,label)
        by_xy = dict()     # (src,x,y) -> label（最後の値）
        for p in self.points:
            src = p.get("source","")
            kxy = self._point_key(src, p.get("x",0), p.get("y",0))
            lbl = str(p.get("label",""))
            exact.add((kxy, lbl))
            by_xy[kxy] = lbl
        return exact, by_xy

    def _existing_poly_maps(self):
        exact = set()      # (src,canon_verts,label)
        by_shape = dict()  # (src,canon_verts) -> label
        for pg in self.polygons:
            src = pg.get("source","")
            verts = pg.get("verts") or []
            k = self._poly_key(src, verts)
            lbl = str(pg.get("label",""))
            exact.add((k, lbl))
            by_shape[k] = lbl
        return exact, by_shape

    # --------------------------------------------------------------------- #
    # Data Loading
    # --------------------------------------------------------------------- #
    def open_hdr(self) -> None:
        path = filedialog.askopenfilename(title="Select HDR file", filetypes=[("ENVI header", "*.hdr")])
        if path:
            self._load_hdr_from_path(path)

    def _load_hdr_from_path(self, path: str) -> bool:
        """Load HSI (.hdr) and sync UI. Returns True on success."""
        if not path or not os.path.isfile(path) or not path.lower().endswith(".hdr"):
            return False
        try:
            img = spectral.open_image(path)
            data = np.asarray(img.load())
        except Exception as e:
            messagebox.showerror("Load error", str(e))
            return False

        if data.ndim == 2:
            data = data[:, :, None]

        self.img, self.data = img, data
        self.path_var.set(os.path.abspath(path))

        try:
            wl_meta = img.metadata.get("wavelength", None)
            wl = self.to_float_array(wl_meta) if wl_meta is not None else np.arange(data.shape[2], dtype=float)
        except Exception:
            wl = np.arange(data.shape[2], dtype=float)
        self.wavelengths = wl

        self.gray_band = min(10, data.shape[2] - 1)
        B = data.shape[2]
        self.rgb_bands = {"R": int(B * 0.8), "G": int(B * 0.5), "B": int(B * 0.2)}

        wl_min, wl_max, res = float(wl.min()), float(wl.max()), self._wl_resolution()
        self.gray_scale.configure(from_=wl_min, to=wl_max, resolution=res)
        self.gray_scale_var.set(float(wl[self.gray_band]))

        for sc in (self.r_scale, self.g_scale, self.b_scale):
            sc.configure(from_=wl_min, to=wl_max, resolution=res)
        self.r_var.set(float(wl[self.rgb_bands["R"]]))
        self.g_var.set(float(wl[self.rgb_bands["G"]]))
        self.b_var.set(float(wl[self.rgb_bands["B"]]))
        self._update_rgb_labels()

        for sc in (self.plot_min_scale, self.plot_max_scale):
            sc.configure(from_=wl_min, to=wl_max, resolution=res)
        self.plot_min_var.set(wl_min)
        self.plot_max_var.set(wl_max)
        self._update_plot_range_label()

        self._set_sliders_state(tk.NORMAL)
        self._update_gray_label()

        self.reset_spectra()
        self._pt_raw_cache.clear()
        self._pt_proc_cache.clear()
        self._poly_idx_cache.clear()
        self._poly_proc_cache.clear()
        return True

    @staticmethod
    def to_float_array(x: Any) -> np.ndarray:
        try:
            return np.array(x, dtype=float)
        except Exception:
            return np.array([float(str(v).strip().replace(",", "")) for v in x])

    def _wl_resolution(self) -> float:
        wl = self.wavelengths
        if wl is None or wl.size < 2:
            return 1.0
        diffs = np.diff(wl.astype(float))
        diffs = diffs[np.isfinite(diffs)]
        res = float(np.median(np.abs(diffs))) if diffs.size else 1.0
        return res if np.isfinite(res) and res > 0 else 1.0

    # --------------------------------------------------------------------- #
    # Image Rendering (Gray / RGB)
    # --------------------------------------------------------------------- #
    def _update_gray_label(self) -> None:
        b = int(self.gray_band)
        wl = float(self.wavelengths[b]) if self.wavelengths is not None else float(b)
        self.gray_sel_var.set(f"λ={wl:.1f} nm (Band {b})")

    def _update_rgb_labels(self) -> None:
        def t(k: str) -> str:
            b = self.rgb_bands[k]
            wl = float(self.wavelengths[b]) if self.wavelengths is not None else float(b)
            return f"λ={wl:.1f} nm (Band {b})"
        self.r_label.set(f"R: {t('R')}"); self.g_label.set(f"G: {t('G')}"); self.b_label.set(f"B: {t('B')}")

    def _update_gray_image(self) -> None:
        if self.data is None or self.wavelengths is None:
            return
        b = int(np.clip(self.gray_band, 0, self.data.shape[2] - 1))
        wl = float(self.wavelengths[b])
        ax = self.ax_gray
        ax.cla(); ax.set_title(f"Gray — λ={wl:.1f} nm (Band {b})"); ax.set_xticks([]); ax.set_yticks([])
        ax.imshow(self.data[:, :, b], cmap=self.cmap_name.get(), zorder=0)
        self._draw_markers(ax)
        self._draw_polygons(ax)
        self.gray_canvas.draw()

    def _update_rgb_image(self) -> None:
        if self.data is None or self.wavelengths is None:
            return
        R = self.rgb_bands["R"]; G = self.rgb_bands["G"]; Bn = self.rgb_bands["B"]
        ax = self.ax_rgb
        ax.cla(); ax.set_xticks([]); ax.set_yticks([])
        if None in (R, G, Bn):
            ax.set_title("Pseudo RGB (select R/G/B)")
        else:
            R = int(np.clip(R, 0, self.data.shape[2] - 1))
            G = int(np.clip(G, 0, self.data.shape[2] - 1))
            Bn = int(np.clip(Bn, 0, self.data.shape[2] - 1))
            wlR = float((self.wavelengths[R])); wlG = float((self.wavelengths[G])); wlB = float((self.wavelengths[Bn]))
            rgb = np.dstack([
                self.stretch01(self.data[:, :, R]),
                self.stretch01(self.data[:, :, G]),
                self.stretch01(self.data[:, :, Bn])
            ])
            ax.set_title(
                f"Pseudo RGB — λ: {wlR:.1f}/{wlG:.1f}/{wlB:.1f} nm\n(Bands: {R}/{G}/{Bn})"
            )
            ax.imshow(rgb, zorder=0)
        self._draw_markers(ax)
        self._draw_polygons(ax)
        self.rgb_canvas.draw()

    @staticmethod
    def stretch01(img: np.ndarray, low: int = PERCENTILE_LOW, high: int = PERCENTILE_HIGH) -> np.ndarray:
        v1, v2 = np.nanpercentile(img, [low, high])
        if v2 - v1 == 0:
            return np.zeros_like(img, dtype=float)
        return np.clip((img - v1) / (v2 - v1), 0, 1)

    # --------------------------------------------------------------------- #
    # Tab / Sliders
    # --------------------------------------------------------------------- #
    def _set_sliders_state(self, state: str) -> None:
        self.gray_scale.configure(state=state)
        for sc in (self.r_scale, self.g_scale, self.b_scale):
            sc.configure(state=state)

    def _nearest_band(self, wl_value: float) -> int:
        dif = np.abs(self.wavelengths - wl_value)
        return int(np.argmin(dif))

    def on_gray_scale(self, val: str) -> None:
        if self.data is None or self._snapping:
            return
        self._snapping = True
        try:
            idx = self._nearest_band(float(val))
            self.gray_band = idx
            self.gray_scale_var.set(float(self.wavelengths[idx]))  # snap to real wl
            self._update_gray_label()
            self._update_gray_image()
        finally:
            self._snapping = False

    def on_rgb_scale(self, _=None) -> None:
        if self.data is None or self._snapping:
            return
        self._snapping = True
        try:
            self.rgb_bands["R"] = self._nearest_band(float(self.r_var.get()))
            self.rgb_bands["G"] = self._nearest_band(float(self.g_var.get()))
            self.rgb_bands["B"] = self._nearest_band(float(self.b_var.get()))
            self.r_var.set(float(self.wavelengths[self.rgb_bands["R"]]))
            self.g_var.set(float(self.wavelengths[self.rgb_bands["G"]]))
            self.b_var.set(float(self.wavelengths[self.rgb_bands["B"]]))
            self._update_rgb_labels()
            self._update_rgb_image()
        finally:
            self._snapping = False

    def on_tab_changed(self, event) -> None:
        if self.data is None:
            return
        nb = event.widget
        tab = nb.nametowidget(nb.select())
        if tab is self.tab_gray:
            self._update_gray_image()
        elif tab is self.tab_rgb:
            self._update_rgb_image()

    # --------------------------------------------------------------------- #
    # Drawing (markers & polygons)
    # --------------------------------------------------------------------- #
    def _draw_markers(self, ax) -> None:
        cur_src = self.path_var.get()
        for p in self.points:
            if not self._same_source(p.get("source", ""), cur_src):
                continue
            ax.plot(p["x"], p["y"], marker='+', color=p["color"],
                    markersize=10, markeredgewidth=1.8, zorder=3, clip_on=True)

    def _draw_polygons(self, ax) -> None:
        cur_src = self.path_var.get()
        for pg in self.polygons:
            if not self._same_source(pg.get("source", ""), cur_src):
                continue
            vs = pg.get("verts") or []
            if not vs:
                continue
            xs, ys = zip(*vs)
            if len(vs) >= 2:
                ax.plot(xs + (xs[0],), ys + (ys[0],), lw=1.5, linestyle='-',
                        color=pg["color"], zorder=5, clip_on=True)
            for (vx, vy) in vs:
                ax.plot(vx, vy, marker='o', markersize=5.5, markerfacecolor='none',
                        markeredgewidth=1.4, markeredgecolor=pg["color"], zorder=6, clip_on=True)

        if self.poly_mode.get() and self._poly_temp_verts and (ax is self._poly_drawing_axes):
            xs, ys = zip(*self._poly_temp_verts)
            if len(xs) >= 2:
                ax.plot(xs, ys, lw=1.0, linestyle='--', color='k', zorder=7, clip_on=True)
            for (vx, vy) in self._poly_temp_verts:
                ax.plot(vx, vy, marker='o', markersize=6.0, markerfacecolor='none',
                        markeredgewidth=1.2, markeredgecolor='k', zorder=8, clip_on=True)

    # --------------------------------------------------------------------- #
    # Spectral plot & processing
    # --------------------------------------------------------------------- #
    def on_plot_range_change(self, *_):
        self._update_plot_range_label()
        self._debounce("plot_redraw", self._redraw_spec_lines, delay_ms=100)

    def _style_spec_axes(self) -> None:
        self.ax_spec.set_title("Spectra")
        self.ax_spec.set_xlabel("Wavelength [nm]")
        ylab = "Reflectance" if self.mode_var.get() == "Reflectance" else "Absorbance"
        self.ax_spec.set_ylabel(ylab)
        self.ax_spec.grid(True)
        self.ax_spec.xaxis.set_minor_locator(AutoMinorLocator())
        self.ax_spec.yaxis.set_minor_locator(AutoMinorLocator())
        self.ax_spec.grid(which='minor', linestyle=':', linewidth=0.5, alpha=0.6)

    def _legend_for_point(self, p: Dict[str, Any]) -> str:
        base = p["label"] if p["label"] else f'({p["x"]},{p["y"]})'
        src = p.get("source", "")
        cur = self.path_var.get()
        if src and (not self._same_source(src, cur)):
            base += f" @{os.path.basename(src)}"
        return base

    def _toolbar_busy(self, ax) -> bool:
        tb = None; canvas = None
        if ax is self.ax_gray:
            tb = getattr(self, "toolbar_gray", None); canvas = self.gray_fig.canvas
        elif ax is self.ax_rgb:
            tb = getattr(self, "toolbar_rgb", None); canvas = self.rgb_fig.canvas
        if tb is None: return False
        active = getattr(tb, "_active", None)
        if isinstance(active, str) and active in ("PAN", "ZOOM"): return True
        if hasattr(active, "name") and str(active.name).lower() in ("pan", "zoom"): return True
        mode = getattr(tb, "mode", "")
        if isinstance(mode, str) and mode.lower() in ("pan", "zoom", "pan/zoom"): return True
        wl = getattr(canvas, "widgetlock", None)
        return bool(wl and wl.locked())

    def _proc_flags(self) -> Tuple[str, bool, bool, bool]:
        return (self.mode_var.get(),
                bool(self.noise_var.get()),
                bool(self.smooth_var.get()),
                bool(self.snv_var.get()))

    # --- clicks ---
    def on_image_click(self, event) -> None:
        if self.data is None: return
        if event.inaxes not in (self.ax_gray, self.ax_rgb): return
        if event.xdata is None or event.ydata is None: return
        if self._toolbar_busy(event.inaxes): return

        x, y = int(round(event.xdata)), int(round(event.ydata))
        H, W, _ = self.data.shape
        if not (0 <= x < W and 0 <= y < H): return

        # Polygon input mode
        if self.poly_mode.get():
            if self._poly_drawing_axes is None:
                self._poly_drawing_axes = event.inaxes
                self._poly_temp_verts = []
            if event.inaxes is not self._poly_drawing_axes:
                return
            if getattr(event, "button", None) == 3:
                if self._poly_temp_verts:
                    self._poly_temp_verts.pop()
                    if event.inaxes is self.ax_gray: self._update_gray_image()
                    else: self._update_rgb_image()
                    return
                if self._delete_polygon_near(x, y):
                    if self._pts_visible: self._refresh_points_view()
                    return
                return
            self._poly_temp_verts.append((x, y))
            if getattr(event, "dblclick", False) and len(self._poly_temp_verts) >= 3:
                pg = {"verts": tuple(self._poly_temp_verts),
                      "color": self._next_polygon_color(),
                      "label": "", "source": self.path_var.get()}
                self.polygons.append(pg)
                self._poly_temp_verts = []; self._poly_drawing_axes = None
                self._redraw_spec_lines()
                self._update_gray_image(); self._update_rgb_image()
                self.spec_canvas.draw_idle(); self.spec_canvas.flush_events()
                if self._pts_visible: self._refresh_points_view(select_last=True)
                return
            if event.inaxes is self.ax_gray: self._update_gray_image()
            else: self._update_rgb_image()
            return

        # Point mode
        if getattr(event, "button", None) == 3:
            self._delete_marker_near(x, y)
            return

        color = self._next_point_color()
        p = {"x": x, "y": y, "color": color, "label": "", "source": self.path_var.get()}
        self.points.append(p)

        sl, i_lo, i_hi = self._current_plot_slice_and_bounds()
        wl_plot = self.wavelengths[sl]
        yraw_full = np.asarray(self.data[y, x, :]).squeeze()
        yraw = yraw_full[sl]

        ydisp = self._apply_mode(yraw)
        yplot = self._process_spectrum(ydisp)

        legend_text = self._legend_for_point(p)
        self.ax_spec.plot(wl_plot, yplot, marker='o', lw=1.5, markersize=2.5,
                          color=color, label=legend_text)
        lines = [ln for ln in self.ax_spec.get_lines()
                 if ln.get_label() and not str(ln.get_label()).startswith('_')]
        if lines:
            self.ax_spec.legend(loc='best')
        self.spec_canvas.draw()

        event.inaxes.plot(x, y, marker='+', color=color, markersize=10, markeredgewidth=1.8,
                          zorder=3, clip_on=True)
        if event.inaxes is self.ax_gray: self._update_gray_image()
        else: self._update_rgb_image()
        if self._pts_visible:
            self._refresh_points_view(select_last=True)

    # --- plot range / slice ---
    def _current_plot_slice_and_bounds(self):
        if self.wavelengths is None or self.wavelengths.size == 0:
            return slice(None), None, None
        lo = float(self.plot_min_var.get()); hi = float(self.plot_max_var.get())
        if hi < lo: lo, hi = hi, lo
        i_lo = self._nearest_band(lo)
        i_hi = self._nearest_band(hi)
        if i_hi < i_lo: i_lo, i_hi = i_hi, i_lo
        return slice(i_lo, i_hi + 1), i_lo, i_hi

    def _update_plot_range_label(self) -> None:
        if self.wavelengths is None or self.wavelengths.size == 0:
            self.plot_rng_label.set("(-)"); return
        lo = float(self.plot_min_var.get()); hi = float(self.plot_max_var.get())
        if hi < lo: lo, hi = hi, lo
        self.plot_rng_label.set(f"{lo:.1f} – {hi:.1f}")

    # --- main redraw ---
    def _redraw_spec_lines(self):
        ax = self.ax_spec
        ax.cla(); self._style_spec_axes()
        s, i_lo, i_hi = self._current_plot_slice_and_bounds()
        if i_lo is None:
            self.spec_canvas.draw_idle(); return

        line_count = 0
        # Points
        for p in self.points:
            wl_plot, y_plot = self._get_point_proc_slice(p, i_lo, i_hi)
            if wl_plot is None: continue
            ax.plot(wl_plot, y_plot, marker='o', lw=1.5, markersize=2.5,
                    color=p["color"], label=self._legend_for_point(p))
            line_count += 1

        # Polygons
        for i, pg in enumerate(self.polygons):
            res = self._get_polygon_proc_slice_stats(pg, i_lo, i_hi)
            if not res: continue
            wl_plot, y_mean, y_std, N = res
            base_label = (pg.get("label") or f"pg{i+1:04d}")
            src = str(pg.get("source","")); cur = str(self.path_var.get())
            if src and (src != cur): base_label += f" @{os.path.basename(src)}"
            ax.plot(wl_plot, y_mean, lw=2.0, linestyle='-', color=pg["color"], label=base_label)
            try:
                ax.fill_between(wl_plot, y_mean-y_std, y_mean+y_std, alpha=0.25, linewidth=0, facecolor=pg["color"])
            except Exception:
                pass
            line_count += 1

        if line_count > 0:
            ax.legend(loc='best')
        self.spec_canvas.draw_idle()

    # --- processing helpers / caches ---
    def _get_point_proc_slice(self, p, i_lo, i_hi):
        """対象範囲[i_lo:i_hi]に処理をかけた結果を返す（wl_slice, y_proc_slice）。"""
        src = str(p.get("source",""))
        key_raw = (src, int(p["x"]), int(p["y"]))  # RAWフルは既存キャッシュを使用
        # RAWフル（反射値フル帯域）は既存取得
        y_full = self._pt_raw_cache.get(key_raw)
        if y_full is None:
            if self._same_source(src, self.path_var.get()):
                y_full = np.asarray(self.data[int(p["y"]), int(p["x"]), :]).squeeze().astype(float)
            else:
                d, _ = self._get_hsi_for_source(src)
                if d is None: return None, None
                y_full = d[int(p["y"]), int(p["x"]), :].astype(float)
            self._pt_raw_cache[key_raw] = y_full

        flags = self._proc_flags()
        key_proc = key_raw + (flags, int(i_lo), int(i_hi))
        y_proc = self._pt_proc_cache.get(key_proc)
        if y_proc is None:
            y_slice = y_full[i_lo:i_hi+1].astype(np.float32, copy=False)
            y_disp  = self._apply_mode(y_slice)          # 範囲だけモード変換
            y_proc  = self._process_spectrum(y_disp)     # 範囲だけ前処理
            self._pt_proc_cache[key_proc] = y_proc
        else:
            y_proc = y_proc
        wl_slice = self.wavelengths[i_lo:i_hi+1]
        return wl_slice, y_proc

    def _polygon_key(self, pg: Dict[str, Any]) -> Tuple[str, Tuple[Tuple[int, int], ...]]:
        src = str(pg.get("source",""))
        verts = tuple((int(x), int(y)) for x, y in (pg.get("verts") or []))
        return (src, verts)

    def _get_polygon_idx(self, pg: Dict[str, Any], d: np.ndarray) -> np.ndarray:
        k = self._polygon_key(pg)
        idx = self._poly_idx_cache.get(k)
        if idx is None:
            H, W, _ = d.shape
            yy, xx = np.mgrid[0:H, 0:W]
            pts = np.column_stack([xx.ravel(), yy.ravel()])
            mask = Path([*k[1]]).contains_points(pts).reshape(H, W)
            idx = np.flatnonzero(mask)
            self._poly_idx_cache[k] = idx
        return idx

    def _get_polygon_proc_slice_stats(self, pg, i_lo, i_hi):
        src = str(pg.get("source",""))
        if self._same_source(src, self.path_var.get()):
            d, wl = self.data, self.wavelengths
        else:
            d, wl = self._get_hsi_for_source(src)
        if d is None or wl is None or wl.size == 0:
            return None

        k_base = (src, self._normalize_verts(pg.get("verts") or []))
        flags  = self._proc_flags()
        key    = k_base + (flags, int(i_lo), int(i_hi))
        cached = self._poly_proc_cache.get(key)
        if cached is not None:
            return cached

        idx = self._get_polygon_idx(pg, d)
        if idx.size == 0: return None
        H, W, B = d.shape
        s = slice(i_lo, i_hi+1)
        D = d.reshape(-1, B)[idx][:, s].astype(np.float32, copy=False)  # (N, B_slice)

        # 画素ごとに処理（範囲のみ）
        def _proc(y):
            return self._process_spectrum(self._apply_mode(y))
        try:
            Y = np.apply_along_axis(_proc, 1, D)
        except Exception:
            Y = np.vstack([_proc(row) for row in D])

        mean = np.nanmean(Y, axis=0)
        std  = np.nanstd(Y, axis=0, ddof=0)
        out  = (self.wavelengths[s], mean, std, idx.size)
        self._poly_proc_cache[key] = out
        return out

    # --- pre/post processing pipeline ---
    def on_noise_toggle(self, *_): self._pt_proc_cache.clear(); self._poly_proc_cache.clear(); self._redraw_spec_lines()
    def on_smooth_toggle(self, *_): self._pt_proc_cache.clear(); self._poly_proc_cache.clear(); self._redraw_spec_lines()
    def on_snv_toggle(self, *_): self._pt_proc_cache.clear(); self._poly_proc_cache.clear(); self._redraw_spec_lines()

    def on_mode_change(self) -> None:
        self._pt_proc_cache.clear(); self._poly_proc_cache.clear()
        self._style_spec_axes()
        self._redraw_spec_lines()

    def _apply_mode(self, y: np.ndarray) -> np.ndarray:
        """
        Reflectance / Absorbance 変換。
        - 常に float32 を返す
        - 吸光度は 0–1 反射率 or 0–65535 のいずれにも耐性あり（自動判定）
        """
        y = np.asarray(y, dtype=np.float32)
        mode = self.mode_var.get()
        if mode == "Reflectance":
            return y
        if mode == "Absorbance":
            # スケール自動判定：最大値が 1.5 より大なら 16bit スケールとみなす
            maxv = float(np.nanmax(y)) if y.size else 0.0
            if np.isfinite(maxv) and maxv > 1.5: R = y * (1.0 / 65535.0) 
            else: R = y
            R = np.clip(R, 1e-8, 1.0)
            A = -np.log10(R)
            return A.astype(np.float32, copy=False)
        return y

    def _process_spectrum(self, y: np.ndarray) -> np.ndarray:
        # 無駄コピーせず float32 & C連続に統一
        y2 = np.asarray(y, dtype=np.float32, order="C")
        if getattr(self, "noise_var", None) and self.noise_var.get():
            y2 = self._apply_denoise(y2)
        if getattr(self, "smooth_var", None) and self.smooth_var.get():
            y2 = self._apply_smoothing(y2)
        if getattr(self, "snv_var", None) and self.snv_var.get():
            y2 = self._apply_snv(y2)
        return np.asarray(y2, dtype=np.float32, order="C", copy=False)

    def _apply_denoise(self, y: np.ndarray) -> np.ndarray:
        n = len(y)
        k = self._safe_window_length(n, base=MED_BASE_WIN, min_win=MED_MIN_WIN)
        if k is None: return y
        try:
            return medfilt(y, kernel_size=k)
        except Exception:
            return y

    def _apply_smoothing(self, y: np.ndarray) -> np.ndarray:
        try:
            n = len(y); poly = SG_POLYORDER
            win = self._safe_window_length(n, base=SG_BASE_WIN, min_win=SG_MIN_WIN)
            if win is None: return y
            if win <= poly:
                win = poly + 3
                if win % 2 == 0: win += 1
            return savgol_filter(y, window_length=win, polyorder=poly, mode="interp")
        except Exception:
            n = len(y)
            k = self._safe_window_length(n, base=7, min_win=3)
            if k is None: return y
            return np.convolve(y, np.ones(k) / k, mode="same")

    def _apply_snv(self, y: np.ndarray) -> np.ndarray:
        m = np.nanmean(y); s = np.nanstd(y)
        if not np.isfinite(s) or s == 0:
            return y - m
        return (y - m) / s

    @staticmethod
    def _safe_window_length(n: int, base: int = 5, min_win: int = 3) -> Optional[int]:
        if n < min_win: return None
        k = base if n >= base else (n | 1)
        k = max(min_win, k)
        return k if k <= n else None

    # --------------------------------------------------------------------- #
    # Delete / Reset / Color
    # --------------------------------------------------------------------- #
    def _next_point_color(self):
        c = self._palette10[self._pt_color_idx % 10]
        self._pt_color_idx = (self._pt_color_idx + 1) % 10
        return c

    def _next_polygon_color(self):
        c = self._palette10[self._pg_color_idx % 10]
        self._pg_color_idx = (self._pg_color_idx + 1) % 10
        return c

    def on_delete_last_marker(self, *_):
        if not self.points: return
        p = self.points.pop()
        self._invalidate_point_cache(p.get("source", self.path_var.get()), int(p["x"]), int(p["y"]))
        self._redraw_spec_lines(); self._update_gray_image(); self._update_rgb_image()
        if self._pts_visible: self._refresh_points_view()

    def reset_spectra(self) -> None:
        self._pt_raw_cache.clear(); self._pt_proc_cache.clear()
        self._poly_idx_cache.clear(); self._poly_proc_cache.clear()
        self.ax_spec.cla(); self._style_spec_axes(); self.spec_canvas.draw()
        self.points.clear(); self.polygons.clear()
        self._poly_temp_verts = []; self._poly_drawing_axes = None
        self._pt_color_idx = 0
        self._pg_color_idx = 0
        self._update_gray_image(); self._update_rgb_image()
        if self._pts_visible: self._refresh_points_view()

    def _invalidate_point_cache(self, src: str, x: int, y: int) -> None:
        key_raw = (str(src), int(x), int(y))
        self._pt_raw_cache.pop(key_raw, None)
        to_del = [k for k in self._pt_proc_cache.keys()
                  if isinstance(k, tuple) and len(k) >= 3 and k[0:3] == key_raw]
        for k in to_del:
            self._pt_proc_cache.pop(k, None)

    def _normalize_verts(self, verts: Sequence[Tuple[int, int]]) -> Tuple[Tuple[int, int], ...]:
        return tuple((int(x), int(y)) for (x, y) in verts or [])

    def _invalidate_polygon_cache(self, src: str, verts: Sequence[Tuple[int, int]]) -> None:
        key_base = (str(src), self._normalize_verts(verts))
        self._poly_idx_cache.pop(key_base, None)
        to_del = [k for k in self._poly_proc_cache.keys()
                  if isinstance(k, tuple) and len(k) >= 3 and k[0:2] == key_base]
        for k in to_del:
            self._poly_proc_cache.pop(k, None)

    def _delete_marker_near(self, x: int, y: int, radius: Optional[int] = None) -> bool:
        radius = radius or DELETE_RADIUS_PX
        if not self.points: return False
        pts = np.array([(p["x"], p["y"]) for p in self.points])
        d = np.sqrt((pts[:, 0] - x) ** 2 + (pts[:, 1] - y) ** 2)
        i = int(np.argmin(d))
        if d[i] <= radius:
            p = self.points.pop(i)
            self._redraw_spec_lines()
            self._invalidate_point_cache(p.get("source", self.path_var.get()), int(p["x"]), int(p["y"]))
            self._update_gray_image(); self._update_rgb_image()
            if self._pts_visible: self._refresh_points_view()
            return True
        return False

    def _delete_polygon_near(self, x: int, y: int, radius: Optional[int] = None) -> bool:
        if not self.polygons: return False
        rad = radius if radius is not None else DELETE_RADIUS_PX
        rad2 = (rad * 1.5)

        def _pt_seg_dist(px, py, x1, y1, x2, y2):
            vx, vy = x2 - x1, y2 - y1
            wx, wy = px - x1, py - y1
            denom = vx*vx + vy*vy
            if denom <= 1e-12:
                dx, dy = px - x1, py - y1
                return (dx*dx + dy*dy) ** 0.5
            t = max(0.0, min(1.0, (wx*vx + wy*vy) / denom))
            nx, ny = x1 + t*vx, y1 + t*vy
            dx, dy = px - nx, py - ny
            return (dx*dx + dy*dy) ** 0.5

        for i, pg in enumerate(self.polygons):
            vs = pg.get("verts") or []
            if len(vs) < 3: continue
            if Path(vs).contains_point((x, y)):
                pg = self.polygons.pop(i)
                self._invalidate_polygon_cache(pg.get("source", self.path_var.get()), pg.get("verts", []))
                self._redraw_spec_lines(); self._update_gray_image(); self._update_rgb_image()
                return True

        for i, pg in enumerate(self.polygons):
            vs = pg.get("verts") or []
            if len(vs) < 3: continue
            for (vx, vy) in vs:
                if (vx - x)**2 + (vy - y)**2 <= rad*rad:
                    pg = self.polygons.pop(i)
                    self._invalidate_polygon_cache(pg.get("source", self.path_var.get()), pg.get("verts", []))
                    self._redraw_spec_lines(); self._update_gray_image(); self._update_rgb_image()
                    return True
            for (x1, y1), (x2, y2) in zip(vs, vs[1:] + vs[:1]):
                if _pt_seg_dist(x, y, x1, y1, x2, y2) <= rad2:
                    pg = self.polygons.pop(i)
                    self._invalidate_polygon_cache(pg.get("source", self.path_var.get()), pg.get("verts", []))
                    self._redraw_spec_lines(); self._update_gray_image(); self._update_rgb_image()
                    return True
        return False

    # --------------------------------------------------------------------- #
    # Points list (Treeview)
    # --------------------------------------------------------------------- #
    def _toggle_points_panel(self) -> None:
        if self._pts_visible:
            self._pts_frame.pack_forget()
            self._pts_visible = False
            self._pts_btn.config(text="Show points list")
        else:
            self._pts_frame.pack(before=self._viewer_spec, fill=tk.X, expand=False, padx=6, pady=(4, 4))
            self._pts_visible = True
            self._pts_btn.config(text="Hide points list")
            self._refresh_points_view()

    def _refresh_points_view(self, *, select_last: bool = False) -> None:
        for item in self.tree.get_children():
            self.tree.delete(item)
        for i, p in enumerate(self.points):
            pid = f"sp{i+1:04d}"
            src = str(p.get("source", "")) if p.get("source", "") is not None else ""
            base = os.path.basename(src) if src else "-"
            if src and not self._source_exists(src):
                base = f"{base} [MISSING]"
            self.tree.insert("", "end", iid=pid,
                             values=(pid, p["label"], p["x"], p["y"], base))
        for j, pg in enumerate(self.polygons):
            iid = f"pg{j+1:04d}"
            vs = pg.get("verts") or []
            if len(vs) >= 1:
                cx = int(round(sum(v[0] for v in vs) / len(vs)))
                cy = int(round(sum(v[1] for v in vs) / len(vs)))
            else:
                cx, cy = "", ""
            src = str(pg.get("source","")) if pg.get("source","") is not None else ""
            base = os.path.basename(src) if src else "-"
            if src and not self._source_exists(src):
                base = f"{base} [MISSING]"
            self.tree.insert("", "end", iid=iid, values=(iid, pg.get("label",""), cx, cy, base))

        if select_last:
            if self.points:
                pid = f"sp{len(self.points):04d}"
            elif self.polygons:
                pid = f"pg{len(self.polygons):04d}"
            else:
                pid = None
            if pid:
                self.tree.selection_set(pid)
                self.tree.see(pid)

    def _get_selected_index(self) -> Optional[Tuple[str, int]]:
        sel = self.tree.selection()
        if not sel: return None
        iid = sel[0]
        if iid.startswith("sp"):
            try:
                idx = int(iid[2:]) - 1
                return ("point", idx) if 0 <= idx < len(self.points) else None
            except Exception:
                return None
        if iid.startswith("pg"):
            try:
                idx = int(iid[2:]) - 1
                return ("poly", idx) if 0 <= idx < len(self.polygons) else None
            except Exception:
                return None
        return None

    def _delete_selected(self) -> None:
        sel = self._get_selected_index()
        if sel is None: return
        kind, idx = sel
        if kind == "point":
            p = self.points.pop(idx)
            self._invalidate_point_cache(p.get("source", self.path_var.get()), int(p["x"]), int(p["y"]))
        elif kind == "poly":
            pg = self.polygons.pop(idx)
            self._invalidate_polygon_cache(pg.get("source", self.path_var.get()), pg.get("verts", []))
        self._redraw_spec_lines(); self._update_gray_image(); self._update_rgb_image(); self._refresh_points_view()

    def _rename_selected(self) -> None:
        sel = self._get_selected_index()
        if sel is None: return
        kind, idx = sel
        iid = (f"sp{idx+1:04d}" if kind == "point" else f"pg{idx+1:04d}")
        try:
            bbox = self.tree.bbox(iid, column="#2")
        except Exception:
            bbox = None
        if not bbox: return
        x, y, w, h = bbox
        absx = self.tree.winfo_rootx() + x
        absy = self.tree.winfo_rooty() + y

        top = tk.Toplevel(self)
        top.overrideredirect(True)
        top.geometry(f"{w}x{h}+{absx}+{absy}")
        e = ttk.Entry(top)
        e.insert(0, self.points[idx]["label"] if kind == "point" else self.polygons[idx].get("label",""))
        e.pack(fill=tk.BOTH, expand=True); e.focus_set()

        def _commit(evt=None):
            new_label = e.get().strip()
            if kind == "point": self.points[idx]["label"] = new_label
            else: self.polygons[idx]["label"] = new_label
            top.destroy(); self._refresh_points_view(); self._redraw_spec_lines()

        def _cancel(evt=None):
            top.destroy()

        e.bind("<Return>", _commit); e.bind("<Escape>", _cancel); e.bind("<FocusOut>", _commit)

    def _on_tree_double_click(self, event) -> None:
        item = self.tree.identify_row(event.y)
        if not item: return
        self.tree.selection_set(item)
        self._rename_selected()

    # --------------------------------------------------------------------- #
    # Polygon Mode toggles
    # --------------------------------------------------------------------- #
    def _on_poly_mode_toggle(self) -> None:
        if not self.poly_mode.get():
            self._poly_temp_verts = []; self._poly_drawing_axes = None
        self._update_gray_image(); self._update_rgb_image()

    def _clear_polygons(self) -> None:
        self.polygons.clear(); self._poly_temp_verts = []; self._poly_drawing_axes = None
        self._redraw_spec_lines(); self._update_gray_image(); self._update_rgb_image()

    # --------------------------------------------------------------------- #
    # CSV / Meta / Figure Save
    # --------------------------------------------------------------------- #
    @staticmethod
    def _safe_float(v: Any) -> float:
        try: return float(v)
        except Exception: return float("nan")

    def on_export_csv_spectra_only(self) -> None:
        if (self.data is None and not self.points and not self.polygons) or not (self.points or self.polygons):
            messagebox.showinfo("Export CSV", "No spectra to export."); return

        path = filedialog.asksaveasfilename(
            title="Save spectra CSV",
            defaultextension=".csv",
            filetypes=[("CSV", "*.csv")],
            initialfile="spectra_simple.csv"
        )
        if not path: return
        if not path.lower().endswith(".csv"): path += ".csv"
        if self.wavelengths is None or self.wavelengths.size == 0:
            messagebox.showerror("Export CSV", "Wavelengths are not available."); return

        wl = np.asarray(self.wavelengths).ravel()
        cols: List[np.ndarray] = []; ids: List[str] = []
        label_items: List[str] = []; src_items: List[str] = []

        # points
        for i, p in enumerate(self.points):
            cols.append(self._get_raw_spectrum_on_master(p, wl))
            ids.append(f"sp{i+1:04d}")
            lbl = p.get("label") or f"({p.get('x')},{p.get('y')})"
            label_items.append(lbl)
            src_full = str(p.get("source","")) if p.get("source","") is not None else ""
            src_base = os.path.basename(src_full) if src_full else ""
            src_items.append(f"{src_base}@x={p.get('x','')};y={p.get('y','')}")

        # polygons
        for j, pg in enumerate(self.polygons):
            w_src, m_src, s_src, N = self._compute_polygon_raw_stats(pg)
            if w_src is None: continue
            m_out = np.interp(wl, w_src, m_src, left=np.nan, right=np.nan)
            s_out = np.interp(wl, w_src, s_src, left=np.nan, right=np.nan)
            cols.append(m_out); ids.append(f"pg{j+1:04d}_mean")
            cols.append(s_out); ids.append(f"pg{j+1:04d}_std")
            pg_label = (pg.get("label") or f"pg{j+1:04d}")
            label_items.append(f"{pg_label} (mean)"); label_items.append(f"{pg_label} (std)")
            src_full = str(pg.get("source","")) if pg.get("source","") is not None else ""
            src_base = os.path.basename(src_full) if src_full else ""
            src_items.append(src_base); src_items.append(src_base)

        M = np.column_stack(cols) if cols else np.empty((wl.shape[0], 0))
        self._write_csv_new(path, wl, ids, M, note_recomputed=True,
                            labels_list=label_items, sources_list=src_items)
        messagebox.showinfo("Export CSV", f"Saved (spectra only): {os.path.basename(path)}")

    def _get_raw_spectrum_on_master(self, p: Dict[str, Any], wl_master: np.ndarray) -> np.ndarray:
        wl_master = np.asarray(wl_master).reshape(-1)
        B = wl_master.shape[0]
        if self.data is None or self.wavelengths is None or B == 0:
            return np.full((B,), np.nan, dtype=float)

        cur_src = str(self.path_var.get())
        src = str(p.get("source", "")) if p.get("source", "") is not None else ""

        if src == cur_src:
            H, W, _ = self.data.shape
            x0 = int(np.clip(p["x"], 0, W-1)); y0 = int(np.clip(p["y"], 0, H-1))
            return np.asarray(self.data[y0, x0, :]).astype(float).reshape(-1)

        d, wl_src = self._get_hsi_for_source(src)
        if d is None or wl_src is None or wl_src.size == 0:
            return np.full((B,), np.nan, dtype=float)

        Hs, Ws, _ = d.shape
        x0 = int(np.clip(p["x"], 0, Ws-1)); y0 = int(np.clip(p["y"], 0, Hs-1))
        y_src = np.asarray(d[y0, x0, :]).astype(float).reshape(-1)

        wl_src = np.asarray(wl_src, dtype=float).reshape(-1)
        order = np.argsort(wl_src)
        wl_sorted = wl_src[order]; y_sorted = y_src[order]
        uniq_wl, idx_start = np.unique(wl_sorted, return_index=True)
        y_uniq = y_sorted[idx_start]
        y_out = np.interp(wl_master, uniq_wl, y_uniq, left=np.nan, right=np.nan)
        return y_out

    def on_save_meta_only(self) -> None:
        default_name = "spectra_meta.json"
        path = filedialog.asksaveasfilename(
            title="Save Meta JSON",
            defaultextension=".json",
            filetypes=[("JSON", "*.json")],
            initialfile=default_name
        )
        if not path: return

        meta: Dict[str, Any] = {
            "version": "1.0",
            "processing": {
                "mode": self.mode_var.get(),
                "denoise_median": bool(self.noise_var.get()),
                "smooth_savgol":  bool(self.smooth_var.get()),
                "snv":            bool(self.snv_var.get()),
            },
            "plot_range": {},
            "spectra": [],
            "polygons": []
        }

        try:
            lo = float(self.plot_min_var.get()); hi = float(self.plot_max_var.get())
            if hi < lo: lo, hi = hi, lo
            meta["plot_range"] = {"wl_min": lo, "wl_max": hi}
        except Exception:
            pass

        for i, p in enumerate(self.points):
            src_full = str(p.get("source", "")) if p.get("source", "") is not None else ""
            meta["spectra"].append({
                "id": f"sp{i+1:04d}",
                "label": str(p.get("label", "")),
                "source": {
                    "path_full": src_full,
                    "path_basename": os.path.basename(src_full) if src_full else "",
                    "coords": {"x": int(p["x"]), "y": int(p["y"])}
                }
            })

        for j, pg in enumerate(self.polygons):
            src_full = str(pg.get("source","")) if pg.get("source","") is not None else ""
            vs = [[int(x), int(y)] for (x, y) in (pg.get("verts") or [])]
            try:
                _, _, _, N = self._compute_polygon_raw_stats(pg)
            except Exception:
                N = 0
            meta["polygons"].append({
                "id": f"pg{j+1:04d}",
                "label": str(pg.get("label","")),
                "source": {
                    "path_full": src_full,
                    "path_basename": os.path.basename(src_full) if src_full else "",
                },
                "vertices": vs,
                "num_pixels": int(N)
            })

        try:
            with open(path, "w", encoding="utf-8") as jf:
                json.dump(meta, jf, ensure_ascii=False, indent=2)
            messagebox.showinfo("Save Meta JSON", f"Saved: {os.path.basename(path)}")
        except Exception as e:
            messagebox.showerror("Save Meta JSON", f"Failed:\n{e}")

    def _write_csv_new(self, path: str, wl: np.ndarray, ids: List[str], M: np.ndarray,
                       note_recomputed: bool = False,
                       labels_list: Optional[List[str]] = None,
                       sources_list: Optional[List[str]] = None) -> None:
        with open(path, "w", newline="", encoding="utf-8") as f:
            if note_recomputed:
                f.write("# note: values are RAW REFLECTANCE (no absorbance transform, no denoise/smoothing/SNV).\n")
                f.write("# note: polygon columns are mean and std over pixels INSIDE each polygon (raw reflectance).\n")
                f.write("# note: wavelength_nm is the master axis; other HSI spectra are interpolated onto it.\n")
            if labels_list is not None:
                f.write(f"# labels:, {', '.join(map(str, labels_list))}\n")
            if sources_list is not None:
                f.write(f"# sources:, {', '.join(map(str, sources_list))}\n")
            w = csv.writer(f)
            w.writerow(["wavelength_nm", *ids])
            for i in range(len(wl)):
                w.writerow([float(wl[i]), *[self._safe_float(M[i, j]) for j in range(M.shape[1])]])

    def on_save_figure(self) -> None:
        if self.data is None:
            messagebox.showinfo("Save PNG", "No image loaded."); return
        base = filedialog.asksaveasfilename(
            title="Save PNG base name",
            defaultextension=".png",
            filetypes=[("PNG", "*.png")],
            initialfile="figure.png"
        )
        if not base: return
        try:
            active = self.nb.index(self.nb.select())
            if active == 0:
                img_path = base
                self.gray_fig.savefig(img_path, dpi=SAVE_DPI, bbox_inches="tight")
            else:
                img_path = base
                self.rgb_fig.savefig(img_path, dpi=SAVE_DPI, bbox_inches="tight")
            spec_path = os.path.splitext(base)[0] + "_spectra.png"
            self.spec_fig.savefig(spec_path, dpi=SAVE_DPI, bbox_inches="tight")
            messagebox.showinfo("Save PNG", f"Saved:\n- {os.path.basename(img_path)}\n- {os.path.basename(spec_path)}")
        except Exception as e:
            messagebox.showerror("Save PNG error", str(e))

    # --------------------------------------------------------------------- #
    # Meta JSON load (unchanged behavior; slightly tidied)
    # --------------------------------------------------------------------- #
    def load_meta_json(self) -> None:
        skipped_points = 0
        skipped_polygons = 0
        missing_sources = set()
        path = filedialog.askopenfilename(title="Load meta JSON", filetypes=[("JSON", "*.json")])
        if not path: return
        try:
            with open(path, "r", encoding="utf-8") as f:
                meta = json.load(f)
        except Exception as e:
            messagebox.showerror("Load meta JSON", f"Failed to read JSON: {e}")
            return

        json_dir = os.path.dirname(os.path.abspath(path))
        specs = meta.get("spectra", meta if isinstance(meta, list) else None)
        if specs is None:
            messagebox.showerror("Load meta JSON", "JSON does not contain usable 'spectra'.")
            return

        items = specs.items() if isinstance(specs, dict) else [(str(i), v) for i, v in enumerate(specs)]
        pending_points: List[Dict[str, Any]] = []
        pending_polygons: List[Dict[str, Any]] = []
        hdr_candidates: List[str] = []
        # 既存（画面内）と重複判定用のマップ
        pt_exact, pt_by_xy   = self._existing_point_maps()
        pg_exact, pg_by_shape = self._existing_poly_maps()
        # 今回読み込む JSON の中での「自分自身の重複」も避けるためのバッファ
        seen_pts_in_meta   = set()  # ((src,x,y), label) と (src,x,y)
        seen_polys_in_meta = set()  # ((src,canon_verts), label) と (src,canon_verts)

        def _coerce_xy(v): 
            try: return int(v)
            except Exception: return None

        for sid, info in items:
            if not isinstance(info, dict): continue

            src_path = info.get("source_path")
            if src_path is None:
                src = info.get("source", {})
                if isinstance(src, dict):
                    src_path = src.get("path_full") or src.get("path") or src.get("path_basename")
                    coords = src.get("coords", {})
                    x = info.get("x", _coerce_xy(coords.get("x")))
                    y = info.get("y", _coerce_xy(coords.get("y")))
                else:
                    x = info.get("x"); y = info.get("y")
            else:
                x = info.get("x"); y = info.get("y")

            x = _coerce_xy(x); y = _coerce_xy(y)
            if x is None or y is None: continue

            if src_path:
                sp = str(src_path)
                if not os.path.isabs(sp):
                    cand = os.path.join(json_dir, sp)
                    if os.path.isfile(cand): sp = cand
                if not os.path.isfile(sp) and sp.lower().endswith(".hdr"):
                    cand = os.path.join(json_dir, os.path.basename(sp))
                    if os.path.isfile(cand): sp = cand
                src_path = sp

            label = info.get("label") or info.get("name") or info.get("id") or sid
            src_path = str(src_path) if src_path is not None else ""

            if src_path and src_path.lower().endswith(".hdr") and os.path.isfile(src_path):
                hdr_candidates.append(src_path)

            # 点の重複判定
            label = str(label)
            kxy = self._point_key(src_path, x, y)
            k_exact = (kxy, label)
            # (A) 完全一致（パス・座標・ラベルが一致）はスキップ
            if (k_exact in pt_exact) or (k_exact in seen_pts_in_meta):
                skipped_points += 1
                pass
            else:
                # (B) パス＋座標が一致・ラベルだけ不一致
                if (kxy in pt_by_xy) or (kxy in {k for (k, _) in pt_exact}):
                    current_lbl = pt_by_xy.get(kxy, "")
                    # デフォルト方針：既存優先。既存が空で meta が非空なら補完
                    if (not current_lbl) and label:
                        for p in self.points:
                            if self._point_key(p.get("source",""), p.get("x",0), p.get("y",0)) == kxy:
                                p["label"] = label
                                break
                    skipped_points += 1
                    pass
                else:
                    # (C) 本当に新規 → 追加
                    pending_points.append({
                        "x": x, "y": y, "color": None,
                        "label": label, "source": src_path
                    })
                    seen_pts_in_meta.add(k_exact)
                    seen_pts_in_meta.add(kxy)
            # ---------------------------------------------
            if src_path and src_path.lower().endswith(".hdr") and (not os.path.isfile(src_path)):
                missing_sources.add(os.path.basename(str(src_path)))

        # processing / plot_range
        proc = meta.get("processing", {})
        mode = proc.get("mode")
        if mode in ("Reflectance", "Absorbance"): self.mode_var.set(mode)
        if "denoise_median" in proc: self.noise_var.set(bool(proc["denoise_median"]))
        if "smooth_savgol" in proc:  self.smooth_var.set(bool(proc["smooth_savgol"]))
        if "snv" in proc:            self.snv_var.set(bool(proc["snv"]))

        polys_meta = meta.get("polygons", [])
        polys_iter = polys_meta.values() if isinstance(polys_meta, dict) else polys_meta

        def _resolve_src_path(spath: str) -> str:
            if not spath: return ""
            sp = str(spath)
            if not os.path.isabs(sp):
                cand = os.path.join(json_dir, sp)
                if os.path.isfile(cand): sp = cand
            if not os.path.isfile(sp) and sp.lower().endswith(".hdr"):
                base = os.path.basename(sp)
                cand1 = os.path.join(json_dir, base)
                if os.path.isfile(cand1): return cand1
                parent = os.path.dirname(json_dir)
                cand2 = os.path.join(parent, base)
                if os.path.isfile(cand2): return cand2
            return sp

        loaded_polys = 0
        for item in polys_iter:
            if not isinstance(item, dict): continue
            verts = item.get("vertices") or item.get("verts") or []
            if not verts or len(verts) < 3: continue
            try:
                vs = tuple((int(v[0]), int(v[1])) for v in verts)
            except Exception:
                continue

            src_path = item.get("source_path")
            if src_path is None:
                sdict = item.get("source", {})
                if isinstance(sdict, dict):
                    src_path = sdict.get("path_full") or sdict.get("path") or sdict.get("path_basename")
            src_path = _resolve_src_path(src_path) if src_path else ""
            if src_path and src_path.lower().endswith(".hdr") and os.path.isfile(src_path):
                hdr_candidates.append(src_path)

            label = item.get("label") or item.get("id") or ""
            # ポリゴンの重複判定
            canon = self._canon_poly(vs)
            kshape = (self._norm_src(src_path or self.path_var.get()), canon)
            k_exact = (kshape, str(label))
            # (A) 完全一致（パス・形状・ラベル一致）はスキップ
            if (k_exact in pg_exact) or (k_exact in seen_polys_in_meta):
                skipped_polygons += 1
                pass
            else:
                # (B) パス＋形状が一致・ラベルだけ不一致
                if (kshape in pg_by_shape) or (kshape in {k for (k, _) in pg_exact}):
                    current_lbl = pg_by_shape.get(kshape, "")
                    # 既存優先。既存が空で meta が非空なら補完
                    if (not current_lbl) and label:
                        for pg in self.polygons:
                            if self._poly_key(pg.get("source",""), pg.get("verts") or []) == kshape:
                                pg["label"] = str(label)
                                break
                    skipped_polygons += 1
                    pass
                else:
                    # (C) 本当に新規 → 追加
                    pending_polygons.append({
                        "verts": vs, "color": None,
                        "label": str(label), "source": src_path or self.path_var.get()
                    })
                    seen_polys_in_meta.add(k_exact)
                    seen_polys_in_meta.add(kshape)
            # ---------------------------------------
            loaded_polys += 1
            if src_path and src_path.lower().endswith(".hdr") and (not os.path.isfile(src_path)):
                missing_sources.add(os.path.basename(str(src_path)))

        if self.data is None and hdr_candidates:
            for cand in hdr_candidates:
                if self._load_hdr_from_path(os.path.abspath(cand)):
                    try: self._sync_plot_range_to(self.wavelengths)
                    except Exception: pass
                    break

        if pending_points: self.points.extend(pending_points)
        if pending_polygons: self.polygons.extend(pending_polygons)
        # 既存＋読み込んだ順で安定再配色（位相ずれ防止）
        for i, p in enumerate(self.points):   p["color"]  = self._palette10[i % 10]
        for j, pg in enumerate(self.polygons): pg["color"] = self._palette10[j % 10]
        # 次回追加の起点を現在数に合わせる
        self._pt_color_idx = len(self.points)   % 10
        self._pg_color_idx = len(self.polygons) % 10

        pr = meta.get("plot_range", {})
        if ("wl_min" in pr) and ("wl_max" in pr) and (self.wavelengths is not None) and (self.wavelengths.size > 0):
            lo = float(pr["wl_min"]); hi = float(pr["wl_max"])
            wmin, wmax = float(self.wavelengths.min()), float(self.wavelengths.max())
            lo = max(wmin, min(wmax, min(lo, hi)))
            hi = max(wmin, min(wmax, max(lo, hi)))
            self.plot_min_var.set(lo); self.plot_max_var.set(hi)
            self._update_plot_range_label()

        self._redraw_spec_lines()
        if self.data is not None:
            self._update_gray_image(); self._update_rgb_image()
        if self._pts_visible: self._refresh_points_view()

        # ---- Build compact message ----
        lines = []
        # Title line
        if missing_sources:
            title = "Meta data loaded. (Missing source file(s))"
        elif skipped_points or skipped_polygons:
            title = "Meta data loaded. (Some entries skipped)"
        else:
            title = "Meta data loaded."
        lines.append(title)
        lines.append("")  # blank line
        # Counts
        line_points   = f"Points:   {len(pending_points)}"
        line_polygons = f"Polygons: {loaded_polys}"
        if skipped_points:
            line_points   += f"  (skipped {skipped_points})"
        if skipped_polygons:
            line_polygons += f" (skipped {skipped_polygons})"
        lines.append(line_points)
        lines.append(line_polygons)
        # Missing HDR info
        if missing_sources:
            lines.append("")
            lines.append("Missing HDR:")

            listed = sorted(missing_sources)
            show = listed[:5]  # show only first 5
            for f in show:
                lines.append(f" - {f}")

            if len(listed) > 5:
                lines.append(f"... (+{len(listed)-5})")

        msg = "\n".join(lines)
        # ---- Show dialog ----
        if missing_sources:
            messagebox.showwarning("Load meta JSON", msg)
        else:
            messagebox.showinfo("Load meta JSON", msg)


    def _sync_plot_range_to(self, wl: np.ndarray) -> None:
        wl = np.asarray(wl).ravel()
        if wl.size:
            self.plot_min_var.set(float(np.nanmin(wl)))
            self.plot_max_var.set(float(np.nanmax(wl)))
            self._update_plot_range_label()

    def _get_hsi_for_source(self, src_path: str) -> Tuple[Optional[np.ndarray], Optional[np.ndarray]]:
        if not src_path: return None, None
        src_path = self._norm_path(src_path)
        if src_path in self._hsi_cache:
            return self._hsi_cache[src_path]
        if not os.path.isfile(src_path) or (not src_path.lower().endswith(".hdr")):
            self._hsi_cache[src_path] = (None, None); return None, None
        try:
            img = spectral.open_image(src_path)
            data = np.asarray(img.load())
            if data.ndim == 2: data = data[:, :, None]
            wl_meta = img.metadata.get("wavelength", None)
            wl = self.to_float_array(wl_meta) if wl_meta is not None else np.arange(data.shape[2], dtype=float)
            self._hsi_cache[src_path] = (data, wl)
            return data, wl
        except Exception:
            self._hsi_cache[src_path] = (None, None)
            return None, None

    def _compute_polygon_raw_stats(self, pg: Dict[str, Any]) -> Tuple[Optional[np.ndarray], Optional[np.ndarray], Optional[np.ndarray], int]:
        src = str(pg.get("source",""))
        if src == str(self.path_var.get()):
            if self.data is None or self.wavelengths is None:
                return None, None, None, 0
            d, wl = self.data, self.wavelengths
        else:
            d, wl = self._get_hsi_for_source(src)
            if d is None or wl is None or wl.size == 0:
                return None, None, None, 0
        H, W, B = d.shape
        vs = pg.get("verts") or []
        if len(vs) < 3: return None, None, None, 0
        yy, xx = np.mgrid[0:H, 0:W]
        pts = np.column_stack([xx.ravel(), yy.ravel()])
        mask = Path(vs).contains_points(pts).reshape(H, W)
        idx = np.flatnonzero(mask)
        if idx.size == 0: return None, None, None, 0
        D = d.reshape(-1, B)[idx].astype(float, copy=False)
        m = np.nanmean(D, axis=0)
        s = np.nanstd(D, axis=0, ddof=0)
        return np.asarray(wl).astype(float), m, s, idx.size


# === Entry Point =========================================================
if __name__ == "__main__":
    HyperspecTk().mainloop()
