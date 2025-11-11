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

# "Tools should be kind to humans."
#   — iken008, 2025

# =============================================================================
# SETUP & IMPORTS
# =============================================================================
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
import base64
import tempfile


# =============================================================================
# JAPANESE FONT CONFIGURATION
# =============================================================================
from matplotlib import font_manager as _fm, rcParams as _rc
_JP_CANDIDATES = ["Yu Gothic UI", "Yu Gothic", "Meiryo", "MS Gothic", "Noto Sans CJK JP"]
_available = {f.name for f in _fm.fontManager.ttflist}
for fam in _JP_CANDIDATES:
    if fam in _available:
        cur = _rc.get("font.family", [])
        if isinstance(cur, str):
            cur = [cur]
        _rc["font.family"] = [fam, *cur]
        break
_rc["axes.unicode_minus"] = False


# =============================================================================
# CONSTANTS
# =============================================================================
APP_NAME: str = "Hyperspectral Viewer"
APP_VERSION: str = "v1.6.7"
APP_TITLE: str = f"{APP_NAME} {APP_VERSION}"
APP_GEOMETRY: str = "1350x700"

DELETE_RADIUS_PX: int = 8
FIG_DPI: int = 100
SAVE_DPI: int = 150

PERCENTILE_LOW: int = 2
PERCENTILE_HIGH: int = 98

TAB10_CYCLE: int = 10

# SG smoothing defaults
SG_POLYORDER: int = 2
SG_BASE_WIN: int = 51 # 15
SG_MIN_WIN: int = 3

# Median (denoise) defaults
MED_BASE_WIN: int = 21 # 7
MED_MIN_WIN: int = 3


# =============================================================================
# CUSTOM TOOLBAR WITH DIRECTORY CONTROL
# =============================================================================
class CustomNavigationToolbar(NavigationToolbar2Tk):
    """Custom toolbar that respects application's current directory."""
    
    def __init__(self, canvas, window, app_instance=None, **kwargs):
        super().__init__(canvas, window, **kwargs)
        self.app_instance = app_instance
    
    def save_figure(self, *args):
        """Override save_figure to use current HDR directory."""
        from tkinter import filedialog
        
        # Get initial directory from current HDR file
        initialdir = None
        if self.app_instance is not None:
            current_path = self.app_instance.path_var.get()
            if current_path and current_path != "-" and os.path.isfile(current_path):
                initialdir = os.path.dirname(os.path.abspath(current_path))
        
        # Get file types from canvas
        filetypes = self.canvas.get_supported_filetypes_grouped()
        default_filetype = self.canvas.get_default_filetype()

        # Prefer PNG as default when available
        preferred_ext = None
        for exts in filetypes.values():
            if 'png' in [e.lower() for e in exts]:
                preferred_ext = 'png'
                break

        # Prepare filetype list for dialog (put PNG first if present)
        items = list(filetypes.items())
        if preferred_ext is not None:
            # move any entry that contains png to the front
            items.sort(key=lambda it: 0 if preferred_ext in [e.lower() for e in it[1]] else 1)
        else:
            items.sort()

        tk_filetypes = [
            (name, '*.%s' % ' *.'.join(exts))
            for name, exts in items
        ]

        # Decide defaultextension (use .png when available)
        if preferred_ext is not None:
            defext = '.' + preferred_ext
        else:
            # fallback to canvas default
            defext = '.' + (default_filetype or 'png')

        # Open save dialog with initialdir
        fname = filedialog.asksaveasfilename(
            master=self.canvas.get_tk_widget().master,
            title='Save the figure',
            filetypes=tk_filetypes,
            defaultextension=defext,
            initialdir=initialdir  # ← 重要：初期ディレクトリを指定
        )
        
        if fname in ['', ()]:
            return
        
        # Save the figure
        try:
            self.canvas.figure.savefig(fname)
        except Exception as e:
            from tkinter import messagebox
            messagebox.showerror("Error saving file", str(e))


# =============================================================================
# COORDINATE TRANSFORMATION HELPERS
# =============================================================================
def flip_x_for_display(x: float, width: int) -> float:
    """
    Transform X coordinate from data space to display space (horizontally flipped).
    
    Args:
        x: X coordinate in data space (0 to width-1)
        width: Image width
    
    Returns:
        X coordinate in display space
    """
    return width - 1 - x


def flip_x_from_display(x: float, width: int) -> float:
    """
    Transform X coordinate from display space back to data space.
    
    Args:
        x: X coordinate in display space
        width: Image width
    
    Returns:
        X coordinate in data space (0 to width-1)
    """
    return width - 1 - x


# =============================================================================
# ICON HELPER FUNCTIONS
# =============================================================================
_ICO = b"AAABAAEAQEAAAAEAIAAoQgAAFgAAACgAAABAAAAAgAAAAAEAIAAAAAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAALywsAC8rJwAvKicALiomAC0pKgMuKicTLionLC0pJzYtKSY2LSkmNi0oJjYtKSc2LSgmNiwnJTYrJyU2LCclNiwoJjYsKCY2LCgmNi0oJjYsKCY2LCgmNi0oJjYtKSY2LSkmNi0oJjYsKCY2LCgmNi0oJjYtKCY2LSgmNi0pJjYtKSc2LSgmNiwoJjYsKCY2LSgmNi0pJjYtKSY2LSkmNi0pJzYtKSY2LSknNi0pJzYtKSc2LSknNi0pJzYtKSc2LSgmNi0oJjYtKSc2LSknNi0pJzYtKSc2LiknNi0qJywtKiYTLConAy4pJQAtKiYALSklAC0qKgAAAAAAOTQyAColIQAwKygALysoCy4pJ08uKSeiLiomyS4qJuMuKiXqLiol6i4qJeouKSXqLikl6i4qJeotKSXqLSkl6i4pJeouKSXqLiom6i4qJuouKSXqLikl6i4pJeouKSXqLikl6i4qJuouKiXqLikl6i4pJeouKSXqLikl6i4pJeouKiXqLiol6i4pJeouKSXqLikl6i4pJeouKSXqLiol6i4qJeouKibqLiom6i4qJuouKibqLiom6i4pJeouKibqLiol6i4pJeouKibqLiol6i4pJeouKibqLiom6i4qJuouKibjLiolyS4qJaMuKiZVLSonCzAsJwAjHRQAOTYzACwoJQAtKCYAMCsoHS8qJqMuKib2Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJv8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y8qJv8uKiX/Liom/y4qJf8uKiX/Liol/y4qJf8uKiX/Liom/y4qJf8uKiX/Liom/y4qJv8uKiX/Liol9y4qJqcxLSkmLCgkAB8cFgAxLSsAMi4rFC8rJ7IuKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/LisnvzAtKRsvLCgALCYiAC4qJm4uKiX+Liol/y4pJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJP8uKiX/Liol/y4qJf8uKiWCHhcPAC4pJxMvKibGLyol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKib/Lyok/ywqLf8sLDr/LSks/y8pJP8uKSX/Liol1S8sJyAwLCo4Lyom6i8qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8vKSb/Likj/ystQP8pPaD/JkXL/yk8mP8sKzb/Likl/y4qJfMuKiZLLSgmXS4pJvkuKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiT/Liol/y4qJf8uKiX/Liol/y4qJf8vKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y8qJf8vKiT/Liol/y4qJf8vKiX/Liol/y4qJf8vKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKyX/Liok/yssQP8oQLP/JEnv/yNJ8v8lSer/KTVq/y0pI/8uKib8LSkmai4nI24tKSP8Likj/y4pI/8uKSP/Lioj/y4qI/8uKiL/Likj/y0pI/8uKCP/Ligi/y0nI/8uJyP/Ligk/y4oI/8uKCP/Licj/y4nJP8uJyP/Ligj/y4nI/8uJyP/Ligi/y4oIv8uKCL/Ligi/y8oI/8vKCP/Ligk/y0oJf8tKCX/LSgl/y0oJv8tKCb/LSgl/y0oJf8tKCX/LCgl/ywoJv8sKCb/LSgl/y0oJv8sKSX/LSkl/y0pJf8sKCX/LCgl/ywpJv8tKSb/LCkl/y0pJP8tKSX/Likj/yssP/8nQK//JUnu/yNI7/8jSPD/Jkfk/ysyYP8uKSP/Lyom/C8qJ24sL1RuLi9T/C4vUv8uL1P/Li9T/y4vUv8uMFL/LjBS/y81U/8uQFL/LklR/y1MUv8tSlP/LUpT/y1KU/8tS1P/LUpT/y1KU/8tS1T/LUtT/y1LUv8tS1L/LUtS/y1LUv8tS1L/LUtS/y1LU/8sS1T/MUtJ/zZJN/87SSn/O0ko/zpJJ/87SSj/O0ko/zpJJ/87SCf/PEgn/z5HJ/9DRib/REUl/0VGJf9KQyX/UT0k/1I8JP9SPCT/Ujwj/1I8JP9TPCT/Uzwk/1M9JP9UPCT/Uz0i/z43RP8nQbX/JUru/yRI7/8kSPD/JUjo/yg6jf8tKi3/Likl/y8qJfwvKidtOULMbThF2fw2R+T/Nkbj/zVH4v82RuP/Nkfj/zZH4/82S+P/NVbj/zdv4/85nOf/O7nr/zm77P85uuz/OLvs/zi77P84u+z/OLvs/zi77P84u+z/OLvs/zi77P84u+z/OLvs/zi67f85u+b/S7ev/1+xZ/9osEP/a7A6/2uwOf9rsDn/a685/2uvOP9rrzf/bq02/3WrNf+DpjL/jqMv/5ShLf+nlir/voQm/8h9JP/KfCX/ynwl/8l8JP/KfCX/ynwk/8p8JP/KfSX/zHwj/6pxSP9HVLv/I0nu/yRJ7/8lSO//JUjn/yg5i/8tKi7/Liok/y4pJf8vKiX8LyonbS0uR20wMmL8Mz2n/zVH5P82SPX/Nkj0/zZI9P82SPT/NUj0/zRI8/8zR/P/MVTy/zWI9v85v/v/N8b9/zfG/f83xv3/N8b9/zfG/f83xv3/N8b9/zfG/f83xv3/N8b9/zfG/v84xfb/UsCg/2q6SP9vujj/b7o5/2+6Ov9vuzr/b7o6/265Of9vuTj/cbg2/3e2NP+JsDH/lqwu/52qLP+3mCf/0YUj/9aBI//XgyP/2IMj/9eDJP/XgyP/2IMk/9eDI//XgyP/2IMj/7V3Sv9PWLz/JUnw/yRJ7/8kSfD/Jkjn/yg5iP8rKi3/Liok/y4qJf8uKiX/Lyol/C8qJ20vKCRtLSkj/C0qLP8vM2b/NUTN/zZI9P82SPP/Nkjz/zZI8/80SPP/NEjy/zJI8v8yS/H/NYD0/zi/+v83xvv/N8X8/zfF/P83xfz/N8X8/zfF/P83xfz/N8X8/zfF/P83xfz/S8Gy/2u5Q/9vuTj/b7o6/2+6Of9vujn/b7o6/2+6Ov9vuDn/cLc3/3K2Nf+CsjL/kqws/56mKv+6lSj/04cr/9eHL//WiDD/14Ur/9WCJP/WgCD/1oIi/9eDJP/WgyT/14Mj/85/Kv9iXKX/Ikjy/yVJ8P8lSfD/Jkjl/yk5if8tKS3/Lioj/y4qJf8uKiX/Liol/y8qJfwvKidtLikmbS4qJvwvKiX/Likk/y8wU/82RM//Nkj0/zZI8v82SPP/Nkjz/zZI8/81SPP/M0jy/zJM8f80jfT/N8T7/zfF+/83xfv/N8X8/zfF/P83xfz/N8X8/zbF/P82xfz/P8Pi/2S7Xf9vujj/b7o6/2+6Ov9vujr/b7o5/2+6Ov9vujr/b7g4/3C3Nv91tDP/jK8z/6e3UP/Nv33/6cun//Hawv/04Mv/8+DL//HawP/qxqL/4Kpw/9mOPP/UgSP/1oEh/9eBIf/Uijf/joq2/y5S7v8iSPH/Jknl/yg5hv8rKiz/Liok/y4qJf8uKiX/Liol/y4qJv8vKib8LyonbS0pJ20uKib8Liom/y8qJf8uKiP/MDNs/zVH5v82SPP/Nkjz/zZI8/82SPP/NEjz/zNI8v8zR/L/MVbw/zem+P84xfv/NsX6/zfF/P83xfz/N8X8/zfF/P82xfz/N8X8/0/AqP9uuTz/b7o6/2+6Ov9vujr/b7o6/2+6Ov9vujr/b7o5/264OP9wtjf/kcBZ/83bp//y8+b//v7+//////////////////////////////////38+//16Nn/5buM/9iMOv/XijX/7M2r//n4+f+ksvD/M1DY/yg4hP8tKSz/Lyok/y4qJf8uKiX/Liol/y4qJf8uKib/Lyom/C8qJ20tKSZtLiom/C4qJf8uKiX/Liok/y0qLv80P6r/Nkn0/zZI8/81SPP/NUjz/zRI8/80SPP/NEjy/zJI8f8zcPL/OL76/zfF+/83xfz/N8X8/zfF/P83xfz/N8X8/zrF7/9gvG7/cLo3/2+6Ov9vujr/b7o6/2+6Ov9vuTr/b7o5/265Of9xuT3/qNCG/+zz5P/////////////////9+/j/+fPt//jt4v/47eL/+vPt//38+v////////////7+/v/y4M3/79i+///+/f/+/v3/qKeo/zU3Sv8tKir/Lyok/y4qJf8uKiX/Liol/y4qJf8uKiX/Likl/y8qJvwvKidtLColbS8qJvwvKib/Liol/y4qJf8tKiL/MDNi/zVH6P82SPP/NUjz/zRI8/80SPP/NEny/zNJ8v8ySfP/MU/y/zab9v83xvz/N8X8/zfF/P83xfz/N8X8/zbF/v9Dw9P/ablL/2+6OP9vujr/b7o6/2+6Ov9vujr/brk5/265Of9yuj//tdiZ//j79v////////////jv5f/pyKT/4KZm/9qWTP/akED/2pBA/9qXTf/gqGz/682s//nz6//////////////////8/Pz/p6Wk/zs2Mf8sKCL/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4pJf8vKib8LyonbS0qJW0vKib8Lyom/y4qJf8uKiX/Lyol/y4sNP81QsD/Nkj1/zVI8v80SPP/NEjz/zRJ8v8zSfL/Mkny/zJJ8v8xbvL/N776/zfF/P83xfz/N8X8/zfF/P82xf7/Tr+r/264PP9uujr/b7o6/2+6Ov9vujr/b7o6/265Of9uuTr/rtWR//r8+P///////v37/+3Rs//bl03/1oIl/9aAIP/WgCD/1oEi/9eBIv/VgSD/1oAg/9WDJv/bnVf/6tfD//7+////////9fX1/3Jvbf8sJyH/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Lyom/C8qJ20tKiVtLiom/C4qJf8uKiX/Lisl/y8rJv8uKiX/MjqP/zdI8/81SPL/NEjz/zRI8/80SfL/NEny/zNJ8v8zSfP/MFHx/zai9v83xvv/N8T7/zfF/P83xfz/OMX4/1i9gv9uuTf/bro5/2+6Ov9vujr/b7o6/2+6Ov9tuTf/lMpv//L47v///////fz6/+fCm//VhzH/1oAg/9WCI//WgiP/1oIj/9WCI//WgiP/1oIj/9WCI//XgSP/yHkh/3VYOv+wr6///v7+///////X1tX/S0dE/ywoJP8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liom/y8qJvwvKidtLiolbS4qJvwuKiX/Liol/y4qJf8uKiX/Lioj/zAyXv82SOf/NUjz/zRI8/80SPP/NEny/zRJ8v80SfL/M0ry/zJJ8v8ze/P/N8L7/zbF+/83xfz/N8X9/zzF6f9ju1//cLk3/2+6Of9vujr/b7o6/2+6Ov9uujn/eL1H/9fqyP///////////+zKpv/Whi3/14Eh/9eCI//WgiT/1oIj/9aCI//WgiP/1oIj/9aCI//XgiL/038k/4BTJP8uKCL/Pzs4/769vP///////////6Siof8wLCj/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4pJf8vKib8LysnbS0qJW0uKib8Liol/y4qJf8uKiX/Liol/y8rJP8uLj7/NkTR/zVI9f81SPP/NUjz/zRI8/80SfL/NEny/zJK8v8ySvL/MVrx/zaw+f82xfv/OMT8/zbF/v9Gw87/ablH/3C6OP9vujr/b7o6/2+6Ov9vujn/bbk3/57OfP/6/Pn///////Tk1P/Yjz7/1oAh/9aCJP/WgiP/14Ik/9aCI//WgiP/1oIj/9aCI//XgiP/2YIj/6hpJv87MCT/LCkl/ywnI/9UUU7/4+Pi///////p6Oj/U1BN/ywoI/8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKSX/Lyom/C8rJ20sKiVtLyom/C4qJf8uKiX/Liol/y8rJv8vKyX/LSst/zM/sv82SPb/Nkjz/zZI8/81SPP/NEjz/zRI8/8ySfL/Mkvz/y9M8v80jfT/NsX7/zbF+/81xvz/T8Co/225O/9uujn/b7o6/2+6Ov9vujr/bro5/3K5PP/K47n///////79/P/js33/1IAh/9WCIv/WgiP/1oIj/9aCI//WgiP/1oIj/9aCI//WgiP/1oIk/89/JP9mRyT/LCkl/y4qJf8uKiX/LSkl/5mXlv///////////46Miv8sKCP/Likl/y4qJf8uKiX/Liol/y4qJf8uKiX/Likl/y8qJvwvKydtLCklbS4pJfwuKiX/Liol/y4qJf8uKiX/Liol/y0qJf8yOY3/Nkj0/zZI8/82SPP/NUjz/zRI8/80SPP/NEny/zNK8/8xSvL/MWjy/zi7+v82xfz/OcX1/1y8e/9wujf/bro5/2+6Ov9wuzv/b7s6/2+5OP9+wE//6PLg///////37OD/2ZFA/9iBIf/XgiP/1oIj/9aCI//WgiP/1oIj/9eDJP/WgiP/1oIj/9mDI/+tbCT/OzAk/y0qJf8uKiX/Liom/ywnIv9bWFT/8PDv///////Bv77/NTAt/y4pJP8uKiX/Liol/y4qJf8uKiX/Liol/y4pJf8vKib8LysnbS0pJm0uKSX8Liol/y4qJf8uKiX/Lysm/y4rJv8uKiP/MDRs/zZI7f82SPP/Nkjz/zVI8/80SPP/NEjz/zRJ8v8zSfL/Mkry/y9T8f82ovf/N8b8/z/E4P9lulf/cLo5/2+6Ov9vujr/cLs7/2+7Ov9uuTf/i8Vi//X58f//////8dm//8yBK/+3cSP/yHok/9eCI//XgSP/14Ej/9eBI//YgiP/14Ej/9iCI//UgCT/dE4l/y0pJf8uKiX/Liol/y4qJf8tKSP/Pzs3/9fW1f//////3Nzb/0I+O/8tKST/Liol/y4qJf8uKiX/Liol/y4qJf8uKib/Lyom/C8rJ20tKSZtLikm/C4qJf8uKiX/Liol/y4qJf8uKiX/Lyoj/y4wTP81Rt7/Nkj0/zZI8/81SPP/NEjz/zRI8/80SfL/Mkny/zNK8/8wTPH/Mn7z/zbE/f9Kwbn/bbpA/3C7Ov9vujr/b7o6/2+6Ov9vuzr/bbg3/5XKb//5/Pj//////+HEpf90TiX/PDAk/2FEJP/EdyT/2IIj/9iBI//YgSP/2IEj/9iBI//agiP/tG8l/0AzJP8tKSb/Liol/y8rJv8uKiX/Liol/zIuKv+8u7r//////+rq6v9QTEn/LSgk/y4qJf8uKiX/Liol/y4qJf8uKiX/Likl/y8qJvwvKidtLSkmbS4qJvwuKiX/Liol/y4qJf8uKiX/Liol/y4qJP8tLDf/NEPI/zZI9f82SPP/NUjz/zRI8/80SPP/NEny/zJJ8v8yS/L/MUvy/y9e8v83s/X/WL+E/3C6OP9vujr/b7o6/2+6Ov9vujr/b7s6/224Nv+Yy3D/+vz5//////+2q6D/NS0k/ywpJv8uKiX/dE4j/9F/JP/ZgSP/2IEj/9eBI//YgSP/038j/3NNI/8uKSX/Liol/y4qJf8uKiX/Liol/y4qJf8xLSn/tbSz///////w7+//WFRR/ywnI/8uKiX/Liol/y4qJf8uKiX/Liol/y4pJf8vKib8LysobS0qJW0vKib8Lyol/y4qJf8uKiX/Liol/y8qJf8uKyX/LSsp/zM+qP82SfX/Nkjz/zZI8/81SPP/NEjz/zRI8/8ySfL/Mkrz/zFM8/8vT/P/PZHZ/2a7Vf9vujf/b7o6/2+6Ov9vujr/b7o6/2+6Ov9uuTb/ksdq//j79v//////rayq/y8rJ/8uKiX/Liom/zcuJf+SXiT/1YEk/9eBI//XgiP/14Ij/5pjJf86MCT/Liom/y4qJf8uKiX/Liol/y4qJf8uKiX/NDAs/7+/vv//////6enp/09LSP8sKCP/Liol/y4qJf8uKiX/Liol/y4qJf8uKSX/Lyom/C8rKG0tKiVtLyom/C8qJv8uKiX/Liol/y4qJf8uKiX/Liol/y8qI/8yOIH/N0ny/zZI8/82SPP/NUjz/zRI8/80SPP/M0ny/zJK8/8xTPP/L030/zxkpP9przz/b7o6/2+6Ov9vujr/b7o6/2+6Ov9vujr/brg2/4jCW//y9+3//////8nIx/83My//LSkk/y4rJf8tKSb/PTEk/4xbJf/FeCT/zHwk/5xlJf9ENST/LSkm/y4qJf8uKiX/Liol/y4qJf8uKiX/LSkk/0I/Ov/b29r//////9va2v9BPTn/LSgk/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y8qJvwvKidtLSkmbS8qJvwuKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiP/LzJZ/zdH5/81SPT/NUjz/zVI8/80SPP/NEjz/zNJ8v8ySvP/MUzz/zFN6f8vO2b/WIoy/2+8Ov9vujr/b7o6/266Ov9uujr/brk6/2+4Nv97u0b/4u7W///////o6Of/UU1K/ywnI/8uKiX/Liol/y4qJf8zLCX/Tjok/1M+JP85LyT/LSkl/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/ywnIv9kYF7/9PTz//////+8urn/My8r/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJv8vKib8LyonbS0oJm0uKSX8Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liok/y4tOv81Q8v/NUj0/zVI8/80SPP/NEjz/zRI8/8zSfL/MUny/zFL9P8vSMb/LCs4/0FRKf9rsDr/b7s6/2+6Ov9uujr/brk5/2+5Of9vtzf/cbM2/7nMpf///////v/+/4+Ni/8sJyT/Likl/y4qJf8uKiX/Liol/ywpJf8sKSX/LSol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJP8wLCj/qKal///////+/v7/h4WC/ywoI/8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKib/Lyom/C8qJ20tKSZtLikl/C4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y8rJf8uKij/Mzyc/zZI9P80SPP/NEjz/zRI8/80SPP/M0ny/zJJ8v8xS/P/Lz2Q/y4qJv8vLiT/VoMy/3C7Ov9vujr/b7o6/2+5Of9vuDj/crg2/2SYMf9pb13/8PDw///////e3d3/T0tJ/ywoI/8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8rJyL/Y19d/+3s7P//////4eHg/01JRv8sKCP/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y8qJvwvKidtLiknbS4qJvwuKiX/Liol/y4qJf8uKiX/Liol/y8rJv8vKyb/Lioj/y8yYf83Ruj/NUj0/zZI8/82SPP/NUjz/zNJ8v8ySfL/MUnj/y4xWf8vKiP/Likl/ztKKP9pqjn/b7o6/2+5OP9vuDj/cLg3/3CwNv9FXCr/NC8r/7Curf///////////7m4t/89Ojb/LCgj/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y8qJv8rJyP/SkdD/8/Ozf///////v7//5SSkf8vKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJv8vKib8LysnbS0pJm0uKib8Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Lysm/y8qJf8uKzP/NEC7/zZI9f82SPP/Nkjz/zVI8/80SfL/Mkr0/zFCt/8uKzL/Liok/y4qJf8uKyT/TWwv/262Ov9vujn/b7k4/3K0N/9TdS7/MS4l/ywoI/9STkv/3t3c///////+/v7/s7Kx/0ZCP/8rJyL/LSkk/y4qJf8uKiX/Liol/y4qJf8uKiX/Lysm/y0pJP8tKCP/VFFN/8fGxf///////////8nJyP9BPjr/LSkj/y4qJf8vKyb/Liol/y4qJf8uKiX/Liol/y4qJf8uKSX/Lyom/C8qJ20tKSZtLiom/C4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Lioi/y40bf82R+r/NUjz/zVI8/80SPP/NEjz/zNJ6P8uNWz/LSkk/y4qJf8uKiX/LSkl/zAxJf9LbC7/ZJ42/2ObNf9Oay3/MjIl/y4pJf8uKiX/LSkj/29saf/r6+v////////////Pz87/cnBt/zs3Mv8sKCP/Kyci/ysnIv8rJyL/Kyci/y4qJf9CPzv/hIKA/97e3f///////////97e3f9aV1T/LCgi/y4qJf8uKiX/Lysm/y4qJf8uKiX/Liol/y4qJf8uKiX/Likl/y8qJvwvKidtLSgmbS4qJvwuKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Lyol/y8rJP8uKzD/Mj2k/zZI8/80SPT/NUj0/zRJ8f8xPqP/LSsv/y4qJP8vKib/Liol/y4qJf8uKSX/Lisl/zQ3J/8yNiX/Liok/y4qJf8uKiX/Liol/y4qJf8uKiX/cm9t/+Tj4/////////////f39//Lysn/l5WT/3Nxb/9lY2D/ZmRi/3l3df+hn57/19bV//z8/P///////////9ra2f9iX1z/LCgj/y4qJf8uKiX/Liol/y8rJv8uKiX/Liol/y4qJf8uKiX/Liol/y4qJv8vKib8LyonbS0oJm0uKSX8Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y8qJf8vKyX/Liok/ywtOv80PJj/NkbX/zVH3/8zPqT/Li08/y8qJP8tKyX/Liol/y4qJf8vKiX/Likl/y4qJP8uKSX/Likl/y4pJf8uKiX/Liol/y4qJf8uKiX/Liol/y0pJf9cWFb/w8LB//v7+//////////////////7+/v/9/f3//f39//9/f3/////////////////9/f3/7e1tP9TT0v/LCgj/y4qJf8uKiX/Liol/y8rJv8vKyb/Liol/y4qJf8uKiX/Liol/y4qJf8uKSX/Lyom/C8qJ20tKSVtLiom/C4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y8rJv8uKyb/Liol/y8rJv8vKiX/LSsq/y4uRP8uMEz/Lisw/y8rJf8vKyb/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8tKiX/Liol/y4qJf8uKiX/Lyol/y4qJf8uKSX/LCcj/zw4NP99enj/xsXF//Dw8P/+/v7///////////////////////39/f/r6+v/vby7/3FubP84My//LSgj/y4qJf8uKiX/Liol/y4qJf8uKiX/Lysm/y4qJf8uKiX/Liol/y4qJf8uKiX/Likl/y8qJvwvKydtLSklbS4pJfwuKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8vKyb/Lysm/y4qJf8uKiP/Lioj/y8qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKST/LCcj/zg0Mf9cWFb/g4B+/52bmf+hn57/oZ+e/5qYlv98eXf/VFFO/zUxLf8sJyL/Liok/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJv8vKib8LyonbS0pJW0uKSX8Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKib/Lysm/y8qJv8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJv8uKiX/Liol/y4qJv8uKiX/Liol/y4qJv8uKiX/LCgj/ywoIv8tKST/LSgl/y0pJf8sKCT/Kyci/ywoI/8uKSX/Liom/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKib/Lyol/C8qJ20tKSVtLikl/C4qJf8vKyb/Lysm/y4qJf8uKiX/Liol/y4qJf8uKiX/LSkk/y0oI/8uKCP/LSgj/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJv8uKSX/LCcj/ywoI/8sJyP/LSkk/y4qJf8uKiX/Liol/y4qJf8uKiX/LSkk/ysnIv8sKCP/Liom/y8rJ/8uKiX/LCgj/ywoI/8uKSX/Likm/y4qJf8vKyb/Liol/y8rJv8tKST/LCgj/ywoI/8sKCL/Liok/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liom/y8qJvwvKidtLSklbS4qJfwuKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/zs4M/9XVFH/WFVT/1dTUP85NjH/Liol/y8rJv8vKyb/Liol/y8rJv8uKyT/ODUw/1VTUP9YVVL/WFVS/z06Nf8tKST/Liol/y4qJf8uKiX/LSgk/z05Nv9nZWL/kI6N/6mopv+wrq3/paOh/4iFhP9cWFX/NjEu/ywnJP8uKiX/Lysm/y8rJv8vKyX/R0RA/1lWU/9YVlP/UExJ/zEsKf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8vKib8LyonbS0pJm0uKib8Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/ysnIv9qaGT/7Ozr//Hx8f/p6en/Y2Bd/ywoI/8vKyb/Lysm/y8rJv8uKiX/LCgj/1xZVv/n5ub/8vHx/+/v7v91c3D/Kyci/y4qJf8uKSX/Lysn/25raf/My8v/9vb2////////////////////////////8O/v/7m3tv9ZVVP/LSkk/y4qJf8vKib/Lysm/6Kgn//09PT/8/Pz/8rIyP89ODX/Likl/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKib/Lyom/C8qJ20tKCZtLikl/C4qJf8uKiX/Lysm/y4qJf8uKiX/Liol/y4qJf8rJyL/b21p//v7+///////+Pj4/2dkYf8rJyL/Liol/y4qJf8uKiX/Liol/ysnI/9gXVr/9fX1///////+/v7/enl1/yonIv8uKiX/LSkl/3VycP/u7u7/////////////////+fn5//b29v/7+/v/////////////////39/e/2BdWv8sKCP/Likm/zArJv+rqaj////////////V1NT/Pjo2/y4pJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liom/y8qJvwvKidtLSkmbS4pJfwuKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Kyci/25saf/6+vr///////f39/9nZGH/Kyci/y4qJf8uKiX/Liol/y4qJf8sJyP/YF1a//T09P///////f39/3p4df8rJyL/LSkk/0hEQP/a2dn////////////v7+7/oZ+e/2xpZ/9kYV3/dHBu/6+trP/19fX////////////GxcT/Ozcz/y4oJf8vKyb/q6mo////////////1NTT/z05Nf8tKST/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4pJf8vKib8LysnbS0pJW0uKSX8Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/ysnIv9vbGn/+vr6///////39/f/Z2Rh/ysnIv8uKiX/Liol/y4qJf8uKiX/LCcj/2BdWv/09PT///////39/f96eHb/Kici/ywnIv97eHb//v7+////////////j42L/y8rJv8rJyL/Kyci/ysnIv8zLyr/o6Gg////////////9PT0/2NgXf8sJyP/Lysm/6upqP///////////9TT0/89OTX/LSkk/y4qJf8uKiX/Liol/y4qJf8vKyb/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Lyom/C8qJ20tKiVtLikl/C4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8rJyL/b2xp//r6+v//////9/f3/2dkYf8rJyL/Liol/y4qJf8uKiX/Liol/ywnI/9gXVr/9PT0///////9/f3/enh2/ysnI/8tKST/jImH/+Tj4//k4+L/1dTT/1BNSf8sKCP/Lysm/y8rJv8vKyb/KiYh/3FubP/7+/v///////z8/P90cW7/KyYi/y8rJv+rqaj////////////U09P/PTk1/y0pJP8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liom/y8qJvwvKidtLiolbS4qJvwuKib/Liol/y4qJf8uKiX/Liol/y4qJf8vKyb/LCgj/29sav/6+vr///////f39/9mY2D/KiUh/y0oJP8tKSP/LSkj/y0pI/8qJiD/X1xY//T09P///////f39/3p4dv8rJyP/Lyol/zw4M/9HQz//SUVA/0VBPv8xLSj/Liok/ywpJP8rJyL/Liol/0M/PP+vraz////////////39/f/Z2Rh/ywnI/8vKyb/q6mo////////////1NPT/z05Nf8tKST/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJv8vKib8LysnbS0qJW0uKib8Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/ysnIv9vbGr/+vr6///////4+Pj/e3h3/0dDQP9JRkP/SkZD/0pHQ/9JRkP/R0RA/3VycP/29vX///////39/f96eHb/Kycj/y8rJv8tKST/LSkk/y0pJP8rJyL/Kycj/zUwLP9MSUb/cG5r/5+dm//W1tX//fz8////////////z87N/z87OP8tKST/Lysm/6upqP///////////9TT0/89OTX/Likk/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Lyom/C8qJ20tKSVtLikl/C4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8rJyL/b2xq//r6+v///////v7+/+zr6//k5OP/5OTk/+Tk5P/k5OT/5OTk/+Tk4//r6ur//v7+///////9/f3/enh2/ysnI/8uKiX/Lysm/y8rJf8tKST/RkI+/4F+ff+8urr/5eXl//r6+v//////////////////////5OTj/2hlY/8sKCT/Lyol/zArJv+rqaj////////////U09P/PTk1/y0pJP8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liom/y8qJvwvKidtLikmbS4qJvwuKiX/Liol/y4qJf8uKiX/Liol/y4qJf8vKyb/Kyci/25saf/6+vr//////////////////////////////////////////////////////////////////f39/3p4dv8rJyP/Liol/y4qJf8wLSj/dHFv/9fW1v/9/f3////////////////////////////u7e3/trSz/1xYVv8uKiX/Liol/y8qJv8wKyf/q6mo////////////1NPT/z05Nf8tKST/Liol/y4qJf8uKiX/Liol/y8rJv8uKiX/Liol/y4qJf8uKiX/Liol/y4qJv8vKib8LysobS0pJm0uKSb8Liol/y4qJf8vKyb/Liol/y4qJf8uKiX/Lysm/ysnIv9ubGn/+vr6///////+/v7/9fX1//Hx8f/x8fH/8vHx//Lx8f/y8fH/8fHx//X09P/+/v7///////39/f96eHb/Kycj/y8rJv8tKST/bWtp/+/u7v/////////////////9/P3/6ejo/8PCwf+QjY3/WlZT/zUxLP8tKCP/Lysm/y8rJv8vKib/MCsn/6upqP///////////9TT0/89OTX/Liol/y8rJv8vKyb/Liol/y8rJv8vKyb/Lysm/y4qJf8uKiX/Liol/y4qJf8uKib/Lyom/C8rKG0tKSZtLikl/C4qJf8uKiX/Liol/y4qJf8uKiX/Lyom/y8rJv8sKCP/b2xp//r6+v//////+fn5/4aEg/9YVFH/WldU/1pXVP9bV1T/W1dV/1hUUv+Bfn3/9vb2///////9/f3/enh2/ysnI/8uKiX/OTUx/8bGxf////////////r6+v/Ew8H/f3x6/1FNSv82Mi7/LCgk/ywnI/8tKST/Liol/y4qJf8uKiX/Lyom/zArJ/+rqaj////////////U09P/PTk1/y4qJf8vKyb/Liol/y8rJv8vKyb/Lysm/y4qJf8uKiX/Liol/y4qJf8uKiX/Liom/y8qJvwvKydtLiknbS4qJvwuKiX/Liol/y4qJf8uKiX/Liol/y8rJv8vKyb/Kyci/29saf/6+vr///////f39/9lYl//KSUg/ywoI/8rJyL/LCci/ywoI/8pJSD/XVtY//T09P///////f39/3p4dv8rJyL/LSgj/0tHQ//n5ub///////////+wr67/Ojcy/ywoI/8tKCT/Liol/y4qJf82Mi7/Pjo2/z46Nv84NDD/Liol/y4qJv8vKyb/q6mo////////////1NPT/z05Nf8tKST/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJv8vKib8LyonbS0pJ20uKib8Liol/y4qJf8uKiX/Liol/y4qJf8vKyb/Lysm/ysnIv9ubGn/+vr6///////39/f/ZmRh/ysnIv8uKiX/Liol/y4qJf8uKiX/LCgj/19dWv/09PT///////39/f96eHb/Kycj/y0pJP9NSUX/6Ojo////////////hYOB/yolIf8vKyb/Lysm/y4pJP8vKyb/l5aU/9fX1v/Y19b/l5WT/y8rJv8vKib/Lysm/6upqP///////////9TT0v89OTX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKib/Lyom/C8qJ20uKSduLyom/C4qJf8uKiX/Liol/y4qJf8uKiX/Lysm/y4qJf8sKCL/bmxp//r6+v//////9/f3/2ZkYf8rJyL/Liol/y4qJf8uKiX/Liol/ysoI/9fXVr/9PT0///////9/f3/enh2/ysnIv8uKiT/Pzs3/9XU1P///////////8vKyf9PTEn/MCwo/y4rJv81MSz/bWpo/+rq6f///////////5KRj/8sKCT/Lyom/zArJv+rqaj////////////U09P/PTk1/y0pJP8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liom/y8qJvwvKidtLSgmbi4qJvwvKyb/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Kyci/25saf/6+vr///////f39/9nZGH/Kyci/y4qJf8uKiX/Liol/y4qJf8rKCP/YF1a//T09P///////f39/3p4dv8rJyP/Lysm/y4qJf+Nion//f39////////////4N/f/7Oysv+sq6r/wsHA/+/v7////////////9/f3v9PTEn/LCgj/y4qJv8wKyb/q6mo////////////1NPT/z05Nf8uKST/Lysm/y4qJf8vKyb/Lysm/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJv8vKib8Lyonbi0oJl0uKSb5Liol/y4qJf8uKiX/Lysm/y4qJf8uKiX/Lysm/ysoI/9vbWr//f39///////6+vr/aGVi/ysnIv8uKiX/Liol/y4qJf8uKiX/LCgj/2BeW//39/f///////////97eXf/Kyci/y4qJf8uKST/Ozcz/6Wkov/39vb//////////////////////////////////////97d3f9saWf/Liok/y4qJf8vKib/MCsn/62rqv///////////9fW1v8+Ojb/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKib/Lyom+y0pJmcxKyo2Lyom6C8rJv8uKiX/Liol/y8rJv8uKiX/Lysm/y8rJv8tKST/WVZS/7a1tP+7ubn/tbOy/1RRTf8tKST/Liol/y4qJf8uKiX/Liol/y0pJP9PTEn/srGw/7u6uP+4t7b/YV5a/ywoI/8vKyb/Liol/y4qJf82Mi3/cW5r/7Szsv/a2tr/5+fn/+rq6v/k5OP/z87O/5mXlv9QTEn/LSkk/y4qJf8uKiX/Lyol/y8qJ/+Bfn3/vLu6/7y7uf+dmpn/ODMw/y4qJf8uKiX/Liol/y4qJf8uKiX/Lysm/y4qJf8uKiX/Liol/y4qJf8uKib/Lyom/y4qJvEuKihGKyglEC4qJsEvKyb/Liol/y4qJf8uKiX/Lysm/y8rJv8vKyb/Lysm/zAsJ/8yLir/My8q/zIuKv8wLCf/Lysm/y4qJf8uKiX/Liol/y4qJf8uKiX/Lysn/zIuKv8yLir/Mi4q/y8sJ/8uKiX/Liol/y8rJv8uKiX/Liok/y0oI/8yLir/Qj07/0xIRv9PS0j/SUVC/zw4NP8uKib/LCgk/y4qJf8uKiX/Liol/y4rJv8vKyb/MSwo/zIuKv8yLir/MS0p/y8qJv8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y8qJv8uKibNLyooGjIrKQAvKihmLyom/C4qJf8uKiX/Liol/y8rJv8vKyb/Lysm/y8rJv8uKiX/Liol/y4rJP8uKiT/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJv8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4pJf8tKCT/LSgk/y0pJP8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Lism/y4qJf8uKiX/Liol/y4qJf8uKib/LiondC4rJwAwKykAMS0rDi8rJ6guKib/Liol/y4qJf8vKyb/Lysm/y8rJv8vKyb/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8vKyb/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Lysm/y4qJf8vKyb/Lysm/y8rJv8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKiX/Liol/y4qJf8uKib/LionsS8sKhQvKygALyooADAsKgAxLisaLysnly8qJvEvKyb/Lysm/y8rJv8vKyb/Lysm/y8rJv8vKyX/Lyol/y8qJf8vKyX/Liol/y8qJf8vKiX/Liol/y4qJf8vKyb/Lyol/y4qJf8vKiX/Lyol/y8qJf8vKiX/Lyol/y8rJf8uKiX/Liol/y8qJf8vKyb/Lysm/y8rJv8vKyb/Lysm/y8qJf8uKiX/Liol/y4qJf8vKiX/Lysm/y8qJf8uKiX/Liol/y4qJf8uKiX/Lyol/y8rJv8vKyb/Lyol/y4qJf8vKiX/Liol/y8rJf8uKiX/Liol/y8rJf8uKiXxLyonnTEsKx4wKygALisnADMwLQAvLCkAMC0qADIvLQcuKic+Lyomii4qJ7wvKibGLykmxi8qJsYvKiXGLyolxi8qJcYvKiXGLyolxi8qJcYvKibGLyomxi8pJsYvKSbGLyomxi8qJsYvKibGLyomxi8qJsYvKiXGLyokxi8qJcYvKiXGLyolxi8qJsYvKiXGLyomxi8qJcYvKiXGLyomxi8pJsYvKSbGLyomxi8qJcYvKiXGLyolxi8qJcYvKiXGLyolxi8qJsYvKiXGLyolxi8qJcYvKibGLyomxi8qJcYvKiXGLyslxi8qJcYvKiXGLiolxi4qJr0vKiaPLyonQjItKwcwLCkALikmADEtLQAAAAAAODUyADAtKgAxLisALSomACwqFgAvKysMLiooEC0oJhAtKSUQLSolEC4qJhAuKiYQLiomEC4qJhAuKicQLikmEC4pJhAuKSYQLikmEC4pJhAuKSYQLikmEC4pJhAtKSYQLiomEC4qJhAuKiYQLSkmEC4pJhAuKSYQLikmEC4pJhAtKSYQLSkmEC0pJhAtKSYQLSkmEC4pJhAuKSYQLSkmEC0oJhAtKCYQLikmEC4pJhAtKSYQLikmEC4pJhAtKSYQLSkmEC0pJhAtKiUQLSolEC4qJhAuKiYQLiomEC4rJhAuKycM3lcJAC8qJgAxLCoAMSwpADMuLQAAAAAAgAAAAAAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAAE="

def set_icon(win):
    """Set application icon for window."""
    icon_file = tempfile.NamedTemporaryFile(delete=False, suffix=".ico")
    icon_file.write(base64.b64decode(_ICO))
    icon_file.close()
    try:
        win.iconbitmap(icon_file.name)
    except:
        pass


def enable_taskbar_icon(app_id="iken008.hsi.viewer"):
    """Enable taskbar icon on Windows."""
    try:
        import ctypes
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(app_id)
    except:
        pass


# =============================================================================
# MAIN APPLICATION CLASS
# =============================================================================
class HyperspecTk(tk.Tk):
    """
    Main Tk application for Hyperspectral Viewer.
    Refactored for better organization while maintaining identical behavior.
    """

    # =========================================================================
    # INITIALIZATION
    # =========================================================================
    def __init__(self) -> None:
        super().__init__()
        enable_taskbar_icon()
        set_icon(self)
        self.title(APP_TITLE)
        self.geometry(APP_GEOMETRY)

        # Initialize state variables
        self._init_state_variables()
        
        # Build UI components
        self._build_menu()
        self._build_topbar()
        self._build_panes()
        self._build_left_tabs()
        self._build_right_panel()
        self._set_sliders_state(tk.DISABLED)

        # Set window on center
        self.after(0, self.center_window)

        # Setup hotkeys
        self._setup_hotkeys()

    def _init_state_variables(self) -> None:
        """Initialize all state variables."""
        # Initialize custom style for menubutton without arrow
        style = ttk.Style()
        style.layout('NoArrow.TMenubutton', [
            ('Menubutton.background', None),
            ('Menubutton.button', {'children':
                [('Menubutton.padding', {'children':
                    [('Menubutton.label', {'side': 'left'})]
                })]
            }),
        ])
        
        # HSI data
        self.img = None
        self.data: Optional[np.ndarray] = None
        self.wavelengths: Optional[np.ndarray] = None
        
        # Display state
        self.gray_band: int = 0
        self.rgb_bands: Dict[str, Optional[int]] = {"R": None, "G": None, "B": None}
        self.cmap_name = tk.StringVar(value="gray")
        self._snapping: bool = False
        self._is_full = False
        
        # Status message
        self.status_var = tk.StringVar(value="Ready")
        
        # 初期化後にSGオーダーの表示を設定
        def _after_init():
            if hasattr(self, 'sg_order_btn'):
                self._update_sg_order_display()
        self.after(100, _after_init)
        self._status_after_id = None
        
        # Color palette (fixed 10)
        self._palette10 = [plt.cm.tab10(i) for i in range(10)]
        
        # Points and polygons
        self.points: List[Dict[str, Any]] = []
        self.external_spectra: List[Any] = []
        self._pt_color_idx = 0
        self.polygons: List[Dict[str, Any]] = []
        self._pg_color_idx = 0
        
        # Processing mode
        self.mode_var = tk.StringVar(value="Reflectance")
        
        # SG微分次数の選択用
        self.sg_deriv_var = tk.StringVar(value="0th")
        
        # Caches
        self._hsi_cache: Dict[str, Tuple[Optional[np.ndarray], Optional[np.ndarray]]] = {}
        self._pt_raw_cache: Dict[Tuple[str, int, int], np.ndarray] = {}
        self._pt_proc_cache: Dict[Tuple, np.ndarray] = {}
        self._poly_idx_cache: Dict[Tuple[str, Tuple[Tuple[int, int], ...]], np.ndarray] = {}
        self._poly_proc_cache: Dict[Tuple, Tuple[np.ndarray, np.ndarray, np.ndarray, int]] = {}
        
        # Polygon drawing state
        self.poly_mode = tk.BooleanVar(value=False)
        self._poly_drawing_axes = None
        self._poly_temp_verts: List[Tuple[int, int]] = []
        
        # View state
        self._view_forced_reset_gray = False
        self._view_forced_reset_rgb = False
        self._pts_visible = False

        # フィルタ窓サイズ（HDR読み込み時に自動設定）
        self.med_window = MED_BASE_WIN
        self.sg_window = SG_BASE_WIN

    # =========================================================================
    # UI CONSTRUCTION
    # =========================================================================
    def _build_menu(self) -> None:
        """Build menu bar."""
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
        # Settings menu
        s = tk.Menu(m, tearoff=False)
        s.add_command(label="Filter Parameters...", command=self._open_filter_settings)
        m.add_cascade(label="Settings", menu=s)
        self.config(menu=m)

    def _open_filter_settings(self) -> None:
        """Open filter parameters dialog."""
        dlg = tk.Toplevel(self)
        dlg.title("Filter Parameters")
        dlg.geometry("400x200")
        dlg.resizable(False, False)
        dlg.transient(self)
        
        # Center dialog
        self.update_idletasks()
        x = self.winfo_x() + (self.winfo_width() - 400) // 2
        y = self.winfo_y() + (self.winfo_height() - 200) // 2
        dlg.geometry(f"+{x}+{y}")
        
        frm = ttk.Frame(dlg, padding=20)
        frm.pack(fill=tk.BOTH, expand=True)
        
        # Median window
        ttk.Label(frm, text="Median Filter Window:").grid(row=0, column=0, sticky="w", pady=8)
        med_var = tk.IntVar(value=self.med_window)
        med_spin = ttk.Spinbox(frm, from_=3, to=101, increment=2, textvariable=med_var, width=10)
        med_spin.grid(row=0, column=1, sticky="w", padx=10)
        ttk.Label(frm, text="(odd, 3-101)", foreground="gray").grid(row=0, column=2, sticky="w")
        
        # SG window
        ttk.Label(frm, text="Savitzky-Golay Window:").grid(row=1, column=0, sticky="w", pady=8)
        sg_var = tk.IntVar(value=self.sg_window)
        sg_spin = ttk.Spinbox(frm, from_=5, to=201, increment=2, textvariable=sg_var, width=10)
        sg_spin.grid(row=1, column=1, sticky="w", padx=10)
        ttk.Label(frm, text="(odd, 5-201)", foreground="gray").grid(row=1, column=2, sticky="w")
        
        # Info
        bands = self.wavelengths.size if self.wavelengths is not None else 0
        info = f"Current bands: {bands}"
        ttk.Label(frm, text=info, foreground="gray").grid(row=2, column=0, columnspan=3, pady=(15, 0))
        
        # Buttons
        btn_frm = ttk.Frame(frm)
        btn_frm.grid(row=3, column=0, columnspan=3, sticky="e", pady=(20, 0))
        
        def apply():
            # 奇数に調整
            m = med_var.get() | 1
            s = sg_var.get() | 1
            self.med_window = max(3, min(101, m))
            self.sg_window = max(5, min(201, s))
            # キャッシュクリアして再描画
            self._pt_proc_cache.clear()
            self._poly_proc_cache.clear()
            self._redraw_spec_lines()
            dlg.destroy()
        
        ttk.Button(btn_frm, text="Cancel", command=dlg.destroy).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frm, text="Apply", command=apply).pack(side=tk.LEFT)

    def _build_topbar(self) -> None:
        """Build top toolbar."""
        top = ttk.Frame(self)
        top.pack(fill=tk.X, padx=8, pady=(6, 4))
        ttk.Button(top, text="Load Meta...", command=self.load_meta_json).pack(side=tk.LEFT)
        ttk.Button(top, text="Open HDR...", command=self.open_hdr).pack(side=tk.LEFT, padx=(8, 0))
        self.path_var = tk.StringVar(value="-")
        ttk.Label(top, textvariable=self.path_var).pack(side=tk.LEFT, padx=10)

    def _build_panes(self) -> None:
        """Build main paned window."""
        self.pw = ttk.PanedWindow(self, orient=tk.HORIZONTAL)
        self.pw.pack(fill=tk.BOTH, expand=True, padx=6, pady=(0, 6))
        self.left = ttk.Frame(self.pw)
        self.right = ttk.Frame(self.pw)
        self.pw.add(self.left, weight=1)
        self.pw.add(self.right, weight=1)

        # Shortcuts for deletion
        self.bind('<BackSpace>', self.on_delete_last_marker)
        self.bind('<Delete>', self.on_delete_last_marker)

    def _build_left_tabs(self) -> None:
        """Build left panel with Gray/RGB image tabs."""
        self.nb = ttk.Notebook(self.left)
        self.nb.pack(fill=tk.BOTH, expand=True, padx=6, pady=0)

        # Gray image tab
        self._build_gray_tab()
        
        # Pseudo RGB tab
        self._build_rgb_tab()

        self.nb.bind("<<NotebookTabChanged>>", self.on_tab_changed)

    def _build_gray_tab(self) -> None:
        """Build gray image tab."""
        self.tab_gray = ttk.Frame(self.nb)
        self.nb.add(self.tab_gray, text="Gray Image")

        # Wavelength slider
        row = ttk.Frame(self.tab_gray)
        row.pack(fill=tk.X, padx=6, pady=(6, 0))
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

        # Colormap selector
        row2 = ttk.Frame(self.tab_gray)
        row2.pack(fill=tk.X, padx=6, pady=6)
        ttk.Label(row2, text="Colormap:").pack(side=tk.LEFT)
        cmaps = ["gray", "viridis", "magma", "plasma", "inferno", "cividis", "jet", "turbo", "gnuplot2"]
        self.cmap_cb = ttk.Combobox(row2, state="readonly", values=cmaps, textvariable=self.cmap_name, width=12)
        self.cmap_cb.pack(side=tk.LEFT, padx=6)
        self.cmap_cb.bind("<<ComboboxSelected>>", lambda e: self._update_gray_image())

        # Viewer
        viewer_gray = ttk.Frame(self.tab_gray)
        viewer_gray.pack(fill=tk.BOTH, expand=True, padx=6, pady=(15, 0))
        self.gray_fig = Figure(figsize=(6, 6), dpi=FIG_DPI)
        self.ax_gray = self.gray_fig.add_subplot(111)
        self.ax_gray.set_xticks([])
        self.ax_gray.set_yticks([])
        self.gray_canvas = FigureCanvasTkAgg(self.gray_fig, master=viewer_gray)
        self.toolbar_gray = CustomNavigationToolbar(self.gray_canvas, viewer_gray, app_instance=self, pack_toolbar=False)
        self.toolbar_gray.update()
        self.toolbar_gray.pack(side=tk.BOTTOM, fill=tk.X)
        self._wrap_toolbar_home(self.toolbar_gray, which="gray")
        self.gray_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self.gray_fig.canvas.mpl_connect("button_press_event", self.on_image_click)

    def _build_rgb_tab(self) -> None:
        """Build pseudo RGB tab."""
        self.tab_rgb = ttk.Frame(self.nb)
        self.nb.add(self.tab_rgb, text="Pseudo RGB")

        # RGB sliders
        self.r_var = tk.DoubleVar()
        self.g_var = tk.DoubleVar()
        self.b_var = tk.DoubleVar()
        
        self.r_scale, self.r_label = self._make_rgb_slider(self.tab_rgb, "R", self.r_var)
        self.g_scale, self.g_label = self._make_rgb_slider(self.tab_rgb, "G", self.g_var)
        self.b_scale, self.b_label = self._make_rgb_slider(self.tab_rgb, "B", self.b_var)

        # Viewer
        viewer_rgb = ttk.Frame(self.tab_rgb)
        viewer_rgb.pack(fill=tk.BOTH, expand=True, padx=6, pady=(15, 0))
        self.rgb_fig = Figure(figsize=(6, 6), dpi=FIG_DPI)
        self.ax_rgb = self.rgb_fig.add_subplot(111)
        self.ax_rgb.set_xticks([])
        self.ax_rgb.set_yticks([])
        self.rgb_canvas = FigureCanvasTkAgg(self.rgb_fig, master=viewer_rgb)
        self.toolbar_rgb = CustomNavigationToolbar(self.rgb_canvas, viewer_rgb, app_instance=self, pack_toolbar=False)
        self.toolbar_rgb.update()
        self.toolbar_rgb.pack(side=tk.BOTTOM, fill=tk.X)
        self._wrap_toolbar_home(self.toolbar_rgb, which="rgb")
        self.rgb_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self.rgb_fig.canvas.mpl_connect("button_press_event", self.on_image_click)

    def _make_rgb_slider(self, parent, label: str, var: tk.DoubleVar) -> Tuple[tk.Scale, tk.StringVar]:
        """Create RGB wavelength slider."""
        r = ttk.Frame(parent)
        r.pack(fill=tk.X, padx=6, pady=0)
        ttk.Label(r, text=f"{label} wavelength:").pack(side=tk.LEFT)
        sc = tk.Scale(
            r, variable=var, command=self.on_rgb_scale, orient=tk.HORIZONTAL,
            length=460, width=16, sliderlength=18, from_=0.0, to=0.0, resolution=1.0, showvalue=True
        )
        sc.pack(side=tk.LEFT, padx=8)
        lv = tk.StringVar(value=f"{label}: -")
        ttk.Label(r, textvariable=lv).pack(side=tk.LEFT)
        return sc, lv

    def _build_right_panel(self) -> None:
        """Build right panel with spectra plot and controls."""
        # Header
        hdr = ttk.Frame(self.right)
        hdr.pack(fill=tk.X, padx=6, pady=(6, 0))
        ttk.Label(hdr, text="Spectra", font=("", 11, "bold")).pack(side=tk.LEFT)
        ttk.Button(hdr, text="Reset Spectra", command=self.reset_spectra).pack(side=tk.RIGHT)

        # Tools row
        self._build_tools_row()

        # Plot range
        self._build_plot_range_controls()

        # Points/Polygons panel
        self._build_points_panel()

        # Spectra viewer
        self._build_spectra_viewer()

    def _build_tools_row(self) -> None:
        """Build tools row with mode selector and preprocessing options."""
        tools = ttk.Frame(self.right)
        tools.pack(fill=tk.X, padx=6, pady=(6, 2))
        
        # Mode selector
        ttk.Label(tools, text="Mode:").pack(side=tk.LEFT)
        self.mode_cb = ttk.Combobox(
            tools, state="readonly",
            values=["Reflectance", "Absorbance"],
            textvariable=self.mode_var, width=12
        )
        self.mode_cb.pack(side=tk.LEFT, padx=(4, 12))
        self.mode_cb.bind("<<ComboboxSelected>>", lambda e: self.on_mode_change())

        ttk.Separator(tools, orient="vertical").pack(side=tk.LEFT, fill=tk.Y, padx=8)

        # Preprocessing checkboxes
        self.noise_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(tools, text="Denoise (median)", variable=self.noise_var,
                        command=self.on_noise_toggle).pack(side=tk.LEFT, padx=(2, 10))
        # SGフィルター関連のコントロール
        # SGフィルター関連のコントロール
        self.smooth_var = tk.BooleanVar(value=False)
        sg_frame = ttk.Frame(tools)
        sg_frame.pack(side=tk.LEFT, padx=(2, 10))
        
        # SGフィルターのメインチェックボックス
        ttk.Checkbutton(sg_frame, text="SG", variable=self.smooth_var,
                       command=self.on_smooth_toggle).pack(side=tk.LEFT)
        
        # 微分次数選択用のドロップダウンメニュー
        self.sg_order_btn = ttk.Menubutton(sg_frame, text="▼", style="NoArrow.TMenubutton")
        self.sg_order_btn.pack(side=tk.LEFT, padx=2)
        
        order_menu = tk.Menu(self.sg_order_btn, tearoff=0)
        self.sg_order_btn["menu"] = order_menu
        for deriv in ["0th", "1st", "2nd"]:
            order_menu.add_radiobutton(
                label=deriv,
                variable=self.sg_deriv_var,
                value=deriv,
                command=self._update_sg_order_display
            )

        # SNV
        self.snv_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(tools, text="SNV", variable=self.snv_var,
                       command=self.on_snv_toggle).pack(side=tk.LEFT, padx=(2, 10))

        ttk.Separator(tools, orient="vertical").pack(side=tk.LEFT, fill=tk.Y, padx=8)

        # Save/Export buttons
        ttk.Button(tools, text="Save Meta", command=self.on_save_meta_only).pack(side=tk.LEFT, padx=(2, 6))
        ttk.Button(tools, text="Save PNG", command=self.on_save_figure).pack(side=tk.LEFT, padx=(2, 6))
        ttk.Button(tools, text="Export CSV", command=self.on_export_csv_spectra_only).pack(side=tk.LEFT, padx=(0, 0))

    def _build_plot_range_controls(self) -> None:
        """Build plot range sliders."""
        pr = ttk.Frame(self.right)
        pr.pack(fill=tk.X, padx=6, pady=(2, 4))
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

    def _build_points_panel(self) -> None:
        """Build collapsible points/polygons list panel."""
        bar = ttk.Frame(self.right)
        bar.pack(fill=tk.X, padx=6, pady=(4, 0))
        
        self._pts_frame = ttk.LabelFrame(self.right, text="Points (current image)")
        self._pts_btn = ttk.Button(bar, text="Show points list", command=self._toggle_points_panel)
        self._pts_btn.pack(side=tk.LEFT)
        
        ttk.Checkbutton(bar, text="Polygon Avg", variable=self.poly_mode,
                        command=self._on_poly_mode_toggle).pack(side=tk.LEFT, padx=(10, 0))
        
        # Status message label
        self.status_label = ttk.Label(bar, textvariable=self.status_var, 
                                       foreground="blue", font=("", 9, "italic"))
        self.status_label.pack(side=tk.RIGHT, padx=(10, 0))

        # Treeview
        cols = ("id", "label", "view", "x", "y", "source")
        self.tree = ttk.Treeview(self._pts_frame, columns=cols, show="headings", height=4)
        for c, w in zip(cols, (70, 160, 60, 70, 70, 220)):
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
        
        # Bind events
        self.tree.bind("<Button-1>", self._on_tree_click_view_toggle, add="+")
        self.tree.bind("<Double-1>", self._on_tree_double_click_inline)
        self.tree.bind("<F2>", lambda e: self._edit_selected_label_inline())

    def _build_spectra_viewer(self) -> None:
        """Build spectra plot viewer."""
        viewer_spec = ttk.Frame(self.right)
        viewer_spec.pack(fill=tk.BOTH, expand=True, padx=6, pady=(6, 0))
        self._viewer_spec = viewer_spec
        
        self.spec_fig = Figure(figsize=(6, 6), dpi=FIG_DPI)
        self.ax_spec = self.spec_fig.add_subplot(111)
        self._style_spec_axes()
        
        self.spec_canvas = FigureCanvasTkAgg(self.spec_fig, master=viewer_spec)
        tb = CustomNavigationToolbar(self.spec_canvas, viewer_spec, app_instance=self, pack_toolbar=False)
        tb.update()
        tb.pack(side=tk.BOTTOM, fill=tk.X, pady=2)
        self.spec_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

    # =========================================================================
    # HOTKEY SETUP
    # =========================================================================
    def _setup_hotkeys(self) -> None:
        """Setup global hotkeys."""
        def _busy_in_entry() -> bool:
            fg = self.focus_get()
            return isinstance(fg, (tk.Entry, ttk.Entry))

        # v: Toggle all visibility
        self.bind_all("v", lambda e: not _busy_in_entry() and self._toggle_all_visibility())
        self.bind_all("V", lambda e: not _busy_in_entry() and self._toggle_all_visibility())

        # m: Toggle mode
        def _toggle_mode():
            if _busy_in_entry(): return
            cur = self.mode_var.get()
            self.mode_var.set("Absorbance" if cur == "Reflectance" else "Reflectance")
            self.on_mode_change()
        self.bind_all("m", lambda e: _toggle_mode())
        self.bind_all("M", lambda e: _toggle_mode())

        # 1/2/3: Toggle preprocessing
        self.bind_all("1", lambda e: self._toggle_bool_if_not_busy(self.noise_var, self.on_noise_toggle, _busy_in_entry))
        self.bind_all("2", lambda e: self._toggle_bool_if_not_busy(self.smooth_var, self.on_smooth_toggle, _busy_in_entry))
        self.bind_all("3", lambda e: self._toggle_bool_if_not_busy(self.snv_var, self.on_snv_toggle, _busy_in_entry))

        # 4/5/6/7: Save/Export actions
        self.bind_all("4", lambda e: not _busy_in_entry() and self.on_save_meta_only())
        self.bind_all("5", lambda e: not _busy_in_entry() and self.on_save_figure())
        self.bind_all("6", lambda e: not _busy_in_entry() and self.on_export_csv_spectra_only())
        self.bind_all("7", lambda e: not _busy_in_entry() and self.reset_spectra())

        # h: Toggle points panel
        self.bind_all("h", lambda e: not _busy_in_entry() and self._toggle_points_panel())
        self.bind_all("H", lambda e: not _busy_in_entry() and self._toggle_points_panel())

        # i: Toggle polygon mode
        def _toggle_poly():
            if _busy_in_entry(): return
            self.poly_mode.set(not self.poly_mode.get())
            self._on_poly_mode_toggle()
        self.bind_all("i", lambda e: _toggle_poly())
        self.bind_all("I", lambda e: _toggle_poly())

        # l/o: Load/Open
        self.bind_all("l", lambda e: not _busy_in_entry() and self.load_meta_json())
        self.bind_all("L", lambda e: not _busy_in_entry() and self.load_meta_json())
        self.bind_all("o", lambda e: not _busy_in_entry() and self.open_hdr())
        self.bind_all("O", lambda e: not _busy_in_entry() and self.open_hdr())

        # a: Cycle tabs
        self.bind_all("a", lambda e: not _busy_in_entry() and self._cycle_tab())
        self.bind_all("A", lambda e: not _busy_in_entry() and self._cycle_tab())

        # q: Cancel
        self.bind_all("q", lambda e: not _busy_in_entry() and self._cancel_current_ui())
        self.bind_all("Q", lambda e: not _busy_in_entry() and self._cancel_current_ui())

        # w: Toggle fullscreen
        self.bind_all("w", lambda e: not _busy_in_entry() and self._toggle_fullscreen())
        self.bind_all("W", lambda e: not _busy_in_entry() and self._toggle_fullscreen())

    def _toggle_bool_if_not_busy(self, var: tk.BooleanVar, callback, busy_check) -> None:
        """Toggle boolean variable if not busy."""
        if busy_check():
            return
        var.set(not var.get())
        callback()

    # =========================================================================
    # Window helpers
    # =========================================================================
    def center_window(self, w=None, h=None, m=16):
        try:
            self.update_idletasks()
            w = int(w or max(self.winfo_width(), 1))
            h = int(h or max(self.winfo_height(), 1))
            sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
            x, y = (sw - w) // 2, (sh - h) // 2
            x = max(m, min(x, sw - w - m)); y = max(m, min(y, sh - h - m))
            self.geometry(f"{w}x{h}+{x}+{y}")
        except Exception:
            pass

    # =========================================================================
    # DATA LOADING
    # =========================================================================
    def open_hdr(self) -> None:
        """Open HDR file dialog."""
        path = filedialog.askopenfilename(
            title="Select HDR file",
            filetypes=[("ENVI header", "*.hdr")]
        )
        if path:
            self._load_hdr_from_path(path)

    def _load_hdr_from_path(self, path: str) -> bool:
        """Load HSI from path and update UI. Returns True on success."""
        if not path or not os.path.isfile(path) or not path.lower().endswith(".hdr"):
            return False
        
        # Show loading status
        self._set_status("Loading HDR file...")
        abs_path = os.path.abspath(path)
        self._hsi_cache.pop(abs_path, None) # 既存キャッシュを削除して再読み込み
        
        try:
            img = spectral.open_image(path)
            data = img.open_memmap(writable=False)  # ← メモリマップで遅延読み込み
        except Exception as e:
            self._clear_status()
            messagebox.showerror("Load error", str(e))
            return False

        if data.ndim == 2:
            data = data[:, :, None]
        if data.dtype == np.float64:
            data = data.astype(np.float32, copy=False)  # メモリ使用量半減
        self.img = img
        self.data = data
        self.path_var.set(os.path.abspath(path))

        # Extract wavelengths
        try:
            wl_meta = img.metadata.get("wavelength", None)
            wl = self.to_float_array(wl_meta) if wl_meta is not None else np.arange(data.shape[2], dtype=float)
        except Exception:
            wl = np.arange(data.shape[2], dtype=float)
        self.wavelengths = wl
        # 波長数に応じて窓サイズを自動設定（初回のみ）
        if not hasattr(self, '_filter_params_set'):
            B = wl.size
            if B >= 1000: self.med_window, self.sg_window = 21, 51
            elif B >= 200: self.med_window, self.sg_window = 7, 15
            else:
                self.med_window = max(3, min(7, B // 10) | 1)
                self.sg_window = max(3, min(11, B // 5) | 1)
            self._filter_params_set = True
        # Set initial bands
        self.gray_band = min(10, data.shape[2] - 1)
        B = data.shape[2]
        self.rgb_bands = {
            "R": int(B * 0.8),
            "G": int(B * 0.5),
            "B": int(B * 0.2)
        }

        # Configure sliders
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
        self._clear_all_caches()
        
        # Show completion status
        H, W, B = data.shape
        self._set_status(f"Loaded: {W}×{H}×{B} ({os.path.basename(path)})", duration_ms=3000)
        
        return True

    @staticmethod
    def to_float_array(x: Any) -> np.ndarray:
        """Convert various formats to float array."""
        try:
            return np.array(x, dtype=float)
        except Exception:
            return np.array([float(str(v).strip().replace(",", "")) for v in x])

    def _wl_resolution(self) -> float:
        """Calculate wavelength resolution from current data."""
        wl = self.wavelengths
        if wl is None or wl.size < 2:
            return 1.0
        diffs = np.diff(wl.astype(float))
        diffs = diffs[np.isfinite(diffs)]
        res = float(np.median(np.abs(diffs))) if diffs.size else 1.0
        return res if np.isfinite(res) and res > 0 else 1.0

    # =========================================================================
    # IMAGE RENDERING
    # =========================================================================
    def _update_gray_image(self) -> None:
        """Update gray image display."""
        if self.data is None or self.wavelengths is None:
            return
        
        ax = self.ax_gray
        view = self._capture_view_if_meaningful(ax, "gray")
        
        b = int(np.clip(self.gray_band, 0, self.data.shape[2] - 1))
        wl = float(self.wavelengths[b])
        
        ax.cla()
        ax.set_title(f"Gray — λ={wl:.1f} nm (Band {b})")
        ax.set_xticks([])
        ax.set_yticks([])
        # Horizontally flip image for correct orientation
        # Replace NaN with 0 for display (minimal change to keep downstream logic)
        img_band = self.data[:, :, b]
        img_band = np.nan_to_num(img_band, nan=0.0)
        ax.imshow(np.fliplr(img_band), cmap=self.cmap_name.get(), zorder=0)
        
        self._draw_markers(ax)
        self._draw_polygons(ax)
        
        if view is not None:
            self._restore_view(ax, view)
        
        self.gray_canvas.draw_idle()
        self._view_forced_reset_gray = False

    def _update_rgb_image(self) -> None:
        """Update pseudo RGB image display."""
        if self.data is None or self.wavelengths is None:
            return
        
        ax = self.ax_rgb
        view = self._capture_view_if_meaningful(ax, "rgb")
        
        R = self.rgb_bands["R"]
        G = self.rgb_bands["G"]
        Bn = self.rgb_bands["B"]
        
        ax.cla()
        ax.set_xticks([])
        ax.set_yticks([])
        
        if None in (R, G, Bn):
            ax.set_title("Pseudo RGB (select R/G/B)")
        else:
            R = int(np.clip(R, 0, self.data.shape[2] - 1))
            G = int(np.clip(G, 0, self.data.shape[2] - 1))
            Bn = int(np.clip(Bn, 0, self.data.shape[2] - 1))
            
            wlR = float(self.wavelengths[R])
            wlG = float(self.wavelengths[G])
            wlB = float(self.wavelengths[Bn])
            
            rgb = np.dstack([
                self.stretch01(self.data[:, :, R]),
                self.stretch01(self.data[:, :, G]),
                self.stretch01(self.data[:, :, Bn])
            ])
            # Replace NaN with 0 for display (minimal change)
            rgb = np.nan_to_num(rgb, nan=0.0)
            
            ax.set_title(f"Pseudo RGB — λ: {wlR:.1f}/{wlG:.1f}/{wlB:.1f} nm\n(Bands: {R}/{G}/{Bn})")
            # Horizontally flip RGB image for correct orientation
            ax.imshow(np.fliplr(rgb), zorder=0)
        
        self._draw_markers(ax)
        self._draw_polygons(ax)
        
        if view is not None:
            self._restore_view(ax, view)
        
        self.rgb_canvas.draw_idle()
        self._view_forced_reset_rgb = False

    @staticmethod
    def stretch01(img: np.ndarray, low: int = PERCENTILE_LOW, high: int = PERCENTILE_HIGH) -> np.ndarray:
        """Stretch image to 0-1 range using percentiles."""
        v1, v2 = np.nanpercentile(img, [low, high])
        if v2 - v1 == 0:
            return np.zeros_like(img, dtype=float)
        return np.clip((img - v1) / (v2 - v1), 0, 1)

    def _update_gray_label(self) -> None:
        """Update gray image wavelength label."""
        b = int(self.gray_band)
        wl = float(self.wavelengths[b]) if self.wavelengths is not None else float(b)
        self.gray_sel_var.set(f"λ={wl:.1f} nm (Band {b})")

    def _update_rgb_labels(self) -> None:
        """Update RGB wavelength labels."""
        def format_label(key: str) -> str:
            b = self.rgb_bands[key]
            wl = float(self.wavelengths[b]) if self.wavelengths is not None else float(b)
            return f"λ={wl:.1f} nm (Band {b})"
        
        self.r_label.set(f"R: {format_label('R')}")
        self.g_label.set(f"G: {format_label('G')}")
        self.b_label.set(f"B: {format_label('B')}")

    # =========================================================================
    # MARKER AND POLYGON DRAWING
    # =========================================================================
    def _draw_markers(self, ax) -> None:
        """Draw point markers on axis."""
        cur_src = self.path_var.get()
        # Get image width for coordinate transformation
        W = self.data.shape[1] if self.data is not None else 1
        
        for p in self.points:
            if not self._same_source(p.get("source", ""), cur_src):
                continue
            if not p.get("visible", True):
                continue
            # Transform x coordinate from data space to display space
            x_display = flip_x_for_display(p["x"], W)
            ax.plot(x_display, p["y"], marker='+', color=p["color"],
                    markersize=10, markeredgewidth=1.8, zorder=3, clip_on=True)

    def _draw_polygons(self, ax) -> None:
        """Draw polygons on axis."""
        cur_src = self.path_var.get()
        # Get image width for coordinate transformation
        W = self.data.shape[1] if self.data is not None else 1
        
        # Draw finalized polygons
        for pg in self.polygons:
            if not self._same_source(pg.get("source", ""), cur_src):
                continue
            if not pg.get("visible", True):
                continue
            
            vs = pg.get("verts") or []
            if not vs:
                continue
            
            # Transform vertices from data space to display space
            vs_display = [(flip_x_for_display(x, W), y) for x, y in vs]
            xs, ys = zip(*vs_display)
            if len(vs) >= 2:
                ax.plot(xs + (xs[0],), ys + (ys[0],), lw=1.5, linestyle='-',
                        color=pg["color"], zorder=5, clip_on=True)
            
            for (vx, vy) in vs_display:
                ax.plot(vx, vy, marker='o', markersize=5.5, markerfacecolor='none',
                        markeredgewidth=1.4, markeredgecolor=pg["color"], zorder=6, clip_on=True)

        # Draw temporary polygon being drawn
        if self.poly_mode.get() and self._poly_temp_verts and (ax is self._poly_drawing_axes):
            # Transform temporary vertices to display space
            temp_display = [(flip_x_for_display(x, W), y) for x, y in self._poly_temp_verts]
            xs, ys = zip(*temp_display)
            if len(xs) >= 2:
                ax.plot(xs, ys, lw=1.0, linestyle='--', color='k', zorder=7, clip_on=True)
            for (vx, vy) in temp_display:
                ax.plot(vx, vy, marker='o', markersize=6.0, markerfacecolor='none',
                        markeredgewidth=1.2, markeredgecolor='k', zorder=8, clip_on=True)

    # =========================================================================
    # SLIDER AND TAB HANDLERS
    # =========================================================================
    def _set_sliders_state(self, state: str) -> None:
        """Enable/disable sliders."""
        self.gray_scale.configure(state=state)
        for sc in (self.r_scale, self.g_scale, self.b_scale):
            sc.configure(state=state)

    def _nearest_band(self, wl_value: float) -> int:
        """Find nearest band index for given wavelength."""
        dif = np.abs(self.wavelengths - wl_value)
        return int(np.argmin(dif))

    def on_gray_scale(self, val: str) -> None:
        """Handle gray scale slider change."""
        if self.data is None or self._snapping:
            return
        
        self._snapping = True
        try:
            idx = self._nearest_band(float(val))
            self.gray_band = idx
            self.gray_scale_var.set(float(self.wavelengths[idx]))
            self._update_gray_label()
            self._update_gray_image()
        finally:
            self._snapping = False

    def on_rgb_scale(self, _=None) -> None:
        """Handle RGB scale slider change."""
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
        """Handle notebook tab change."""
        if self.data is None:
            return
        
        nb = event.widget
        tab = nb.nametowidget(nb.select())
        
        if tab is self.tab_gray:
            self._update_gray_image()
        elif tab is self.tab_rgb:
            self._update_rgb_image()

    # =========================================================================
    # SPECTRAL PLOT MANAGEMENT
    # =========================================================================
    def _style_spec_axes(self) -> None:
        """Style spectra axes."""
        # Build title with processing info
        title = "Spectra"
        processing_tags = []
        
        if getattr(self, "noise_var", None) and self.noise_var.get():
            processing_tags.append("Denoise")
        if getattr(self, "smooth_var", None) and self.smooth_var.get():
            deriv = self.sg_deriv_var.get()
            processing_tags.append(f"SG ({deriv})")
        if getattr(self, "snv_var", None) and self.snv_var.get():
            processing_tags.append("SNV")
        
        if processing_tags:
            title += f" ({', '.join(processing_tags)})"
        
        self.ax_spec.set_title(title)
        self.ax_spec.set_xlabel("Wavelength [nm]")
        mode = self.mode_var.get()
        sg_on = getattr(self, "smooth_var", None) and self.smooth_var.get()
        sg_order = self.sg_deriv_var.get() if hasattr(self, "sg_deriv_var") else "0th"
        snv_on = getattr(self, "snv_var", None) and self.snv_var.get()
        # 軸ラベル生成
        if sg_on:
            if sg_order == "1st":
                base = f"d({mode})/dλ"
            elif sg_order == "2nd":
                # 2次微分はピークの符号が逆になるため、比較しやすいように符号を反転して表示
                base = f"-d²({mode})/dλ²"
            else:
                base = mode
        else:
            base = mode
        if snv_on:
            ylab = f"SNV({base})"
        else:
            ylab = base
        ylab += " [A.U.]"  # 単位を追加
        self.ax_spec.set_ylabel(ylab)
        self.ax_spec.grid(True)
        self.ax_spec.xaxis.set_minor_locator(AutoMinorLocator())
        self.ax_spec.yaxis.set_minor_locator(AutoMinorLocator())
        self.ax_spec.grid(which='minor', linestyle=':', linewidth=0.5, alpha=0.6)

    def on_plot_range_change(self, *_) -> None:
        """Handle plot range slider change."""
        self._update_plot_range_label()
        self._debounce("plot_redraw", self._redraw_spec_lines, delay_ms=100)

    def _update_plot_range_label(self) -> None:
        """Update plot range label."""
        if self.wavelengths is None or self.wavelengths.size == 0:
            self.plot_rng_label.set("(-)")
            return
        
        lo = float(self.plot_min_var.get())
        hi = float(self.plot_max_var.get())
        if hi < lo:
            lo, hi = hi, lo
        self.plot_rng_label.set(f"{lo:.1f} — {hi:.1f}")

    def _current_plot_slice_and_bounds(self) -> Tuple[slice, Optional[int], Optional[int]]:
        """Get current plot range as slice and bounds."""
        if self.wavelengths is None or self.wavelengths.size == 0:
            return slice(None), None, None
        
        lo = float(self.plot_min_var.get())
        hi = float(self.plot_max_var.get())
        if hi < lo:
            lo, hi = hi, lo
        
        i_lo = self._nearest_band(lo)
        i_hi = self._nearest_band(hi)
        if i_hi < i_lo:
            i_lo, i_hi = i_hi, i_lo
        
        return slice(i_lo, i_hi + 1), i_lo, i_hi

    def _redraw_spec_lines(self) -> None:
        """Redraw all spectral lines."""
        # Show status for large dataset processing
        total_items = len(self.points) + len(self.polygons)
        if total_items > 5:
            self._set_status(f"Redrawing {total_items} spectra...")
        
        ax = self.ax_spec
        ax.cla()
        self._style_spec_axes()
        
        s, i_lo, i_hi = self._current_plot_slice_and_bounds()
        if i_lo is None:
            self.spec_canvas.draw_idle()
            self._clear_status()
            return

        line_count = 0
        
        # Draw points
        for p in self.points:
            if not p.get("visible", True):
                continue
            
            wl_plot, y_plot = self._get_point_proc_slice(p, i_lo, i_hi)
            if wl_plot is None:
                continue
            
            ax.plot(wl_plot, y_plot, marker='o', lw=1.5, markersize=2.5,
                    color=p["color"], label=self._legend_for_point(p))
            line_count += 1

        # Draw polygons
        for i, pg in enumerate(self.polygons):
            if not pg.get("visible", True):
                continue
            
            res = self._get_polygon_proc_slice_stats(pg, i_lo, i_hi)
            if not res:
                continue
            
            wl_plot, y_mean, y_std, N = res
            base_label = pg.get("label") or f"pg{i+1:04d}"
            
            src = str(pg.get("source", ""))
            cur = str(self.path_var.get())
            if src and (src != cur):
                base_label += f" @{os.path.basename(src)}"
            
            ax.plot(wl_plot, y_mean, lw=2.0, linestyle='-', color=pg["color"], label=base_label)
            
            try:
                ax.fill_between(wl_plot, y_mean - y_std, y_mean + y_std,
                                alpha=0.25, linewidth=0, facecolor=pg["color"])
            except Exception:
                pass
            
            line_count += 1

        if line_count > 0:
            ax.legend(loc='best')
        
        self.spec_canvas.draw_idle()
        
        # Clear status after redraw
        if total_items > 5:
            self._set_status("Ready", duration_ms=500)

    def _legend_for_point(self, p: Dict[str, Any]) -> str:
        """Generate legend text for point."""
        base = p["label"] if p["label"] else f'({p["x"]},{p["y"]})'
        src = p.get("source", "")
        cur = self.path_var.get()
        
        if src and (not self._same_source(src, cur)):
            base += f" @{os.path.basename(src)}"
        
        return base

    # =========================================================================
    # CLICK HANDLERS
    # =========================================================================
    def on_image_click(self, event) -> None:
        """Handle image click event."""
        if self.data is None:
            return
        if event.inaxes not in (self.ax_gray, self.ax_rgb):
            return
        if event.xdata is None or event.ydata is None:
            return
        if self._toolbar_busy(event.inaxes):
            return

        # Transform click coordinates from display space to data space
        H, W, _ = self.data.shape
        x_display = event.xdata
        y = int(round(event.ydata))
        x = int(round(flip_x_from_display(x_display, W)))
        
        if not (0 <= x < W and 0 <= y < H):
            return

        # Handle polygon mode
        if self.poly_mode.get():
            self._handle_polygon_click(event, x, y)
            return

        # Handle point mode
        if getattr(event, "button", None) == 3:
            self._delete_marker_near(x, y)
            return

        self._add_point(x, y, event.inaxes)

    def _handle_polygon_click(self, event, x: int, y: int) -> None:
        """Handle click in polygon drawing mode."""
        if self._poly_drawing_axes is None:
            self._poly_drawing_axes = event.inaxes
            self._poly_temp_verts = []
        
        if event.inaxes is not self._poly_drawing_axes:
            return
        
        # Right click: remove last vertex or delete polygon
        if getattr(event, "button", None) == 3:
            if self._poly_temp_verts:
                self._poly_temp_verts.pop()
                if event.inaxes is self.ax_gray:
                    self._update_gray_image()
                else:
                    self._update_rgb_image()
                return
            
            if self._delete_polygon_near(x, y):
                if self._pts_visible:
                    self._refresh_points_view()
                return
            return
        
        # Add vertex
        self._poly_temp_verts.append((x, y))
        
        # Double click: finalize polygon
        if getattr(event, "dblclick", False) and len(self._poly_temp_verts) >= 3:
            pg = {
                "verts": tuple(self._poly_temp_verts),
                "color": self._next_polygon_color(),
                "label": "",
                "source": self.path_var.get(),
                "visible": True
            }
            self.polygons.append(pg)
            self._poly_temp_verts = []
            self._poly_drawing_axes = None
            
            self._redraw_spec_lines()
            self._update_gray_image()
            self._update_rgb_image()
            self.spec_canvas.draw_idle()
            self.spec_canvas.flush_events()
            
            if self._pts_visible:
                self._refresh_points_view(select_last=True)
            return
        
        # Update display
        if event.inaxes is self.ax_gray:
            self._update_gray_image()
        else:
            self._update_rgb_image()

    def _add_point(self, x: int, y: int, axes) -> None:
        """Add new point and update display."""
        color = self._next_point_color()
        p = {
            "x": x,
            "y": y,
            "color": color,
            "label": "",
            "source": self.path_var.get(),
            "visible": True
        }
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

        axes.plot(x, y, marker='+', color=color, markersize=10, markeredgewidth=1.8,
                  zorder=3, clip_on=True)
        
        if axes is self.ax_gray:
            self._update_gray_image()
        else:
            self._update_rgb_image()
        
        if self._pts_visible:
            self._refresh_points_view(select_last=True)

    # =========================================================================
    # SPECTRAL PROCESSING
    # =========================================================================
    def on_mode_change(self) -> None:
        """Handle mode change (Reflectance/Absorbance)."""
        self._set_status("Recalculating spectra...")
        self._pt_proc_cache.clear()
        self._poly_proc_cache.clear()
        self._style_spec_axes()
        self._redraw_spec_lines()
        self._set_status("Ready", duration_ms=1000)

    def on_noise_toggle(self, *_) -> None:
        """Handle denoise toggle."""
        self._set_status("Applying denoise...")
        self._pt_proc_cache.clear()
        self._poly_proc_cache.clear()
        self._redraw_spec_lines()
        self._set_status("Ready", duration_ms=1000)

    def _update_sg_order_display(self) -> None:
        """Update SG order button display and reprocess spectra."""
        order = self.sg_deriv_var.get()
        self.sg_order_btn.configure(text=f"▼ {order}")
        self.on_smooth_toggle()

    def on_smooth_toggle(self, *_) -> None:
        """Handle smoothing toggle."""
        self._set_status("Applying smoothing...")
        self._pt_proc_cache.clear()
        self._poly_proc_cache.clear()
        self._redraw_spec_lines()
        self._set_status("Ready", duration_ms=1000)

    def on_snv_toggle(self, *_) -> None:
        """Handle SNV toggle."""
        self._set_status("Applying SNV...")
        self._pt_proc_cache.clear()
        self._poly_proc_cache.clear()
        self._redraw_spec_lines()
        self._set_status("Ready", duration_ms=1000)

    def _apply_mode(self, y: np.ndarray) -> np.ndarray:
        """Apply Reflectance/Absorbance conversion."""
        y = np.asarray(y, dtype=np.float32)
        mode = self.mode_var.get()
        
        if mode == "Reflectance":
            return y
        
        if mode == "Absorbance":
            # Auto-detect scale: if max > 1.5, assume 16-bit scale
            maxv = float(np.nanmax(y)) if y.size else 0.0
            if np.isfinite(maxv) and maxv > 1.5:
                R = y * (1.0 / 65535.0)
            else:
                R = y
            
            R = np.clip(R, 1e-8, 1.0)
            A = -np.log10(R)
            return A.astype(np.float32, copy=False)
        
        return y

    def _process_spectrum(self, y: np.ndarray) -> np.ndarray:
        """Apply preprocessing to spectrum."""
        y2 = np.asarray(y, dtype=np.float32, order="C")
        
        if getattr(self, "noise_var", None) and self.noise_var.get():
            y2 = self._apply_denoise(y2)
        
        if getattr(self, "smooth_var", None) and self.smooth_var.get():
            y2 = self._apply_smoothing(y2)
        
        if getattr(self, "snv_var", None) and self.snv_var.get():
            y2 = self._apply_snv(y2)
        
        return np.asarray(y2, dtype=np.float32, order="C", copy=False)

    def _apply_denoise(self, y: np.ndarray) -> np.ndarray:
        """Apply median filter denoising."""
        n = len(y)
        k = self._safe_window_length(n, base=self.med_window, min_win=MED_MIN_WIN)
        if k is None:
            return y
        try:
            return medfilt(y, kernel_size=k)
        except Exception:
            return y

    def _apply_smoothing(self, y: np.ndarray) -> np.ndarray:
        """Apply Savitzky-Golay smoothing."""
        try:
            n = len(y)
            poly = SG_POLYORDER
            win = self._safe_window_length(n, base=self.sg_window, min_win=SG_MIN_WIN)
            
            if win is None:
                return y
            
            if win <= poly:
                win = poly + 3
                if win % 2 == 0:
                    win += 1
            
            # 微分次数の取得と適用
            deriv_map = {"0th": 0, "1st": 1, "2nd": 2}
            deriv = deriv_map.get(self.sg_deriv_var.get(), 0)
            
            res = savgol_filter(y, window_length=win, polyorder=poly, 
                               deriv=deriv, mode="interp")
            # 2次微分は表示のため符号を反転して返す
            if deriv == 2:
                try:
                    res = -res
                except Exception:
                    pass
            return res
        except Exception:
            # Fallback to simple moving average (derivatives not supported)
            n = len(y)
            k = self._safe_window_length(n, base=7, min_win=3)
            if k is None:
                return y
            return np.convolve(y, np.ones(k) / k, mode="same")

    def _apply_snv(self, y: np.ndarray) -> np.ndarray:
        """Apply Standard Normal Variate normalization."""
        m = np.nanmean(y)
        s = np.nanstd(y)
        
        if not np.isfinite(s) or s == 0:
            return y - m
        
        return (y - m) / s

    @staticmethod
    def _safe_window_length(n: int, base: int = 5, min_win: int = 3) -> Optional[int]:
        """Calculate safe window length for filtering."""
        if n < min_win:
            return None
        
        k = base if n >= base else (n | 1)
        k = max(min_win, k)
        
        return k if k <= n else None

    def _proc_flags(self) -> Tuple[str, bool, bool, bool]:
        """Get current processing flags."""
        return (
            self.mode_var.get(),
            bool(self.noise_var.get()),
            bool(self.smooth_var.get()),
            bool(self.snv_var.get())
        )

    # =========================================================================
    # CACHE MANAGEMENT
    # =========================================================================
    def _get_point_proc_slice(self, p: Dict[str, Any], i_lo: int, i_hi: int) -> Tuple[Optional[np.ndarray], Optional[np.ndarray]]:
        """Get processed spectrum slice for point with caching."""
        src = str(p.get("source", ""))
        key_raw = (src, int(p["x"]), int(p["y"]))
        
        # Get or load raw spectrum
        y_full = self._pt_raw_cache.get(key_raw)
        if y_full is None:
            if self._same_source(src, self.path_var.get()):
                y_full = np.asarray(self.data[int(p["y"]), int(p["x"]), :]).squeeze().astype(float)
            else:
                d, _ = self._get_hsi_for_source(src)
                if d is None:
                    return None, None
                y_full = d[int(p["y"]), int(p["x"]), :].astype(float)
            self._pt_raw_cache[key_raw] = y_full

        # Check processed cache
        flags = self._proc_flags()
        key_proc = key_raw + (flags, int(i_lo), int(i_hi))
        y_proc = self._pt_proc_cache.get(key_proc)
        
        if y_proc is None:
            y_slice = y_full[i_lo:i_hi + 1].astype(np.float32, copy=False)
            y_disp = self._apply_mode(y_slice)
            y_proc = self._process_spectrum(y_disp)
            self._pt_proc_cache[key_proc] = y_proc

        wl_slice = self.wavelengths[i_lo:i_hi + 1]
        return wl_slice, y_proc

    def _get_polygon_proc_slice_stats(self, pg: Dict[str, Any], i_lo: int, i_hi: int) -> Optional[Tuple[np.ndarray, np.ndarray, np.ndarray, int]]:
        """Get processed polygon statistics with caching."""
        src = str(pg.get("source", ""))
        
        if self._same_source(src, self.path_var.get()):
            d, wl = self.data, self.wavelengths
        else:
            d, wl = self._get_hsi_for_source(src)
        
        if d is None or wl is None or wl.size == 0:
            return None

        k_base = (src, self._normalize_verts(pg.get("verts") or []))
        flags = self._proc_flags()
        key = k_base + (flags, int(i_lo), int(i_hi))
        
        cached = self._poly_proc_cache.get(key)
        if cached is not None:
            return cached

        idx = self._get_polygon_idx(pg, d)
        if idx.size == 0:
            return None
        
        H, W, B = d.shape
        s = slice(i_lo, i_hi + 1)
        D = d.reshape(-1, B)[idx][:, s].astype(np.float32, copy=False)

        # Process each pixel
        def _proc(y):
            return self._process_spectrum(self._apply_mode(y))
        
        try:
            Y = np.apply_along_axis(_proc, 1, D)
        except Exception:
            Y = np.vstack([_proc(row) for row in D])

        mean = np.nanmean(Y, axis=0)
        std = np.nanstd(Y, axis=0, ddof=0)
        out = (self.wavelengths[s], mean, std, idx.size)
        self._poly_proc_cache[key] = out
        return out

    def _get_polygon_idx(self, pg: Dict[str, Any], d: np.ndarray) -> np.ndarray:
        """Get pixel indices inside polygon with caching."""
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

    def _polygon_key(self, pg: Dict[str, Any]) -> Tuple[str, Tuple[Tuple[int, int], ...]]:
        """Generate cache key for polygon."""
        src = str(pg.get("source", ""))
        verts = tuple((int(x), int(y)) for x, y in (pg.get("verts") or []))
        return (src, verts)

    def _get_hsi_for_source(self, src_path: str) -> Tuple[Optional[np.ndarray], Optional[np.ndarray]]:
        """Load HSI data from source path with caching."""
        if not src_path:
            return None, None
        
        src_path = self._norm_path(src_path)
        
        if src_path in self._hsi_cache:
            return self._hsi_cache[src_path]
        
        if not os.path.isfile(src_path) or (not src_path.lower().endswith(".hdr")):
            self._hsi_cache[src_path] = (None, None)
            return None, None
        
        try:
            img = spectral.open_image(src_path)
            data = np.asarray(img.load())
            
            if data.ndim == 2:
                data = data[:, :, None]
            
            wl_meta = img.metadata.get("wavelength", None)
            wl = self.to_float_array(wl_meta) if wl_meta is not None else np.arange(data.shape[2], dtype=float)
            
            self._hsi_cache[src_path] = (data, wl)
            return data, wl
        except Exception:
            self._hsi_cache[src_path] = (None, None)
            return None, None

    def _clear_all_caches(self) -> None:
        """Clear all caches."""
        self._pt_raw_cache.clear()
        self._pt_proc_cache.clear()
        self._poly_idx_cache.clear()
        self._poly_proc_cache.clear()

    def _invalidate_point_cache(self, src: str, x: int, y: int) -> None:
        """Invalidate cache for specific point."""
        key_raw = (str(src), int(x), int(y))
        self._pt_raw_cache.pop(key_raw, None)
        
        to_del = [k for k in self._pt_proc_cache.keys()
                  if isinstance(k, tuple) and len(k) >= 3 and k[0:3] == key_raw]
        for k in to_del:
            self._pt_proc_cache.pop(k, None)

    def _invalidate_polygon_cache(self, src: str, verts: Sequence[Tuple[int, int]]) -> None:
        """Invalidate cache for specific polygon."""
        key_base = (str(src), self._normalize_verts(verts))
        self._poly_idx_cache.pop(key_base, None)
        
        to_del = [k for k in self._poly_proc_cache.keys()
                  if isinstance(k, tuple) and len(k) >= 3 and k[0:2] == key_base]
        for k in to_del:
            self._poly_proc_cache.pop(k, None)

    # =========================================================================
    # DELETION AND RESET
    # =========================================================================
    def on_delete_last_marker(self, *_) -> None:
        """Delete last added marker."""
        if not self.points:
            return
        
        p = self.points.pop()
        self._invalidate_point_cache(p.get("source", self.path_var.get()), int(p["x"]), int(p["y"]))
        self._redraw_spec_lines()
        self._update_gray_image()
        self._update_rgb_image()
        
        if self._pts_visible:
            self._refresh_points_view()

    def reset_spectra(self) -> None:
        """Reset all spectra and markers."""
        self._clear_all_caches()
        
        self.ax_spec.cla()
        self._style_spec_axes()
        self.spec_canvas.draw()
        
        self.points.clear()
        self.polygons.clear()
        self._poly_temp_verts = []
        self._poly_drawing_axes = None
        
        self._pt_color_idx = 0
        self._pg_color_idx = 0
        
        self._update_gray_image()
        self._update_rgb_image()
        
        if self._pts_visible:
            self._refresh_points_view()

    def _delete_marker_near(self, x: int, y: int, radius: Optional[int] = None) -> bool:
        """Delete marker near click position."""
        radius = radius or DELETE_RADIUS_PX
        
        if not self.points:
            return False
        
        pts = np.array([(p["x"], p["y"]) for p in self.points])
        d = np.sqrt((pts[:, 0] - x) ** 2 + (pts[:, 1] - y) ** 2)
        i = int(np.argmin(d))
        
        if d[i] <= radius:
            p = self.points.pop(i)
            self._redraw_spec_lines()
            self._invalidate_point_cache(p.get("source", self.path_var.get()), int(p["x"]), int(p["y"]))
            self._update_gray_image()
            self._update_rgb_image()
            
            if self._pts_visible:
                self._refresh_points_view()
            
            return True
        
        return False

    def _delete_polygon_near(self, x: int, y: int, radius: Optional[int] = None) -> bool:
        """Delete polygon near click position."""
        if not self.polygons:
            return False
        
        rad = radius if radius is not None else DELETE_RADIUS_PX
        rad2 = rad * 1.5

        def _pt_seg_dist(px, py, x1, y1, x2, y2):
            vx, vy = x2 - x1, y2 - y1
            wx, wy = px - x1, py - y1
            denom = vx * vx + vy * vy
            
            if denom <= 1e-12:
                dx, dy = px - x1, py - y1
                return (dx * dx + dy * dy) ** 0.5
            
            t = max(0.0, min(1.0, (wx * vx + wy * vy) / denom))
            nx, ny = x1 + t * vx, y1 + t * vy
            dx, dy = px - nx, py - ny
            return (dx * dx + dy * dy) ** 0.5

        # Check if click is inside polygon
        for i, pg in enumerate(self.polygons):
            vs = pg.get("verts") or []
            if len(vs) < 3:
                continue
            
            if Path(vs).contains_point((x, y)):
                pg = self.polygons.pop(i)
                self._invalidate_polygon_cache(pg.get("source", self.path_var.get()), pg.get("verts", []))
                self._redraw_spec_lines()
                self._update_gray_image()
                self._update_rgb_image()
                return True

        # Check if click is near vertices
        for i, pg in enumerate(self.polygons):
            vs = pg.get("verts") or []
            if len(vs) < 3:
                continue
            
            for (vx, vy) in vs:
                if (vx - x) ** 2 + (vy - y) ** 2 <= rad * rad:
                    pg = self.polygons.pop(i)
                    self._invalidate_polygon_cache(pg.get("source", self.path_var.get()), pg.get("verts", []))
                    self._redraw_spec_lines()
                    self._update_gray_image()
                    self._update_rgb_image()
                    return True
            
            # Check if click is near edges
            for (x1, y1), (x2, y2) in zip(vs, vs[1:] + vs[:1]):
                if _pt_seg_dist(x, y, x1, y1, x2, y2) <= rad2:
                    pg = self.polygons.pop(i)
                    self._invalidate_polygon_cache(pg.get("source", self.path_var.get()), pg.get("verts", []))
                    self._redraw_spec_lines()
                    self._update_gray_image()
                    self._update_rgb_image()
                    return True
        
        return False

    # =========================================================================
    # COLOR MANAGEMENT
    # =========================================================================
    def _next_point_color(self):
        """Get next color for point."""
        c = self._palette10[self._pt_color_idx % 10]
        self._pt_color_idx = (self._pt_color_idx + 1) % 10
        return c

    def _next_polygon_color(self):
        """Get next color for polygon."""
        c = self._palette10[self._pg_color_idx % 10]
        self._pg_color_idx = (self._pg_color_idx + 1) % 10
        return c

    # =========================================================================
    # POINTS LIST MANAGEMENT (TREEVIEW)
    # =========================================================================
    def _toggle_points_panel(self) -> None:
        """Toggle points list panel visibility."""
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
        """Refresh points list display."""
        for item in self.tree.get_children():
            self.tree.delete(item)
        
        # Add points
        for i, p in enumerate(self.points):
            pid = f"sp{i+1:04d}"
            src = str(p.get("source", "")) if p.get("source", "") is not None else ""
            base = os.path.basename(src) if src else "-"
            
            if src and not self._source_exists(src):
                base = f"{base} [MISSING]"
            
            view_txt = "✓" if p.get("visible", True) else ""
            self.tree.insert("", "end", iid=pid,
                             values=(pid, p["label"], view_txt, p["x"], p["y"], base))
        
        # Add polygons
        for j, pg in enumerate(self.polygons):
            iid = f"pg{j+1:04d}"
            vs = pg.get("verts") or []
            
            if len(vs) >= 1:
                cx = int(round(sum(v[0] for v in vs) / len(vs)))
                cy = int(round(sum(v[1] for v in vs) / len(vs)))
            else:
                cx, cy = "", ""
            
            src = str(pg.get("source", "")) if pg.get("source", "") is not None else ""
            base = os.path.basename(src) if src else "-"
            
            if src and not self._source_exists(src):
                base = f"{base} [MISSING]"
            
            view_txt = "✓" if pg.get("visible", True) else ""
            self.tree.insert("", "end", iid=iid, values=(iid, pg.get("label", ""), view_txt, cx, cy, base))

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

    def _on_tree_click_view_toggle(self, event) -> None:
        """Handle click on VIEW column to toggle visibility."""
        iid = self.tree.identify_row(event.y)
        col = self.tree.identify_column(event.x)
        
        if not iid or col != "#3":
            return

        if iid.startswith("sp"):
            try:
                idx = int(iid[2:]) - 1
            except Exception:
                return
            
            if 0 <= idx < len(self.points):
                self.points[idx]["visible"] = not bool(self.points[idx].get("visible", True))
        elif iid.startswith("pg"):
            try:
                idx = int(iid[2:]) - 1
            except Exception:
                return
            
            if 0 <= idx < len(self.polygons):
                self.polygons[idx]["visible"] = not bool(self.polygons[idx].get("visible", True))
        else:
            return

        self._refresh_points_view()
        self._redraw_spec_lines()
        self._update_gray_image()
        self._update_rgb_image()

    def _on_tree_double_click_inline(self, event) -> None:
        """Handle double-click on LABEL column for inline editing."""
        iid = self.tree.identify_row(event.y)
        col = self.tree.identify_column(event.x)
        
        if not iid or col != "#2":
            return
        
        self._start_inline_edit_label(iid)

    def _edit_selected_label_inline(self) -> None:
        """Start inline editing for selected row."""
        sel = self.tree.selection()
        if not sel:
            return
        
        iid = sel[0]
        self._start_inline_edit_label(iid)

    def _start_inline_edit_label(self, iid: str) -> None:
        """Start inline label editing for tree item."""
        try:
            x, y, w, h = self.tree.bbox(iid, column="#2")
        except Exception:
            return
        
        if w <= 0 or h <= 0:
            return

        # Get current label
        if iid.startswith("sp"):
            try:
                idx = int(iid[2:]) - 1
            except Exception:
                return
            
            if not (0 <= idx < len(self.points)):
                return
            cur_label = str(self.points[idx].get("label", ""))
        elif iid.startswith("pg"):
            try:
                idx = int(iid[2:]) - 1
            except Exception:
                return
            
            if not (0 <= idx < len(self.polygons)):
                return
            cur_label = str(self.polygons[idx].get("label", ""))
        else:
            return

        # Close existing editor
        if hasattr(self, "_tv_inline_entry") and self._tv_inline_entry is not None:
            try:
                self._tv_inline_entry.destroy()
            except Exception:
                pass
            self._tv_inline_entry = None

        # Create inline entry
        e = ttk.Entry(self.tree)
        e.insert(0, cur_label)
        e.select_range(0, tk.END)
        e.focus_set()
        e.place(x=x, y=y, width=w, height=h)

        self._tv_inline_entry = e
        self._tv_inline_iid = iid

        def _commit(*_):
            # Check if entry still exists
            if not self._tv_inline_entry or not self._tv_inline_entry.winfo_exists():
                self._tv_inline_entry = None
                self._tv_inline_iid = None
                return
            
            try:
                new_label = self._tv_inline_entry.get().strip()
            except Exception:
                # Entry already destroyed
                self._tv_inline_entry = None
                self._tv_inline_iid = None
                return
            
            if self._tv_inline_iid and self._tv_inline_iid.startswith("sp"):
                try:
                    i = int(self._tv_inline_iid[2:]) - 1
                except Exception:
                    i = -1
                if 0 <= i < len(self.points):
                    self.points[i]["label"] = new_label
            elif self._tv_inline_iid and self._tv_inline_iid.startswith("pg"):
                try:
                    i = int(self._tv_inline_iid[2:]) - 1
                except Exception:
                    i = -1
                if 0 <= i < len(self.polygons):
                    self.polygons[i]["label"] = new_label
            
            try:
                if self._tv_inline_entry and self._tv_inline_entry.winfo_exists():
                    self._tv_inline_entry.destroy()
            except Exception:
                pass
            
            self._tv_inline_entry = None
            self._tv_inline_iid = None
            self._refresh_points_view()
            self._redraw_spec_lines()

        def _cancel(*_):
            try:
                if self._tv_inline_entry and self._tv_inline_entry.winfo_exists():
                    self._tv_inline_entry.destroy()
            except Exception:
                pass
            self._tv_inline_entry = None
            self._tv_inline_iid = None

        e.bind("<Return>", _commit)
        e.bind("<KP_Enter>", _commit)
        e.bind("<Escape>", _cancel)
        e.bind("<FocusOut>", _commit)

        self.tree.bind("<<TreeviewSelect>>", lambda _ev: _commit(), add="+")
        self.tree.bind("<Configure>", lambda _ev: _commit(), add="+")
        self.tree.bind("<MouseWheel>", lambda _ev: _commit(), add="+")

    def _get_selected_index(self) -> Optional[Tuple[str, int]]:
        """Get selected item type and index."""
        sel = self.tree.selection()
        if not sel:
            return None
        
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
        """Delete selected item from list."""
        sel = self._get_selected_index()
        if sel is None:
            return
        
        kind, idx = sel
        
        if kind == "point":
            p = self.points.pop(idx)
            self._invalidate_point_cache(p.get("source", self.path_var.get()), int(p["x"]), int(p["y"]))
        elif kind == "poly":
            pg = self.polygons.pop(idx)
            self._invalidate_polygon_cache(pg.get("source", self.path_var.get()), pg.get("verts", []))
        
        self._redraw_spec_lines()
        self._update_gray_image()
        self._update_rgb_image()
        self._refresh_points_view()

    def _rename_selected(self) -> None:
        """Open rename dialog for selected item."""
        # Replace modal rename dialog: start inline edit like double-click
        sel = self.tree.selection()
        if not sel:
            return
        iid = sel[0]
        # Start the same inline editor used on double-click
        self._start_inline_edit_label(iid)

    # =========================================================================
    # POLYGON MODE
    # =========================================================================
    def _on_poly_mode_toggle(self) -> None:
        """Handle polygon mode toggle."""
        if not self.poly_mode.get():
            self._poly_temp_verts = []
            self._poly_drawing_axes = None
        
        self._update_gray_image()
        self._update_rgb_image()

    # =========================================================================
    # EXPORT AND SAVE
    # =========================================================================
    def on_export_csv_spectra_only(self) -> None:
        """Export spectra to CSV."""
        if (self.data is None and not self.points and not self.polygons) or not (self.points or self.polygons):
            messagebox.showinfo("Export CSV", "No spectra to export.")
            return

        path = filedialog.asksaveasfilename(
            title="Save spectra CSV",
            defaultextension=".csv",
            filetypes=[("CSV", "*.csv")],
            initialfile="spectra_simple.csv"
        )
        
        if not path:
            return
        
        if not path.lower().endswith(".csv"):
            path += ".csv"
        
        if self.wavelengths is None or self.wavelengths.size == 0:
            messagebox.showerror("Export CSV", "Wavelengths are not available.")
            return

        wl = np.asarray(self.wavelengths).ravel()
        cols: List[np.ndarray] = []
        ids: List[str] = []
        label_items: List[str] = []
        src_items: List[str] = []

        # Export points
        for i, p in enumerate(self.points):
            cols.append(self._get_raw_spectrum_on_master(p, wl))
            ids.append(f"sp{i+1:04d}")
            
            lbl = p.get("label") or f"({p.get('x')},{p.get('y')})"
            label_items.append(lbl)
            
            src_full = str(p.get("source", "")) if p.get("source", "") is not None else ""
            src_base = os.path.basename(src_full) if src_full else ""
            src_items.append(f"{src_base}@x={p.get('x','')};y={p.get('y','')}")

        # Export polygons
        for j, pg in enumerate(self.polygons):
            w_src, m_src, s_src, N = self._compute_polygon_raw_stats(pg)
            if w_src is None:
                continue
            
            m_out = np.interp(wl, w_src, m_src, left=np.nan, right=np.nan)
            s_out = np.interp(wl, w_src, s_src, left=np.nan, right=np.nan)
            
            cols.append(m_out)
            ids.append(f"pg{j+1:04d}_mean")
            cols.append(s_out)
            ids.append(f"pg{j+1:04d}_std")
            
            pg_label = pg.get("label") or f"pg{j+1:04d}"
            label_items.append(f"{pg_label} (mean)")
            label_items.append(f"{pg_label} (std)")
            
            src_full = str(pg.get("source", "")) if pg.get("source", "") is not None else ""
            src_base = os.path.basename(src_full) if src_full else ""
            src_items.append(src_base)
            src_items.append(src_base)

        M = np.column_stack(cols) if cols else np.empty((wl.shape[0], 0))
        self._write_csv_new(path, wl, ids, M, note_recomputed=True,
                            labels_list=label_items, sources_list=src_items)
        
        messagebox.showinfo("Export CSV", f"Saved (spectra only): {os.path.basename(path)}")

    def _get_raw_spectrum_on_master(self, p: Dict[str, Any], wl_master: np.ndarray) -> np.ndarray:
        """Get raw spectrum interpolated to master wavelength grid."""
        wl_master = np.asarray(wl_master).reshape(-1)
        B = wl_master.shape[0]
        
        if self.data is None or self.wavelengths is None or B == 0:
            return np.full((B,), np.nan, dtype=float)

        cur_src = str(self.path_var.get())
        src = str(p.get("source", "")) if p.get("source", "") is not None else ""

        if src == cur_src:
            H, W, _ = self.data.shape
            x0 = int(np.clip(p["x"], 0, W - 1))
            y0 = int(np.clip(p["y"], 0, H - 1))
            return np.asarray(self.data[y0, x0, :]).astype(float).reshape(-1)

        d, wl_src = self._get_hsi_for_source(src)
        if d is None or wl_src is None or wl_src.size == 0:
            return np.full((B,), np.nan, dtype=float)

        Hs, Ws, _ = d.shape
        x0 = int(np.clip(p["x"], 0, Ws - 1))
        y0 = int(np.clip(p["y"], 0, Hs - 1))
        y_src = np.asarray(d[y0, x0, :]).astype(float).reshape(-1)

        wl_src = np.asarray(wl_src, dtype=float).reshape(-1)
        order = np.argsort(wl_src)
        wl_sorted = wl_src[order]
        y_sorted = y_src[order]
        
        uniq_wl, idx_start = np.unique(wl_sorted, return_index=True)
        y_uniq = y_sorted[idx_start]
        
        y_out = np.interp(wl_master, uniq_wl, y_uniq, left=np.nan, right=np.nan)
        return y_out

    def _compute_polygon_raw_stats(self, pg: Dict[str, Any]) -> Tuple[Optional[np.ndarray], Optional[np.ndarray], Optional[np.ndarray], int]:
        """Compute raw statistics for polygon."""
        src = str(pg.get("source", ""))
        
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
        
        if len(vs) < 3:
            return None, None, None, 0
        
        yy, xx = np.mgrid[0:H, 0:W]
        pts = np.column_stack([xx.ravel(), yy.ravel()])
        mask = Path(vs).contains_points(pts).reshape(H, W)
        idx = np.flatnonzero(mask)
        
        if idx.size == 0:
            return None, None, None, 0
        
        D = d.reshape(-1, B)[idx].astype(float, copy=False)
        m = np.nanmean(D, axis=0)
        s = np.nanstd(D, axis=0, ddof=0)
        
        return np.asarray(wl).astype(float), m, s, idx.size

    @staticmethod
    def _safe_float(v: Any) -> float:
        """Safely convert to float."""
        try:
            return float(v)
        except Exception:
            return float("nan")

    def _write_csv_new(self, path: str, wl: np.ndarray, ids: List[str], M: np.ndarray,
                       note_recomputed: bool = False,
                       labels_list: Optional[List[str]] = None,
                       sources_list: Optional[List[str]] = None) -> None:
        """Write CSV file with headers and data."""
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

    def on_save_meta_only(self) -> None:
        """Save metadata JSON only."""
        default_name = "spectra_meta.json"
        path = filedialog.asksaveasfilename(
            title="Save Meta JSON",
            defaultextension=".json",
            filetypes=[("JSON", "*.json")],
            initialfile=default_name
        )
        
        if not path:
            return

        meta: Dict[str, Any] = {
            "version": "1.0",
            "processing": {
                "mode": self.mode_var.get(),
                "denoise_median": bool(self.noise_var.get()),
                "smooth_savgol": bool(self.smooth_var.get()),
                "sg_order": self.sg_deriv_var.get(),
                "snv": bool(self.snv_var.get()),
                "median_window": int(self.med_window),
                "sg_window": int(self.sg_window),
            },
            "plot_range": {},
            "spectra": [],
            "polygons": []
        }

        try:
            lo = float(self.plot_min_var.get())
            hi = float(self.plot_max_var.get())
            if hi < lo:
                lo, hi = hi, lo
            meta["plot_range"] = {"wl_min": lo, "wl_max": hi}
        except Exception:
            pass

        # Save points
        for i, p in enumerate(self.points):
            src_full = str(p.get("source", "")) if p.get("source", "") is not None else ""
            meta["spectra"].append({
                "id": f"sp{i+1:04d}",
                "label": str(p.get("label", "")),
                "visible": bool(p.get("visible", True)),
                "source": {
                    "path_full": src_full,
                    "path_basename": os.path.basename(src_full) if src_full else "",
                    "coords": {"x": int(p["x"]), "y": int(p["y"])}
                }
            })

        # Save polygons
        for j, pg in enumerate(self.polygons):
            src_full = str(pg.get("source", "")) if pg.get("source", "") is not None else ""
            vs = [[int(x), int(y)] for (x, y) in (pg.get("verts") or [])]
            
            try:
                _, _, _, N = self._compute_polygon_raw_stats(pg)
            except Exception:
                N = 0
            
            meta["polygons"].append({
                "id": f"pg{j+1:04d}",
                "label": str(pg.get("label", "")),
                "visible": bool(pg.get("visible", True)),
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

    def on_save_figure(self) -> None:
        """Save current figure as PNG."""
        if self.data is None:
            messagebox.showinfo("Save PNG", "No image loaded.")
            return
        
        base = filedialog.asksaveasfilename(
            title="Save PNG base name",
            defaultextension=".png",
            filetypes=[("PNG", "*.png")],
            initialfile="figure.png"
        )
        
        if not base:
            return
        
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

    # =========================================================================
    # META JSON LOADING
    # =========================================================================
    def load_meta_json(self) -> None:
        """Load metadata from JSON file."""
        skipped_points = 0
        skipped_polygons = 0
        missing_sources = set()
        
        path = filedialog.askopenfilename(
            title="Load meta JSON",
            filetypes=[("JSON", "*.json")]
        )
        
        if not path:
            return
        
        # Show loading status
        self._set_status("Loading meta JSON...")
        
        try:
            with open(path, "r", encoding="utf-8") as f:
                meta = json.load(f)
        except Exception as e:
            self._clear_status()
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
        
        # Get existing point/polygon maps
        pt_exact, pt_by_xy = self._existing_point_maps()
        pg_exact, pg_by_shape = self._existing_poly_maps()
        
        # Track items in current JSON to avoid self-duplicates
        seen_pts_in_meta = set()
        seen_polys_in_meta = set()

        def _coerce_xy(v):
            try:
                return int(v)
            except Exception:
                return None

        # Load points
        for sid, info in items:
            if not isinstance(info, dict):
                continue

            src_path = info.get("source_path")
            if src_path is None:
                src = info.get("source", {})
                if isinstance(src, dict):
                    src_path = src.get("path_full") or src.get("path") or src.get("path_basename")
                    coords = src.get("coords", {})
                    x = info.get("x", _coerce_xy(coords.get("x")))
                    y = info.get("y", _coerce_xy(coords.get("y")))
                else:
                    x = info.get("x")
                    y = info.get("y")
            else:
                x = info.get("x")
                y = info.get("y")

            x = _coerce_xy(x)
            y = _coerce_xy(y)
            
            if x is None or y is None:
                continue

            if src_path:
                sp = str(src_path)
                if not os.path.isabs(sp):
                    cand = os.path.join(json_dir, sp)
                    if os.path.isfile(cand):
                        sp = cand
                
                if not os.path.isfile(sp) and sp.lower().endswith(".hdr"):
                    cand = os.path.join(json_dir, os.path.basename(sp))
                    if os.path.isfile(cand):
                        sp = cand
                
                src_path = sp

            label = info.get("label") or info.get("name") or info.get("id") or sid
            src_path = str(src_path) if src_path is not None else ""
            visible = bool(info.get("visible", True))

            if src_path and src_path.lower().endswith(".hdr") and os.path.isfile(src_path):
                hdr_candidates.append(src_path)

            # Check for duplicates
            label = str(label)
            kxy = self._point_key(src_path, x, y)
            k_exact = (kxy, label)
            
            if (k_exact in pt_exact) or (k_exact in seen_pts_in_meta):
                skipped_points += 1
            else:
                if (kxy in pt_by_xy) or (kxy in {k for (k, _) in pt_exact}):
                    current_lbl = pt_by_xy.get(kxy, "")
                    for p0 in self.points:
                        if self._point_key(p0.get("source", ""), p0.get("x", 0), p0.get("y", 0)) == kxy:
                            if (not current_lbl) and label:
                                p0["label"] = label
                            p0["visible"] = visible
                            break
                    skipped_points += 1
                else:
                    pending_points.append({
                        "x": x, "y": y, "color": None,
                        "label": label, "source": src_path,
                        "visible": visible,
                    })
                    seen_pts_in_meta.add(k_exact)
                    seen_pts_in_meta.add(kxy)
            
            if src_path and src_path.lower().endswith(".hdr") and (not os.path.isfile(src_path)):
                missing_sources.add(os.path.basename(str(src_path)))

        # Load processing settings
        proc = meta.get("processing", {})
        mode = proc.get("mode")
        if mode in ("Reflectance", "Absorbance"):
            self.mode_var.set(mode)
        
        if "denoise_median" in proc:
            self.noise_var.set(bool(proc["denoise_median"]))
        if "smooth_savgol" in proc:
            self.smooth_var.set(bool(proc["smooth_savgol"]))
        if "sg_order" in proc and proc["sg_order"] in ["0th", "1st", "2nd"]:
            self.sg_deriv_var.set(proc["sg_order"])
            self._update_sg_order_display()  # メニューボタンの表示を更新
        if "snv" in proc:
            self.snv_var.set(bool(proc["snv"]))
        if "median_window" in proc:
            self.med_window = int(proc["median_window"])
        if "sg_window" in proc:
            self.sg_window = int(proc["sg_window"])

        # Load polygons
        polys_meta = meta.get("polygons", [])
        polys_iter = polys_meta.values() if isinstance(polys_meta, dict) else polys_meta

        def _resolve_src_path(spath: str) -> str:
            if not spath:
                return ""
            
            sp = str(spath)
            if not os.path.isabs(sp):
                cand = os.path.join(json_dir, sp)
                if os.path.isfile(cand):
                    sp = cand
            
            if not os.path.isfile(sp) and sp.lower().endswith(".hdr"):
                base = os.path.basename(sp)
                cand1 = os.path.join(json_dir, base)
                if os.path.isfile(cand1):
                    return cand1
                
                parent = os.path.dirname(json_dir)
                cand2 = os.path.join(parent, base)
                if os.path.isfile(cand2):
                    return cand2
            
            return sp

        loaded_polys = 0
        for item in polys_iter:
            if not isinstance(item, dict):
                continue
            
            verts = item.get("vertices") or item.get("verts") or []
            if not verts or len(verts) < 3:
                continue
            
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
            visible = bool(item.get("visible", True))
            
            # Check for duplicates
            canon = self._canon_poly(vs)
            kshape = (self._norm_src(src_path or self.path_var.get()), canon)
            k_exact = (kshape, str(label))
            
            if (k_exact in pg_exact) or (k_exact in seen_polys_in_meta):
                skipped_polygons += 1
            else:
                if (kshape in pg_by_shape) or (kshape in {k for (k, _) in pg_exact}):
                    current_lbl = pg_by_shape.get(kshape, "")
                    for pg in self.polygons:
                        if self._poly_key(pg.get("source", ""), pg.get("verts") or []) == kshape:
                            if (not current_lbl) and label:
                                pg["label"] = str(label)
                            pg["visible"] = visible
                            break
                    skipped_polygons += 1
                else:
                    pending_polygons.append({
                        "verts": vs, "color": None,
                        "label": str(label), "source": src_path or self.path_var.get(),
                        "visible": visible,
                    })
                    seen_polys_in_meta.add(k_exact)
                    seen_polys_in_meta.add(kshape)
            
            loaded_polys += 1
            
            if src_path and src_path.lower().endswith(".hdr") and (not os.path.isfile(src_path)):
                missing_sources.add(os.path.basename(str(src_path)))

        # Auto-load HDR if none loaded
        if self.data is None and hdr_candidates:
            for cand in hdr_candidates:
                if self._load_hdr_from_path(os.path.abspath(cand)):
                    try:
                        self._sync_plot_range_to(self.wavelengths)
                    except Exception:
                        pass
                    break

        # Add pending items
        if pending_points:
            self.points.extend(pending_points)
        if pending_polygons:
            self.polygons.extend(pending_polygons)
        
        # Reassign colors
        for i, p in enumerate(self.points):
            p["color"] = self._palette10[i % 10]
        for j, pg in enumerate(self.polygons):
            pg["color"] = self._palette10[j % 10]
        
        self._pt_color_idx = len(self.points) % 10
        self._pg_color_idx = len(self.polygons) % 10

        # Load plot range
        pr = meta.get("plot_range", {})
        if ("wl_min" in pr) and ("wl_max" in pr) and (self.wavelengths is not None) and (self.wavelengths.size > 0):
            lo = float(pr["wl_min"])
            hi = float(pr["wl_max"])
            wmin, wmax = float(self.wavelengths.min()), float(self.wavelengths.max())
            lo = max(wmin, min(wmax, min(lo, hi)))
            hi = max(wmin, min(wmax, max(lo, hi)))
            self.plot_min_var.set(lo)
            self.plot_max_var.set(hi)
            self._update_plot_range_label()

        # Update display
        self._redraw_spec_lines()
        if self.data is not None:
            self._update_gray_image()
            self._update_rgb_image()
        if self._pts_visible:
            self._refresh_points_view()

        # Build message
        lines = []
        if missing_sources:
            title = "Meta data loaded. (Missing source file(s))"
        elif skipped_points or skipped_polygons:
            title = "Meta data loaded. (Some entries skipped)"
        else:
            title = "Meta data loaded."
        
        lines.append(title)
        lines.append("")
        
        line_points = f"Points:   {len(pending_points)}"
        line_polygons = f"Polygons: {loaded_polys}"
        
        if skipped_points:
            line_points += f"  (skipped {skipped_points})"
        if skipped_polygons:
            line_polygons += f" (skipped {skipped_polygons})"
        
        lines.append(line_points)
        lines.append(line_polygons)
        
        if missing_sources:
            lines.append("")
            lines.append("Missing HDR:")
            listed = sorted(missing_sources)
            show = listed[:5]
            for f in show:
                lines.append(f" - {f}")
            if len(listed) > 5:
                lines.append(f"... (+{len(listed)-5})")

        msg = "\n".join(lines)
        
        # Clear status and show completion message
        self._set_status(f"Loaded: {len(pending_points)} points, {loaded_polys} polygons", duration_ms=3000)
        
        if missing_sources:
            messagebox.showwarning("Load meta JSON", msg)
        else:
            messagebox.showinfo("Load meta JSON", msg)

    def _sync_plot_range_to(self, wl: np.ndarray) -> None:
        """Sync plot range to wavelength array."""
        wl = np.asarray(wl).ravel()
        if wl.size:
            self.plot_min_var.set(float(np.nanmin(wl)))
            self.plot_max_var.set(float(np.nanmax(wl)))
            self._update_plot_range_label()

    # =========================================================================
    # HELPER METHODS
    # =========================================================================
    def _debounce(self, key: str, func, delay_ms: int = 1) -> None:
        """Debounce function call."""
        if not hasattr(self, "_debouncers"):
            self._debouncers: Dict[str, Any] = {}
        
        prev = self._debouncers.get(key)
        if prev:
            try:
                self.after_cancel(prev)
            except Exception:
                pass
        
        self._debouncers[key] = self.after(delay_ms, func)

    def _wrap_toolbar_home(self, toolbar, which: str) -> None:
        """Wrap toolbar home button to set forced reset flag."""
        if not hasattr(toolbar, "home"):
            return
        
        orig_home = toolbar.home
        
        def _home_wrapper(*args, **kwargs):
            if which == "gray":
                self._view_forced_reset_gray = True
            elif which == "rgb":
                self._view_forced_reset_rgb = True
            return orig_home(*args, **kwargs)
        
        toolbar.home = _home_wrapper

    def _capture_view(self, ax):
        """Capture current axis view."""
        try:
            return (ax.get_xlim(), ax.get_ylim())
        except Exception:
            return None

    def _restore_view(self, ax, view) -> None:
        """Restore axis view."""
        try:
            if view and isinstance(view, tuple) and len(view) == 2:
                ax.set_xlim(view[0])
                ax.set_ylim(view[1])
        except Exception:
            pass

    def _has_meaningful_view(self, ax) -> bool:
        """Check if axis has meaningful view (not default)."""
        try:
            xl = ax.get_xlim()
            yl = ax.get_ylim()
        except Exception:
            return False
        
        def _is01(t):
            return (abs(t[0] - 0.0) < 1e-9) and (abs(t[1] - 1.0) < 1e-9)
        
        if _is01(xl) and _is01(yl):
            return False
        
        w = abs(xl[1] - xl[0])
        h = abs(yl[1] - yl[0])
        if w <= 1.0 and h <= 1.0:
            return False
        
        return True

    def _capture_view_if_meaningful(self, ax, which: str):
        """Capture view if meaningful and not forced reset."""
        forced = (self._view_forced_reset_gray if which == "gray" else self._view_forced_reset_rgb)
        
        if not forced and self._has_meaningful_view(ax):
            return self._capture_view(ax)
        
        return None

    def _norm_path(self, p: Any) -> str:
        """Normalize path for comparison."""
        try:
            return os.path.normcase(os.path.normpath(os.path.abspath(str(p))))
        except Exception:
            return str(p) if p is not None else ""

    def _same_source(self, a: Any, b: Any) -> bool:
        """Check if two sources are the same."""
        return self._norm_path(a) == self._norm_path(b)

    def _source_exists(self, sp: str) -> bool:
        """Check if source file exists."""
        try:
            sp = str(sp or "")
            return bool(sp and os.path.isfile(sp) and sp.lower().endswith(".hdr"))
        except Exception:
            return False

    def _norm_src(self, sp: str) -> str:
        """Normalize source path."""
        try:
            return os.path.normcase(os.path.normpath(os.path.abspath(str(sp or ""))))
        except Exception:
            return str(sp or "")

    def _point_key(self, src: str, x: int, y: int) -> tuple:
        """Generate cache key for point."""
        return (self._norm_src(src), int(x), int(y))

    def _canon_poly(self, verts) -> tuple:
        """Canonicalize polygon vertices for comparison."""
        V = tuple((int(x), int(y)) for x, y in (verts or []))
        if len(V) < 3:
            return V
        
        rotations = [V[i:] + V[:i] for i in range(len(V))]
        rev = V[::-1]
        rotations += [rev[i:] + rev[:i] for i in range(len(rev))]
        
        return min(rotations)

    def _poly_key(self, src: str, verts) -> tuple:
        """Generate cache key for polygon."""
        return (self._norm_src(src), self._canon_poly(verts))

    def _normalize_verts(self, verts: Sequence[Tuple[int, int]]) -> Tuple[Tuple[int, int], ...]:
        """Normalize vertex list."""
        return tuple((int(x), int(y)) for (x, y) in verts or [])

    def _existing_point_maps(self):
        """Get existing point maps for duplicate detection."""
        exact = set()
        by_xy = dict()
        
        for p in self.points:
            src = p.get("source", "")
            kxy = self._point_key(src, p.get("x", 0), p.get("y", 0))
            lbl = str(p.get("label", ""))
            exact.add((kxy, lbl))
            by_xy[kxy] = lbl
        
        return exact, by_xy

    def _existing_poly_maps(self):
        """Get existing polygon maps for duplicate detection."""
        exact = set()
        by_shape = dict()
        
        for pg in self.polygons:
            src = pg.get("source", "")
            verts = pg.get("verts") or []
            k = self._poly_key(src, verts)
            lbl = str(pg.get("label", ""))
            exact.add((k, lbl))
            by_shape[k] = lbl
        
        return exact, by_shape

    def _toolbar_busy(self, ax) -> bool:
        """Check if toolbar is in pan/zoom mode."""
        tb = None
        canvas = None
        
        if ax is self.ax_gray:
            tb = getattr(self, "toolbar_gray", None)
            canvas = self.gray_fig.canvas
        elif ax is self.ax_rgb:
            tb = getattr(self, "toolbar_rgb", None)
            canvas = self.rgb_fig.canvas
        
        if tb is None:
            return False
        
        active = getattr(tb, "_active", None)
        if isinstance(active, str) and active in ("PAN", "ZOOM"):
            return True
        if hasattr(active, "name") and str(active.name).lower() in ("pan", "zoom"):
            return True
        
        mode = getattr(tb, "mode", "")
        if isinstance(mode, str) and mode.lower() in ("pan", "zoom", "pan/zoom"):
            return True
        
        wl = getattr(canvas, "widgetlock", None)
        return bool(wl and wl.locked())

    def _toggle_all_visibility(self) -> None:
        """Toggle visibility of all points/polygons."""
        # Check if any item is currently hidden
        any_hidden = any(not p.get("visible", True) for p in self.points)
        any_hidden = any_hidden or any(not pg.get("visible", True) for pg in self.polygons)
        
        # If any hidden, show all; otherwise hide all
        new_state = any_hidden
        
        for p in self.points:
            p["visible"] = new_state
        for pg in self.polygons:
            pg["visible"] = new_state
        
        self._refresh_points_view()
        self._redraw_spec_lines()
        self._update_gray_image()
        self._update_rgb_image()
        
        # Show status
        status_msg = "All items shown" if new_state else "All items hidden"
        self._set_status(status_msg, duration_ms=1500)

    def _cycle_tab(self, *_) -> None:
        """Cycle between Gray/RGB tabs."""
        try:
            idx = self.nb.index(self.nb.select())
            tabs = self.nb.tabs()
            if len(tabs) >= 2:
                next_idx = (idx + 1) % 2
                self.nb.select(tabs[next_idx])
        except Exception:
            pass

    def _cancel_current_ui(self) -> None:
        """Cancel current UI operations."""
        # Close inline editor
        e = getattr(self, "_tv_inline_entry", None)
        if e is not None:
            try:
                e.destroy()
            except Exception:
                pass
            self._tv_inline_entry = None
            self._tv_inline_iid = None

        # Cancel polygon drawing
        if self.poly_mode.get() and self._poly_temp_verts:
            self._poly_temp_verts = []
            self._poly_drawing_axes = None
            self._update_gray_image()
            self._update_rgb_image()

        # Close toplevel windows
        for w in self.winfo_children():
            try:
                if isinstance(w, tk.Toplevel):
                    w.destroy()
            except Exception:
                pass

    def _toggle_fullscreen(self) -> None:
        """Toggle fullscreen mode."""
        import platform
        is_windows = platform.system() == "Windows"
        
        if not self._is_full:
            if is_windows:
                try:
                    self._normal_geometry = self.geometry()
                    self.state('zoomed')
                except Exception:
                    self.attributes("-fullscreen", True)
            else:
                self._normal_geometry = self.geometry()
                self.attributes("-fullscreen", True)
            self._is_full = True
        else:
            if is_windows:
                try:
                    self.state('normal')
                    if hasattr(self, "_normal_geometry"):
                        self.geometry(self._normal_geometry)
                except Exception:
                    self.attributes("-fullscreen", False)
            else:
                self.attributes("-fullscreen", False)
                if hasattr(self, "_normal_geometry"):
                    self.geometry(self._normal_geometry)
            self._is_full = False

    # =========================================================================
    # STATUS MESSAGE MANAGEMENT
    # =========================================================================
    def _set_status(self, message: str, duration_ms: int = 0) -> None:
        """
        Set status message.
        
        Args:
            message: Status message to display
            duration_ms: Duration in milliseconds (0 = permanent until changed)
        """
        self.status_var.set(message)
        self.update_idletasks()  # Force immediate UI update
        
        # Cancel previous auto-clear timer
        if self._status_after_id is not None:
            try:
                self.after_cancel(self._status_after_id)
            except Exception:
                pass
            self._status_after_id = None
        
        # Set auto-clear timer if duration specified
        if duration_ms > 0:
            self._status_after_id = self.after(duration_ms, lambda: self._set_status("Ready"))
    
    def _clear_status(self) -> None:
        """Clear status message (set to Ready)."""
        self._set_status("Ready")


# =============================================================================
# ENTRY POINT
# =============================================================================
if __name__ == "__main__":
    HyperspecTk().mainloop()