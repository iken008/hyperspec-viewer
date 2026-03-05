# Hyperspectral Viewer

[日本語版はこちら](README_jp.md)

A desktop application for hyperspectral imaging data visualization and analysis.

## Features

- Interactive visualization of grayscale and pseudo-color RGB hyperspectral images
- Point and polygon-based spectral extraction
- Spectral preprocessing (median filter, Savitzky-Golay, SNV)
- Reflectance / Absorbance mode switching
- Band position lines overlay on spectra plot (Gray: black, RGB: R/G/B colors)
- Save / load project metadata as JSON (wavelength positions, colormap, active tab, band lines state)
- Export spectra to CSV
- Keyboard shortcuts for efficient workflow
- Help menu with keyboard shortcut reference (`F1`)

## Requirements

- Python 3.8+
- numpy, scipy, matplotlib, spectral

```bash
pip install numpy scipy matplotlib spectral
```

Note: tkinter is included with Python on Windows/macOS. On Linux: `sudo apt-get install python3-tk`

## Usage

```bash
python spectral_viewer.py
```

### Build as Standalone Executable

To create a standalone `.exe` application using PyInstaller:

```bash
pyinstaller .\src\spectral_viewer_v1.7.9.py --onefile --noconsole --icon=icon/original_mag_trsp.png
```

The built executable will be in the `dist/` directory.

### Quick Start

1. Press `O` to open an HDR file
2. Click on the image to extract point spectra
3. Enable polygon mode with `I` to analyze regions
4. Press `4` to save metadata, `5` to save images, `6` to export CSV

### Hotkeys

| Key | Function |
|-----|----------|
| `O` | Open HDR file |
| `L` | Load meta JSON |
| `4` | Save meta JSON |
| `5` | Save PNG |
| `6` | Export CSV |
| `7` | Reset spectra |
| `M` | Toggle Reflectance / Absorbance mode |
| `1` / `2` / `3` | Toggle Denoise / Smoothing / SNV |
| `A` | Cycle image tab (Gray / Pseudo RGB) |
| `T` | Cycle panel tab (Plot Range / Points List) |
| `I` | Toggle polygon draw mode |
| `V` | Toggle all visibility |
| `W` | Toggle fullscreen |
| `Q` | Cancel / close dialog |
| `F1` | Open keyboard shortcut reference |
| `BackSpace` / `Delete` | Delete last marker |
| `F2` | Rename selected item (Points List) |

## Meta JSON

The project state is saved as a JSON file and includes:

- Spectral preprocessing settings
- Plot range (X and Y axis)
- Gray image wavelength and colormap
- Pseudo-color RGB wavelengths
- Active image tab (Gray / Pseudo RGB)
- Band Lines toggle state
- Point and polygon annotations (coordinates, label names, visibility)

## Tips

### Comparing spectra from multiple samples

By loading meta JSON files from different samples sequentially, you can overlay spectra from multiple HDR sources on the same plot. Each meta file records the source HDR path alongside its annotations, so measurements from different samples can be compared side by side without re-opening each file manually.

## File Formats

**Input**: ENVI format (`.hdr` + binary data)

**Output**:
- Meta JSON (project state)
- CSV (spectral data)
- PNG (images)

## License

MIT License - Copyright (c) 2025 Kenya Iijima (iken008)

Based on the spectral viewer tutorial by KLV Co., Ltd.
https://www.klv.co.jp/corner/spectral-python-viewer.html

## Author

Kenya Iijima ([@iken008](https://github.com/iken008))
