# Hyperspectral Viewer

A desktop application for hyperspectral imaging data visualization and analysis.

## Features

- Interactive visualization of grayscale and RGB hyperspectral images
- Point and polygon-based spectral extraction
- Spectral preprocessing (median filter, Savitzky-Golay, SNV)
- Reflectance/Absorbance mode switching
- Save/load project metadata as JSON
- Export spectra to CSV
- Keyboard shortcuts for efficient workflow

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
pyinstaller .\src\spectral_viewer_v1.7.8.py --onefile --noconsole --icon=icon/original_mag_trsp.png
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
| `M` | Toggle Reflectance/Absorbance |
| `1`/`2`/`3` | Toggle Denoise/Smoothing/SNV |
| `4`/`5`/`6` | Save meta/images/CSV |
| `I` | Toggle polygon mode |
| `V` | Toggle all visibility |
| `H` | Show/hide points list |
| `A` | Switch Gray/RGB tabs |

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
