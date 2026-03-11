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
- Brightness calibration from raw scan data (`File > Calibrate...`)
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
python spectral_viewer_(version).py
```

### Build as Standalone Executable

To create a standalone `.exe` application using PyInstaller:

```bash
pyinstaller .\src\spectral_viewer_(version).py --onefile --noconsole --icon=icon/original_mag_trsp_64x64.ico
```

The built executable will be in the `dist/` directory.

### Quick Start

1. Press `O` to open an HDR file
2. Click on the image to extract point spectra
3. Enable polygon mode with `I` to analyze regions
4. Press `4` to save metadata, `5` to save images, `6` to export CSV

### Hotkeys

| Key                        | Function                                   |
| -------------------------- | ------------------------------------------ |
| `O`                      | Open HDR file                              |
| `L`                      | Load meta JSON                             |
| `4`                      | Save meta JSON                             |
| `5`                      | Save PNG                                   |
| `6`                      | Export CSV                                 |
| `7`                      | Reset spectra                              |
| `M`                      | Toggle Reflectance / Absorbance mode       |
| `1` / `2` / `3`      | Toggle Denoise / Smoothing / SNV           |
| `A`                      | Cycle image tab (Gray / Pseudo RGB)        |
| `T`                      | Cycle panel tab (Plot Range / Points List) |
| `I`                      | Toggle polygon draw mode                   |
| `V`                      | Toggle all visibility                      |
| `W`                      | Toggle fullscreen                          |
| `Q`                      | Cancel / close dialog                      |
| `F1`                     | Open keyboard shortcut reference           |
| `BackSpace` / `Delete` | Delete last marker                         |
| `F2`                     | Rename selected item (Points List)         |

## Meta JSON

All settings and annotations visible on screen are bundled together and saved as a single JSON file. The file includes:

- Spectral preprocessing settings
- Plot range (X and Y axis)
- Gray image wavelength and colormap
- Pseudo-color RGB wavelengths
- Active image tab (Gray / Pseudo RGB)
- Band Lines toggle state
- Point and polygon annotations (coordinates, label names, visibility)

## Calibration

`File > Calibrate...` converts a raw scan into a reflectance image using dark and white reference images.
By subtracting the dark reference, **dark current noise** from the sensor is removed.
Dividing by the white reference corrects for **non-uniform illumination** across the field of view.

### Formula

```
calibrated = (scan - dark) / (white × X - dark)
```

| Symbol    | Description                                         |
| --------- | --------------------------------------------------- |
| `scan`  | Raw hyperspectral scan (ENVI `.raw` + `.hdr`)   |
| `dark`  | Dark reference image (`dark.tif`)                 |
| `white` | White reference image (`white.tif`)               |
| `X`     | White reference correction factor (default:`1.2`) |

### Expected folder structure

```
project/
├── raw/
│   ├── scan.raw
│   └── scan.hdr
└── ref/
    ├── dark.tif
    └── white.tif
```

### Output

The calibrated file is saved alongside the input scan:

```
raw/scan_calibrated_x1.2.raw
raw/scan_calibrated_x1.2.hdr
```

Output values are `uint16` in the range `0–65535` (reflectance `0.0–1.0`).
Pixels where the white reference signal is too weak (`wd < 100`) or reflectance exceeds `1.1` are set to `0`.

### Settings

| Field       | Description                                                                                                  |
| ----------- | ------------------------------------------------------------------------------------------------------------ |
| Scan RAW    | Path to the raw scan file (`.raw`). Defaults to the currently open file.                                   |
| Ref folder  | Folder containing `dark.tif` and `white.tif`. Auto-detected by searching parent directories of the scan. |
| X           | White reference correction factor. Remembered across dialog opens.                                           |
| Chunk lines | Number of lines processed at once. Larger values are faster but use more memory.                             |

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
