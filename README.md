# Hyperspectral Viewer — Enhanced Edition

A Python-based hyperspectral visualization and analysis tool.

Originally inspired by the KLV tutorial viewer:
https://www.klv.co.jp/corner/spectral-python-viewer.html
The code has since been heavily extended into a standalone tool.

## ✨ Features (major enhancements)

- 📌 Pixel annotation & polygon selection
- 📊 Polygon mean / std shading & CSV export
- 🎚 Reflectance / Absorbance switching
- 🧼 Spectral preprocessing
  - Median denoise
  - Savitzky–Golay smoothing
  - SNV
- 🗂 Multiple .hdr sources & JSON meta round-trip
- 🚀 Fast band-limited processing & caching
- 🎨 Stable 10-color cycle & overlap-aware import
- ⌨️ Hotkeys for fast analysis
- 🔁 State persistence & reproducible workflows

## 🖥 Requirements

- Python 3.9+
- Required libraries:
  ```bash
  pip install numpy scipy spectral matplotlib pillow
  ```

## ▶️ Usage

```bash
python spectral_viewer.py
```

### Hotkeys

| Key | Action                       |
| --- | ---------------------------- |
| r   | Reflectance mode             |
| a   | Absorbance mode              |
| i   | Point / Polygon input toggle |
| 1   | Noise removal                |
| 2   | Smoothing                    |
| 3   | SNV                          |
| d   | Clear all annotations        |

## 📁 Meta JSON Format

Stores:

- Points / polygons
- Labels
- Source .hdr paths
- Processing settings
- Plot wavelength range

## 👤 Author

**iken008 (Kenya Iijima)**
Tokyo University of Science — Takemura Lab

## 🔖 Credits & Attribution

This software originated from learning with the KLV tutorial viewer.
Original tutorial concept © KLV Co., Ltd.
Modifications & extensions © 2025 iken008 — MIT License

## 📄 License

MIT (for extended functionality by iken008)
See `LICENSE` for details.
