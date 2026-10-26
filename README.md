<div align="center">

<p>
  <img width="1280" src="https://i.imgur.com/70O5ukL.png" alt="SudokuPro screenshot" />
</p>

<h1>SudokuPro</h1>

_A feature-rich Sudoku desktop app built with Python and PyQt5._

[![Platform](https://img.shields.io/badge/platform-Windows-0078D6?logo=windows&logoColor=white)](#requirements)
[![Python](https://img.shields.io/badge/python-3.10%2B-3776AB?logo=python&logoColor=white)](#requirements)
[![PyQt5](https://img.shields.io/badge/UI-PyQt5-41CD52?logo=qt&logoColor=white)](#requirements)
[![License](https://img.shields.io/badge/license-GPL--3.0--or--later-blue.svg)](#license)
[![Status](https://img.shields.io/badge/status-active--development-orange)](#overview)

</div>

## Overview

SudokuPro is a complete Sudoku experience built for people who want more than a basic puzzle board. It blends puzzle play, solving logic, training, and analysis into a desktop application with a polished interface and flexible game modes.

At its core, SudokuPro is a Sudoku game and puzzle engine. You can play standard 9x9 puzzles, explore alternate board sizes, use advanced solving hints, track statistics, save sessions, and learn the logic behind tougher techniques.

It is designed for:

- Casual players who want a strong, polished puzzle experience
- Serious solvers who want explanations and strategy guidance
- Learners who want to practice techniques and understand why a move works
- Players who enjoy custom rules, challenge modes, and replayable puzzle sessions

## What SudokuPro includes

SudokuPro is not just a single board with a keyboard. It includes a broader set of tools and features:

- Multiple board sizes: 6x6, 8x8, 9x9, and 10x10
- Standard Sudoku and Killer Sudoku variants
- Difficulty progression: Easy, Medium, Hard, and Expert
- Built-in hint engine for common and advanced solving techniques
- Tutorial and explanation system for logical solving methods
- Notes mode with automatic cleanup and candidate support
- Daily challenges and replayable session codes
- Save, load, autosave, and share/import functionality
- Statistics tracking for performance over time
- Customizable themes, palettes, and visual settings
- Keyboard-and-mouse controls for efficient play

## Why it stands out

SudokuPro goes beyond a simple game by combining play and learning:

- It explains how a puzzle can be solved logically
- It helps identify the technique behind a move or pattern
- It supports both fast solving and deeper study
- It can be used as a training tool, a challenge app, and a personal statistics tracker

This makes it useful for both entertainment and skill development.

## Features

- Multiple board sizes and variants
- Killer Sudoku mode
- Difficulty ratings and solving-technique context
- Logical hint engine covering singles, pairs, pointing pairs, box/line reduction, triples, X-Wing, Swordfish, Skyscraper, Y-Wing, and XY-Chain
- Notes mode with automatic note cleanup
- Built-in tutorial system
- Statistics dashboard with win rate, averages, mistakes, and filters
- Seed import/export for puzzle sharing and replay
- Autosave and manual save/load
- Built-in color themes and custom palettes
- Rich keyboard and mouse controls

## Requirements

- Python 3.10+
- [PyQt5](https://pypi.org/project/PyQt5/)

Install dependencies:

```bash
python -m pip install PyQt5
```

## Installation and running

Clone the project and launch it:

```bash
git clone https://github.com/JohnyCore/SudokuPro.git
cd SudokuPro
python -m pip install PyQt5
python main.py
```

You can also install the package in editable mode and run the console entry point:

```bash
python -m pip install -e .
sudoku-pro
```

## Controls

| Key / Action | Effect |
|---|---|
| `1-9` | Enter digits (smaller boards use their own max digit) |
| `0` / `A` | Enter 10 on 10x10 boards |
| `N` | Toggle notes mode |
| `Space` (hold) | Temporary notes mode |
| Arrows / `WASD` | Move selection |
| `Shift` + Arrows | Expand selection |
| `Backspace` / `Delete` / `E` | Clear selected cell(s) |
| Click / Drag | Select cells |
| `Ctrl` + Click | Multi-select toggle |
| Click the timer | Pause / resume |
| Click the seed | Copy current seed |

## Project status

SudokuPro is under active development. The project is feature-rich and continues to evolve with additional puzzle logic, UI improvements, and gameplay refinements.

## License

This project is released under the [GPL-3.0-or-later](https://www.gnu.org/licenses/gpl-3.0.html) license.

## Contributing

Contributions are welcome. If you find a bug, want to suggest an improvement, or want to help expand the puzzle logic and training features, feel free to open an issue or submit a pull request.

---

Note: SudokuPro is a personal, feature-heavy project that aims to make Sudoku more interactive and educational. It is meant to be both a playable game and a smart puzzle-solving companion.
