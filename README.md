# Sardanello Timer Optimizer

Sardanello is a Windows gaming timer optimizer and benchmark tool for measuring
and tuning system timer behavior under a controlled synthetic game-like CPU
load.

It measures `Sleep(1)` wake-up behavior using QPC
(`QueryPerformanceCounter`), searches for a stable timer resolution, generates
an HTML report with Chart.js graphs, and can apply the selected timer through a
lightweight background timer-service mode.

This repository includes a ready-to-run `Sardanello.exe` and the source code
used to build it.

> Note: Sardanello helps you measure and apply a stable timer value for your
> specific hardware. It may improve timing consistency on some systems, but it
> does not guarantee higher FPS, lower input latency, or better 1% lows in every
> game.

## Before Running The Benchmark

For the benchmark to find a useful timer value, your system should be as clean
as possible. Third-party programs can alter the system timer, overlays can add
rendering overhead, and background processes can create unpredictable CPU load.

Close these before testing:

- Timer utilities: `TimerResolution.exe`, `ISLC`, `TimerTool.exe`. Reset them to
  default before closing.
- Schedulers: `Process Lasso` and similar tools.
- Overlays: MSI Afterburner + RTSS, AMD Adrenalin / NVIDIA App overlays,
  Discord overlay, Steam overlay.
- Recording and streaming: OBS, Bandicam, Twitch Studio, Streamlabs.
- Browsers and background apps: Chrome, Edge, Firefox, torrent clients, RGB
  software, cloud sync tools, launchers with active downloads.

## What It Does

Sardanello includes a GUI and a console mode. The GUI supports English, Russian,
German, Turkish, Spanish, Brazilian Portuguese, and Hindi.

- Three-wave benchmark:
  - Wave 1: global sweep from `0.500 ms` to `1.000 ms`, step `0.005 ms`.
  - Wave 2: top-15 retest across 7 shuffled rounds.
  - Wave 3: neighborhood sweep around the Wave 2 winner, `+/-0.002 ms`, across
    5 shuffled rounds.
- Robust scoring:
  `score1 = 0.75 * robust_avg_miss + 0.25 * cv_penalty`.
  The slowest 2% wake-time outliers are trimmed to reduce random OS spikes.
- HTML report:
  creates `gaming_timer_analysis.html` with charts and detailed metrics.
- System tools:
  can create a Windows Restore Point, apply the bundled `Sardanello.pow` power
  plan, apply HPET / boot / CPU interval tweaks, and apply the found timer.
- Timer-service mode:
  can add a user-level startup entry so Sardanello can keep the selected timer
  active after reboot.

## Important Safety Notes

Sardanello is a low-level Windows utility. Some buttons intentionally change
system settings and require administrator rights.

Actions that may be performed:

- `bcdedit` timer-related boot settings.
- Registry edits for timer requests and power/system settings.
- Device configuration checks for HPET.
- Importing and activating a Windows power plan.
- Creating a System Restore point through Windows APIs.
- Adding a user-level startup entry for timer-service mode.
- Calling `NtSetTimerResolution` while timer-service mode is active.

Before changing system settings, create a restore point from inside the app or
manually in Windows. Use this software only if you understand that it modifies
local Windows configuration.

## Download / Run

1. Download this repository or the prebuilt `Sardanello.exe`.
2. Run `Sardanello.exe`.
3. Approve the Windows UAC prompt if you want to use system-changing actions.
4. Choose your language and follow the UI prompts.

Official prebuilt `Sardanello.exe` SHA256:

```text
6246423805E0372C5684A19E65C7C8DB03791C042F3352F4225414365EC72632
```

The public build is silent: it does not include movie sounds, copyrighted music,
meme GIFs, or other third-party media.

## Repository Layout

```text
.
|-- Sardanello.exe
|-- Sardanello.cpp
|-- resource.h
|-- resources.rc
|-- assets/
|   |-- Sardanello.ico
|   `-- Sardanello.pow
|-- LICENSE
`-- README.md
```

Generated files such as `resources.o`, `gaming_timer_analysis*.html`,
`optimal_timer.ini`, logs, and CSV dumps are not meant to be committed.

## Compile Manually

Requirements:

- Windows 10 or Windows 11.
- MSYS2 MinGW-w64 x86_64 toolchain.

Recommended MSYS2 packages:

```powershell
pacman -S --needed mingw-w64-x86_64-gcc mingw-w64-x86_64-binutils
```

Open PowerShell in the repository root and run:

```powershell
$env:PATH='C:\msys64\mingw64\bin;C:\msys64\usr\bin;' + $env:PATH
windres resources.rc -O coff -o resources.o
g++ -std=c++17 -O2 -pipe -static -s -static-libgcc -static-libstdc++ -mwindows `
    Sardanello.cpp resources.o -o Sardanello.exe `
    -lsetupapi -lcfgmgr32 -lPowrProf -lole32 -loleaut32 -lsrclient `
    -luuid -ladvapi32 -lntdll -luser32 -lgdi32 -lkernel32 -lshell32 -lws2_32
Remove-Item -Force resources.o
```

If MSYS2 is installed elsewhere, replace `C:\msys64\mingw64\bin` with your MinGW
path.

## Reverting Changes

The safest rollback path is the Windows System Restore point created by the app
before testing.

To manually remove the timer-service startup entry, open an elevated PowerShell
or Command Prompt and run:

```powershell
reg delete "HKCU\Software\Microsoft\Windows\CurrentVersion\Run" /v SardanelloTimer /f
```

Then reboot Windows.

For boot and device settings, manually review your `bcdedit` configuration,
Device Manager (`System Devices -> High Precision Event Timer`), and Windows
Power Options.

## Antivirus Notes

Some antivirus products may flag low-level optimization tools. Sardanello
requests administrator rights, modifies registry/power settings, uses `bcdedit`,
uses SetupAPI for HPET-related device checks, and can add a user-level startup
entry for timer-service mode. The source code is provided so users can inspect
the logic and build the executable themselves.

## License

This project is released under the MIT License. See [LICENSE](LICENSE).
