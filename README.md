# eh-patcher
<p align="center">
    <img src="icon.png" alt="eh-patcher_icon" width="250">
</p>
A Patcher for Project Ebonhold allowing Users to modify/patch their game with visuals and QoL patches/addons.

## Features

- grouped patch selection with optional dependencies and related patch selection
- automatic Ebonhold folder search with remembered target path
- install detection for active and manually present patches
- per-patch uninstall support
- support for direct file, `.zip`, and `.rar` patch sources
- cached patch downloads for faster reinstallations
- built-in GitHub update support for the published Windows executable
- Large Address Aware / 4 GB client flag support
- per-patch notices for compatibility and additional information
- multilingual UI support

## Included Patches

**Character Visuals**
- HD Creatures & Mounts
- HD Race & Class Models
- HD Armor, Weapons / Equipment
- HD Spells & Effects `Not all are newly styled`

**World Visuals**
- HD Environment
- HD Watertextures
- HD Trees

**Misc Visuals**
- New Character Select/Creation Screen
- Character Info and Spellbook `Not compatible with ElvUI`

**QoL Improvements**
- Extra Class & Race Combination (e.g. Night Elf Mage, Blood Elf Warrior...)
- Classic & TBC Maps
- Caverns & Mines Maps
    - Requires WDM & Astrolabe

### Development

Run locally:

```powershell
python app.py
```

## Info
This is a standalone .exe file; no installation is required.
For a faster and smoother user experience, EHPatcher saves your game location and downloaded patches within `%LOCALAPPDATA%\EHPatcher`.

### Releases

The application is distributed through GitHub.
https://github.com/SypherRed/eh-patcher/releases


#### Stuff
*Preview Image*
https://i.imgur.com/9bW2Xjq.png


**Virustotal**
https://www.virustotal.com/gui/file/ca10207063c684fdbda182350b1b87cf036a6015e81d96ac107edbec452ab0a3/detection
_Bkav Pro is known to falsely flag executables_
