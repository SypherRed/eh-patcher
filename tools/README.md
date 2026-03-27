# Bundled RAR Extractor

If you want to distribute patches as `.rar` archives without requiring users to install archive software manually, place one of these files in this folder:

- `unrar.exe`
- or `7z.exe`

The patcher checks this `tools\` directory first and uses the bundled extractor automatically.

Recommended setup:

1. Put `unrar.exe` or `7z.exe` into `tools\`
2. Keep your patch URLs in `patches.json` as `.rar`
3. Ship the patcher together with the `tools\` folder

Notes:

- The repository does not include an extractor binary by default.
- You should verify the license terms of the extractor you plan to redistribute.
