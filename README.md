# D&D Treasure Generator & Wealth Manager

A PyQt5 desktop project for Dungeons & Dragons 5e treasure generation, inventories, party distribution, shop lookup and character wealth tracking.

## Install

Use Python 3.10–3.12 and a desktop environment.

```sh
python -m pip install -r requirements.txt
python DnDWealthManager_V1.0.py
```

Run the script from any working directory: data files are loaded relative to the application source, not your terminal directory. The bundled `base-items.json`, `base-item-tables.json`, `gems.json`, and `art_objects.json` must remain next to the script.

Network-backed equipment information requires an internet connection. External requests now have timeouts; offline use is still possible for features that use local tables.

## Character profiles

Use the **Save Profile** and **Load Profile** menu options. Save operations use an atomic temporary file and replace the destination only after serialization succeeds. Preserve external backups before upgrading from early releases.

## Known limitations

This is a large early-stage, single-file application. No end-to-end Qt GUI regression suite or independent game-rule verification has been completed. Existing game economy and wealth-distribution formulas are not changed by the reliability patch. Some dialogs assume the 2014 5e rules and may need review for later rule sets.

## Improvements in this branch

- Loads bundled JSON files consistently regardless of the launch folder.
- Adds a 15-second timeout to equipment API requests.
- Avoids crashing on a missing optional splash image.
- Reduces startup splash delay.
- Makes profile saves atomic and verifies the loaded JSON root type.
- Removes `enum34`, an obsolete Python 2 backport.

## Testing

Install packages, launch the program and exercise treasure generation, buying and selling, saving, loading, and startup from another working directory. CI currently checks Python compilation and JSON syntax; full GUI/manual game-rule testing is still required.
