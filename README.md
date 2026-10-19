# D&D Treasure Generator & Wealth Manager

A PyQt5 desktop application for Dungeons & Dragons 5e treasure generation, inventory tracking, coin holdings, equipment shopping, party distribution and profile export/import.

## Install and run

Use **Python 3.10–3.12** on a computer with a desktop display.

```sh
git clone https://github.com/q8geeky/DND-Trasure-Generator-Wealth-Manager.git
cd DND-Trasure-Generator-Wealth-Manager
python -m pip install -r requirements.txt
python DnDWealthManager_V1.0.py
```

The `base-items.json`, `base-item-tables.json`, `gems.json` and `art_objects.json` files must stay next to the application script. The app resolves these resources relative to the script rather than the terminal's current working directory.

Online equipment descriptions/search require access to the external 5e API. Failures and timeouts are reported without crashing item descriptions; local treasure tables work offline.

## Safe save profiles

Choose **File → Save Profile** to save currency and inventory to a JSON document. The app writes a temporary file and atomically replaces the intended save only after serialization succeeds. Keep independent backups of important profiles.

**File → Load Profile** validates the complete document *before* replacing the current inventory. Current saves include `profile_version: 1`. Older saves without this key remain supported. The loader checks:

- top-level structure, list/item fields and numeric values;
- finite nonnegative currency, item value and weight;
- valid positive integer gem quantities;
- unknown future profile versions;
- an 8 MiB input-size limit.

A malformed profile is rejected and leaves the existing inventory untouched.

**Current scope:** profiles save currency and the six inventory categories; party loot awaiting distribution, customized exchange-rate settings and other temporary UI state are **not yet persisted**. Do not rely on profiles as a full game-session snapshot.

## Inventory reliability fixes

- Filtering and sorting now map visible rows to the underlying model before showing descriptions or removing selected items.
- Shop-bought flags for Art Objects and Magic Items use the correct columns when selling.
- Duplicate party member names are rejected before loot is distributed, avoiding silent overwrites.
- Invalid gem quantity and offline equipment descriptions are handled more safely.
- A missing optional splash image no longer blocks startup; delay reduced to 1.2 seconds.

## Limitations and development status

This is still a large single-file desktop application. It uses historical D&D 5e tables; newer game editions have not been audited. The original treasure and exchange-value algorithms have not been independently verified for rules accuracy. Windows-specific GUI and full gameplay manual testing are recommended before a public release.

## Automated tests

```sh
python -m pip install -r requirements.txt
python -m unittest discover -s tests -v
```

GitHub Actions compiles the source, checks JSON tables, and runs headless Qt regressions covering filtered selections, shopping flags, corrupted save rejection, offline requests and profile round trips. Tests use `QT_QPA_PLATFORM=offscreen` and do not require live network access.

## Feedback

Open a GitHub issue with reproducible steps and a redacted sample profile if possible. Please do not upload campaign data or private saves publicly.
