"""Import the legacy hyphenated entrypoint under a stable module name."""
from __future__ import annotations
import importlib.util
from pathlib import Path
_spec = importlib.util.spec_from_file_location(
    "DnDWealthManager_V1_0",
    Path(__file__).resolve().parent / "DnDWealthManager_V1.0.py",
)
if _spec is None or _spec.loader is None:
    raise ImportError("Cannot load DnD manager")
_module = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_module)
DnDWealthManager = _module.DnDWealthManager
