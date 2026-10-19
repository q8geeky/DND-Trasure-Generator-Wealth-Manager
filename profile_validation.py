"""Validation of saved D&D profiles before mutating GUI state.

Accepts profiles created by the legacy application (which have no version key).
Missing optional fields remain supported; required inventory fields are checked.
"""
from __future__ import annotations

from decimal import Decimal, InvalidOperation

MAX_PROFILE_BYTES = 8 * 1024 * 1024
MAX_ITEMS_PER_TYPE = 50_000
VERSION = 1

REQUIRED_FIELDS = {
    "misc_items": ("Name", "Value", "Weight"),
    "gems": ("Type", "Quantity", "Total Value", "Weight"),
    "arts": ("Name", "Value", "Weight"),
    "magic_items": ("Name", "Value", "Weight", "Rarity", "Attunement"),
    "weapons": ("Name", "Value", "Weight"),
    "armor": ("Name", "Value", "Weight"),
}
NUMERIC_FIELDS = {
    "misc_items": ("Value", "Weight"),
    "gems": ("Quantity", "Total Value", "Weight"),
    "arts": ("Value", "Weight"),
    "magic_items": ("Value", "Weight"),
    "weapons": ("Value", "Weight"),
    "armor": ("Value", "Weight"),
}


def _nonnegative_number(value, label: str) -> Decimal:
    if isinstance(value, bool) or not isinstance(value, (str, int, float, Decimal)):
        raise ValueError(f"{label} must be numeric.")
    try:
        result = Decimal(str(value))
    except (InvalidOperation, ValueError) as exc:
        raise ValueError(f"{label} must be numeric.") from exc
    if not result.is_finite() or result < 0:
        raise ValueError(f"{label} must be finite and nonnegative.")
    return result


def validate_profile(payload) -> dict:
    if not isinstance(payload, dict):
        raise ValueError("Profile must be a JSON object.")
    version = payload.get("profile_version", VERSION)
    if isinstance(version, bool) or version != VERSION:
        raise ValueError("Unsupported profile version.")

    currencies = payload.get("currency_vars", {})
    if not isinstance(currencies, dict):
        raise ValueError("currency_vars must be an object.")
    for currency, amount in currencies.items():
        if not isinstance(currency, str):
            raise ValueError("Currency names must be strings.")
        _nonnegative_number(amount, f"Currency {currency}")

    for section, required in REQUIRED_FIELDS.items():
        entries = payload.get(section, [])
        if not isinstance(entries, list) or len(entries) > MAX_ITEMS_PER_TYPE:
            raise ValueError(f"{section} must be a list of at most {MAX_ITEMS_PER_TYPE} items.")
        for i, item in enumerate(entries):
            if not isinstance(item, dict):
                raise ValueError(f"{section}[{i}] must be an object.")
            for field in required:
                if field not in item or not isinstance(item[field], str):
                    raise ValueError(f"{section}[{i}].{field} must be a string.")
            for field in NUMERIC_FIELDS[section]:
                value = _nonnegative_number(item[field], f"{section}[{i}].{field}")
                if field == "Quantity" and (value < 1 or value != value.to_integral_value()):
                    raise ValueError(f"{section}[{i}].Quantity must be a positive whole number.")
            for field in ("BoughtFromShop", "Description"):
                if field in item and not isinstance(item[field], str):
                    raise ValueError(f"{section}[{i}].{field} must be a string.")
    return payload
