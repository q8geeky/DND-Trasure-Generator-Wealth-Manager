"""Pure profile-data validation tests; no GUI or network required."""
from __future__ import annotations
import unittest
from profile_validation import validate_profile


class TestProfileValidation(unittest.TestCase):
    def test_legacy_profile_without_version_still_loads(self):
        data={"currency_vars":{"gp":"125","cp":"0"}, "weapons":[
            {"Name":"Dagger","Value":"2","Weight":"1","BoughtFromShop":"No"}]}
        self.assertIs(validate_profile(data),data)

    def test_current_format(self):
        data={"profile_version":1,"gems":[
            {"Type":"Ruby","Quantity":"2","Total Value":"100","Weight":"0.2"}]}
        self.assertIs(validate_profile(data),data)

    def test_invalid_entries_never_mutate(self):
        for value in [
            {"currency_vars":{"gp":"NaN"}},
            {"currency_vars":{"gp":"Infinity"}},
            {"weapons":[{"Name":"Sword","Value":"not-a-number","Weight":"1"}]},
            {"armor":[{"Name":"Shield","Value":"4"}]},
            {"gems":[{"Type":"Ruby","Quantity":"0","Total Value":"10","Weight":"1"}]},
            {"gems":[{"Type":"Ruby","Quantity":"1.5","Total Value":"10","Weight":"1"}]},
            {"magic_items":"not a list"},
            {"profile_version":3},
            {"weapons":[123]},
            {"currency_vars":[1,2]},
        ]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                validate_profile(value)

    def test_does_not_mutate_valid_profile(self):
        data={"weapons":[],"currency_vars":{"cp":"20"}}
        before={"weapons":[],"currency_vars":{"cp":"20"}}
        validate_profile(data)
        self.assertEqual(data,before)


if __name__=="__main__":
    unittest.main()
