"""Headless Qt regressions for actions that can alter player inventory."""
from __future__ import annotations

import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

os.environ.setdefault("QT_QPA_PLATFORM", "offscreen")

from PyQt5 import QtGui, QtWidgets
from DnDWealthManager_V1_0_import import DnDWealthManager


def row(*values):
    return [QtGui.QStandardItem(str(v)) for v in values]


class TestDesktopWorkflows(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.app = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])

    def setUp(self):
        self.window = DnDWealthManager()
        self.window.close()

    def tearDown(self):
        self.window.deleteLater()

    def test_filtered_inventory_remove_correct_item(self):
        self.window.weapons_model.appendRow(row("Sword", "10", "1", "No", "The sword"))
        self.window.weapons_model.appendRow(row("Axe", "15", "2", "No", "The axe"))
        self.window.weapons_search_input.setText("Axe")
        self.app.processEvents()
        self.assertEqual(self.window.weapons_proxy_model.rowCount(), 1)
        self.window.weapons_table.selectRow(0)
        self.window.remove_weapons_item()
        self.assertEqual(self.window.weapons_model.rowCount(), 1)
        self.assertEqual(self.window.weapons_model.item(0, 0).text(), "Sword")

    def test_filtered_description(self):
        self.window.armor_model.appendRow(row("Plate", "30", "10", "No", "heavy armor"))
        self.window.armor_model.appendRow(row("Leather", "10", "2", "Yes", "light armor"))
        self.window.armor_search_input.setText("Leather")
        self.app.processEvents()
        self.window.armor_table.selectRow(0)
        self.assertEqual(self.window.armor_description.toPlainText(), "light armor")

    def test_shop_flag_uses_real_column(self):
        self.window.add_to_inventory_tab(
            "Art Objects", "Copper Statue", 25, 1, bought_from_shop=True,
            description="Not a purchase flag"
        )
        self.window.add_to_inventory_tab(
            "Magic Items", "Radiant Ring", 60, 0, bought_from_shop=True,
            description="Also not a purchase flag"
        )
        self.window.sell_category_combo.setCurrentText("Art Objects")
        self.window.update_sell_table()
        self.assertEqual(self.window.sell_model.item(0, 4).text(), "Yes")
        self.window.remove_item_from_inventory_by_name("Art Objects", "Copper Statue", True)
        self.assertEqual(self.window.art_model.rowCount(), 0)

        self.window.sell_category_combo.setCurrentText("Magic Items")
        self.window.update_sell_table()
        self.assertEqual(self.window.sell_model.item(0, 4).text(), "Yes")
        self.window.remove_item_from_inventory_by_name("Magic Items", "Radiant Ring", True)
        self.assertEqual(self.window.magic_model.rowCount(), 0)

    def test_duplicate_party_names_do_not_clear_loot(self):
        self.window.member_count_input.setValue(2)
        self.window.member_inputs[0].setText("Player")
        self.window.member_inputs[1].setText("Player")
        self.window.party_loot["Coins"] = {"gp": 10}
        with patch.object(QtWidgets.QMessageBox, "warning") as warning:
            self.window.distribute_loot()
            self.assertTrue(warning.called)
        self.assertEqual(self.window.party_loot["Coins"], {"gp": 10})

    def test_profile_saved_and_loaded(self):
        self.window.misc_model.appendRow(row("Rope", "1", "5", "No", "Climbing rope"))
        self.window.magic_model.appendRow(row("Ring", "Rare", "Yes", "30", "0", "Glowing", "Yes"))
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "profile.json"
            with patch.object(QtWidgets.QFileDialog, "getSaveFileName", return_value=(str(path), "JSON Files (*.json)")), \
                 patch.object(QtWidgets.QMessageBox, "information"):
                self.window.save_profile()
            self.assertTrue(path.is_file())
            payload = json.loads(path.read_text(encoding="utf-8"))
            self.assertEqual(payload["magic_items"][0]["BoughtFromShop"], "Yes")
            self.window.misc_model.setRowCount(0)
            self.window.magic_model.setRowCount(0)
            with patch.object(QtWidgets.QFileDialog, "getOpenFileName", return_value=(str(path), "JSON Files (*.json)")), \
                 patch.object(QtWidgets.QMessageBox, "information"):
                self.window.load_profile()
            self.assertEqual(self.window.misc_model.item(0, 4).text(), "Climbing rope")
            self.assertEqual(self.window.magic_model.item(0, 6).text(), "Yes")

    def test_offline_shop_description_does_not_crash(self):
        import requests
        from PyQt5 import QtCore
        lantern = QtGui.QStandardItem("Lantern")
        lantern.setData("/api/equipment/lantern", QtCore.Qt.UserRole)
        self.window.shop_model.appendRow([
            lantern,
            QtGui.QStandardItem("Adventuring Gear"),
            QtGui.QStandardItem("5"),
            QtGui.QStandardItem("1"),
        ])
        with patch("requests.get", side_effect=requests.exceptions.ConnectionError("offline")):
            self.window.shop_table.selectRow(0)
            self.window.display_item_description(None, None)
            self.assertIn("unavailable", self.window.item_description.toPlainText().lower())
            with patch.object(QtWidgets.QMessageBox, "question",
                              return_value=QtWidgets.QMessageBox.No):
                self.window.buy_shop_item()



if __name__ == "__main__":
    unittest.main()
