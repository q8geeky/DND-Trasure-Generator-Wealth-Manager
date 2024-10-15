import sys
import os
import json
import random
import math
import logging
import re
import csv
import concurrent.futures
import requests
import matplotlib.pyplot as plt
import copy
from collections import deque, Counter
from decimal import Decimal, ROUND_DOWN
from enum import Enum
from PyQt5 import QtWidgets, QtGui, QtCore
from PyQt5.QtWidgets import QSplashScreen
from PyQt5.QtCore import Qt, QTimer
from difflib import get_close_matches
from PyQt5.QtGui import QPixmap, QFont, QPainter, QColor
from matplotlib.backends.backend_qt5agg import FigureCanvasQTAgg as FigureCanvas

# =================== Configurable Sections ===================

# Font size for the splash screen message
SPLASH_FONT_SIZE = 16  # Adjust the font size here

# Desired size for the splash screen image (width, height)
SPLASH_IMAGE_SIZE = (800, 800)  # Adjust the image size here

# Splash screen display duration in milliseconds (set to 0 for auto-close)
SPLASH_DISPLAY_TIME = 7000  # 7000 ms = 7 seconds

# Hex color codes for the splash screen message
SPLASH_TEXT_COLOR = "#FF5733"  # Orange-Red color
SPLASH_OUTLINE_COLOR = "#000000"  # Black color
SPLASH_GLOW_COLOR = "#FFD700"  # Gold color

# =================== End of Configurable Sections ===================

def resource_path(relative_path):
    """ Get absolute path to resource, works for dev and for PyInstaller """
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)

with open(resource_path('art_objects.json'), 'r') as f:
    art_objects = json.load(f)

with open(resource_path('base-items.json'), 'r') as f:
    base_items = json.load(f)

with open(resource_path('base-item-tables.json'), 'r') as f:
    magic_item_tables = json.load(f)

with open(resource_path('gems.json'), 'r') as f:
    gems_data = json.load(f)

class Currency(Enum):
    PP = 'pp'
    GP = 'gp'
    EP = 'ep'
    SP = 'sp'
    CP = 'cp'

class CurrencyCustomizationDialog(QtWidgets.QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Customize Currency Rates")
        self.layout = QtWidgets.QFormLayout(self)
        self.rate_inputs = {}
        for currency in Currency:
            h_layout = QtWidgets.QHBoxLayout()
            for target_currency in Currency:
                if target_currency != currency:
                    label = QtWidgets.QLabel(f"{currency.name} to {target_currency.name}")
                    input = QtWidgets.QDoubleSpinBox()
                    input.setDecimals(4)
                    input.setRange(0.0001, 1000000)
                    input.setSingleStep(0.01)
                    rate = self.parent().conversion_rates.get(currency.value, {}).get(target_currency.value, None)
                    if rate is None:
                        inverse_rate = self.parent().conversion_rates.get(target_currency.value, {}).get(currency.value, None)
                        if inverse_rate:
                            rate = 1 / inverse_rate
                    if rate is not None:
                        input.setValue(rate)
                    else:
                        input.setValue(0)
                    h_layout.addWidget(label)
                    h_layout.addWidget(input)
                    self.rate_inputs[(currency.value, target_currency.value)] = input
            self.layout.addRow(f"{currency.name} Conversion Rates:", h_layout)
        buttons = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        self.layout.addWidget(buttons)

    def get_conversion_rates(self):
        rates = {}
        for (currency, target_currency), input in self.rate_inputs.items():
            rate = input.value()
            if rate > 0:
                if currency not in rates:
                    rates[currency] = {}
                rates[currency][target_currency] = rate
        return rates

class DnDWealthManager(QtWidgets.QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("D&D Wealth Manager")
        self.setMinimumSize(1200, 800)
        
        icon_path = resource_path('icon.ico')
        app_icon = QtGui.QIcon(icon_path)
        
        QtWidgets.QApplication.setWindowIcon(app_icon)
        self.setWindowIcon(app_icon)

        self.currency_vars = {currency.value: Decimal('0') for currency in Currency}
        self.misc_items = []
        self.gem_inventory = []
        self.art_inventory = [] 
        self.magic_items = []
        self.attuned_items = []
        self.total_weight = Decimal('0')
        self.carrying_capacity = Decimal('0')  
        self.dice_rolls = []
        self.generation_counter = 0
        
        self.conversion_rates = {
            'cp': {'sp': 0.1, 'ep': 0.02, 'gp': 0.01, 'pp': 0.001},
            'sp': {'cp': 10, 'ep': 0.2, 'gp': 0.1, 'pp': 0.01},
            'ep': {'cp': 50, 'sp': 5, 'gp': 0.5, 'pp': 0.05},
            'gp': {'cp': 100, 'sp': 10, 'ep': 2, 'pp': 0.1},
            'pp': {'cp': 1000, 'sp': 100, 'ep': 20, 'gp': 10}
        }
   
        self.magic_item_rarity_distribution = {
            'Common': 50,
            'Uncommon': 30,
            'Rare': 15,
            'Very Rare': 4,
            'Legendary': 1
        }
        
        self.rarity_values = {
            'Common': Decimal('100'),
            'Uncommon': Decimal('500'),
            'Rare': Decimal('5000'),
            'Very Rare': Decimal('50000'),
            'Legendary': Decimal('100000')
        }
        
        self.rarity_price_mapping = {
            'common': (50, 100),
            'uncommon': (101, 500),
            'rare': (501, 5000),
            'very rare': (5001, 50000),
            'legendary': (50001, 50001)  
        }

        self.magic_item_tables = self.load_json(
            'base-item-tables.json',
            required_keys=[f"Magic Item Table {chr(i)}" for i in range(65, 74)]  
        )
        self.base_items = self.load_json('base-items.json')  
        self.gems_data = self.load_json(
            'gems.json',
            required_keys=[
                '10 GP Gemstones', '50 GP Gemstones', '100 GP Gemstones',
                '500 GP Gemstones', '1000 GP Gemstones', '5000 GP Gemstones'
            ]
        )
        self.art_objects_data = self.load_json(
            'art_objects.json',
            required_keys=[
                '25 GP Art Objects', '250 GP Art Objects', '750 GP Art Objects',
                '2500 GP Art Objects', '7500 GP Art Objects'
            ]
        )

        if not self.validate_json_data(self.magic_item_tables, self.base_items, self.gems_data, self.art_objects_data):
            QtWidgets.QMessageBox.critical(self, "Error", "Validation of JSON data failed.")
            sys.exit(1)

        self.treasure_tables = {
            'Individual': {
                '0-4': {
                    'd100': {
                        '01-30': {'CP': '5d6', 'SP': None, 'EP': None, 'GP': None, 'PP': None},
                        '31-60': {'CP': None, 'SP': '4d6', 'EP': None, 'GP': None, 'PP': None},
                        '61-70': {'CP': None, 'SP': None, 'EP': '3d6', 'GP': None, 'PP': None},
                        '71-95': {'CP': None, 'SP': None, 'EP': None, 'GP': '3d6', 'PP': None},
                        '96-100': {'CP': None, 'SP': None, 'EP': None, 'GP': None, 'PP': '1d6'}
                    }
                },
                '5-10': {
                    'd100': {
                        '01-30': {'CP': '4d6 x 100', 'SP': None, 'EP': '1d6 x 10', 'GP': None, 'PP': None},
                        '31-60': {'CP': None, 'SP': '6d6 x 10', 'EP': None, 'GP': '2d6 x 10', 'PP': None},
                        '61-70': {'CP': None, 'SP': None, 'EP': '1d6 x 100', 'GP': '2d6 x 10', 'PP': None},
                        '71-95': {'CP': None, 'SP': None, 'EP': None, 'GP': '4d6 x 10', 'PP': None},
                        '96-100': {'CP': None, 'SP': None, 'EP': None, 'GP': '2d6 x 10', 'PP': '3d6'}
                    }
                },
                '11-16': {
                    'd100': {
                        '01-20': {'CP': None, 'SP': '4d6 x 100', 'EP': None, 'GP': '1d6 x 100', 'PP': None},
                        '21-35': {'CP': None, 'SP': None, 'EP': '1d6 x 100', 'GP': '1d6 x 100', 'PP': None},
                        '36-75': {'CP': None, 'SP': None, 'EP': None, 'GP': '2d6 x 100', 'PP': '1d6 x 10'},
                        '76-100': {'CP': None, 'SP': None, 'EP': None, 'GP': '2d6 x 100', 'PP': '2d6 x 10'}
                    }
                },
                '17+': {
                    'd100': {
                        '01-15': {'CP': None, 'SP': None, 'EP': '2d6 x 1000', 'GP': '8d6 x 100', 'PP': None},
                        '16-55': {'CP': None, 'SP': None, 'EP': None, 'GP': '1d6 x 1000', 'PP': '1d6 x 100'},
                        '56-100': {'CP': None, 'SP': None, 'EP': None, 'GP': '1d6 x 1000', 'PP': '2d6 x 100'}
                    }
                }
            },
            'Hoard': {
                '0-4': {
                    'Coins': {'CP': '6d6 x 100', 'SP': '3d6 x 100', 'EP': None, 'GP': '2d6 x 10', 'PP': None},
                    'd100': {
                        '01-06': {'Gems/Art': None, 'Magic Items': None},
                        '07-16': {'Gems/Art': '2d6 l10 gp gems', 'Magic Items': None},
                        '17-26': {'Gems/Art': '2d4 l25 gp art objects', 'Magic Items': None},
                        '27-36': {'Gems/Art': '2d6 l50 gp gems', 'Magic Items': None},
                        '37-44': {'Gems/Art': '2d6 l10 gp gems', 'Magic Items': 'Roll 1d6 times on Magic Item Table A'},
                        '45-52': {'Gems/Art': '2d4 l25 gp art objects', 'Magic Items': 'Roll 1d6 times on Magic Item Table A'},
                        '53-60': {'Gems/Art': '2d6 l50 gp gems', 'Magic Items': 'Roll 1d6 times on Magic Item Table A'},
                        '61-65': {'Gems/Art': '2d6 l10 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table B'},
                        '66-70': {'Gems/Art': '2d4 l25 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table B'},
                        '71-75': {'Gems/Art': '2d6 l50 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table B'},
                        '76-78': {'Gems/Art': '2d6 l10 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table C'},
                        '79-80': {'Gems/Art': '2d4 l25 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table C'},
                        '81-85': {'Gems/Art': '2d6 l50 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table C'},
                        '86-92': {'Gems/Art': '2d4 l25 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table F'},
                        '93-97': {'Gems/Art': '2d6 l50 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table F'},
                        '98-99': {'Gems/Art': '2d4 l25 gp art objects', 'Magic Items': 'Roll once on Magic Item Table G'},
                        '100': {'Gems/Art': '2d6 l50 gp gems', 'Magic Items': 'Roll once on Magic Item Table G'}
                    }
                },
                '5-10': {
                    'Coins': {'CP': '2d6 x 100', 'SP': '2d6 x 1000', 'EP': None, 'GP': '6d6 x 100', 'PP': '3d6 x 10'},
                    'd100': {
                        '01-04': {'Gems/Art': None, 'Magic Items': None},
                        '05-10': {'Gems/Art': '2d4 l25 gp art objects', 'Magic Items': None},
                        '11-16': {'Gems/Art': '3d6 l50 gp gems', 'Magic Items': None},
                        '17-22': {'Gems/Art': '3d6 l100 gp gems', 'Magic Items': None},
                        '23-28': {'Gems/Art': '2d4 l25 gp art objects', 'Magic Items': None},
                        '29-32': {'Gems/Art': '2d4 l25 gp art objects', 'Magic Items': 'Roll 1d6 times on Magic Item Table A'},
                        '33-36': {'Gems/Art': '3d6 l50 gp gems', 'Magic Items': 'Roll 1d6 times on Magic Item Table A'},
                        '37-40': {'Gems/Art': '3d6 l100 gp gems', 'Magic Items': 'Roll 1d6 times on Magic Item Table A'},
                        '41-44': {'Gems/Art': '2d4 l250 gp art objects', 'Magic Items': 'Roll 1d6 times on Magic Item Table A'},
                        '45-49': {'Gems/Art': '2d4 l25 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table B'},
                        '50-54': {'Gems/Art': '3d6 l50 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table B'},
                        '55-59': {'Gems/Art': '3d6 l100 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table B'},
                        '60-63': {'Gems/Art': '2d4 l250 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table B'},
                        '64-66': {'Gems/Art': '2d4 l25 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table C'},
                        '67-69': {'Gems/Art': '3d6 l50 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table C'},
                        '70-72': {'Gems/Art': '3d6 l100 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table C'},
                        '73-74': {'Gems/Art': '2d4 l250 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table C'},
                        '75-76': {'Gems/Art': '2d4 l25 gp art objects', 'Magic Items': 'Roll once on Magic Item Table D'},
                        '77-78': {'Gems/Art': '3d6 l50 gp gems', 'Magic Items': 'Roll once on Magic Item Table D'},
                        '79-80': {'Gems/Art': '3d6 l100 gp gems', 'Magic Items': 'Roll once on Magic Item Table D'}
                    }
                },
                '11-16': {
                    'Coins': {'CP': None, 'SP': None, 'EP': None, 'GP': '4d6 x 1000', 'PP': '5d6 x 100'},
                    'd100': {
                        '01-03': {'Gems/Art': None, 'Magic Items': None},
                        '04-06': {'Gems/Art': '2d4 l250 gp art objects', 'Magic Items': None},
                        '07-10': {'Gems/Art': '2d4 l750 gp art objects', 'Magic Items': None},
                        '11-12': {'Gems/Art': '3d6 l500 gp gems', 'Magic Items': None},
                        '13-15': {'Gems/Art': '3d6 l1000 gp gems', 'Magic Items': None},
                        '16-19': {'Gems/Art': '2d4 l250 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table A and 1d6 times on Magic Item Table B'},
                        '20-23': {'Gems/Art': '2d4 l750 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table A and 1d6 times on Magic Item Table B'},
                        '24-26': {'Gems/Art': '3d6 l500 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table A and 1d6 times on Magic Item Table B'},
                        '27-29': {'Gems/Art': '3d6 l1000 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table A and 1d6 times on Magic Item Table B'},
                        '30-35': {'Gems/Art': '2d4 l250 gp art objects', 'Magic Items': 'Roll 1d6 times on Magic Item Table C'},
                        '36-40': {'Gems/Art': '2d4 l750 gp art objects', 'Magic Items': 'Roll 1d6 times on Magic Item Table C'},
                        '41-45': {'Gems/Art': '3d6 l500 gp gems', 'Magic Items': 'Roll 1d6 times on Magic Item Table C'},
                        '46-50': {'Gems/Art': '3d6 l1000 gp gems', 'Magic Items': 'Roll 1d6 times on Magic Item Table C'},
                        '51-54': {'Gems/Art': '2d4 l250 gp art objects', 'Magic Items': 'Roll once on Magic Item Table D'},
                        '55-58': {'Gems/Art': '2d4 l750 gp art objects', 'Magic Items': 'Roll once on Magic Item Table D'},
                        '59-62': {'Gems/Art': '3d6 l500 gp gems', 'Magic Items': 'Roll once on Magic Item Table D'},
                        '63-66': {'Gems/Art': '3d6 l1000 gp gems', 'Magic Items': 'Roll once on Magic Item Table D'},
                        '67-68': {'Gems/Art': '2d4 l250 gp art objects', 'Magic Items': 'Roll once on Magic Item Table E'},
                        '69-70': {'Gems/Art': '2d4 l750 gp art objects', 'Magic Items': 'Roll once on Magic Item Table E'},
                        '71-72': {'Gems/Art': '3d6 l500 gp gems', 'Magic Items': 'Roll once on Magic Item Table E'},
                        '73-74': {'Gems/Art': '3d6 l1000 gp gems', 'Magic Items': 'Roll once on Magic Item Table E'},
                        '75-76': {'Gems/Art': '2d4 l250 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table F and 1d4 times on Magic Item Table G'},
                        '77-78': {'Gems/Art': '2d4 l750 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table F and 1d4 times on Magic Item Table G'},
                        '79-80': {'Gems/Art': '3d6 l500 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table F and 1d4 times on Magic Item Table G'},
                        '81-82': {'Gems/Art': '3d6 l1000 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table F and 1d4 times on Magic Item Table G'},
                        '83-85': {'Gems/Art': '2d4 l250 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table H'},
                        '86-88': {'Gems/Art': '2d4 l750 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table H'},
                        '89-91': {'Gems/Art': '3d6 l500 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table H'},
                        '92-94': {'Gems/Art': '3d6 l1000 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table H'},
                        '95-96': {'Gems/Art': '2d4 l250 gp art objects', 'Magic Items': 'Roll once on Magic Item Table I'},
                        '97-98': {'Gems/Art': '3d6 l500 gp gems', 'Magic Items': 'Roll once on Magic Item Table I'},
                        '99-100': {'Gems/Art': '3d6 l1000 gp gems', 'Magic Items': 'Roll once on Magic Item Table I'}
                    }
                },
                '17+': {
                    'Coins': {'CP': None, 'SP': None, 'EP': None, 'GP': '12d6 x 1000', 'PP': '8d6 x 1000'},
                    'd100': {
                        '01-02': {'Gems/Art': None, 'Magic Items': None},
                        '03-05': {'Gems/Art': '3d6 l1000 gp gems', 'Magic Items': 'Roll 1d8 times on Magic Item Table C'},
                        '06-08': {'Gems/Art': '1d10 l2500 gp art objects', 'Magic Items': 'Roll 1d8 times on Magic Item Table C'},
                        '09-11': {'Gems/Art': '1d4 l7500 gp art objects', 'Magic Items': 'Roll 1d8 times on Magic Item Table C'},
                        '12-14': {'Gems/Art': '1d8 l5000 gp gems', 'Magic Items': 'Roll 1d8 times on Magic Item Table C'},
                        '15-22': {'Gems/Art': '3d6 l1000 gp gems', 'Magic Items': 'Roll 1d6 times on Magic Item Table D'},
                        '23-30': {'Gems/Art': '1d10 l2500 gp art objects', 'Magic Items': 'Roll 1d6 times on Magic Item Table D'},
                        '31-38': {'Gems/Art': '1d4 l7500 gp art objects', 'Magic Items': 'Roll 1d6 times on Magic Item Table D'},
                        '39-46': {'Gems/Art': '1d8 l5000 gp gems', 'Magic Items': 'Roll 1d6 times on Magic Item Table D'},
                        '47-52': {'Gems/Art': '3d6 l1000 gp gems', 'Magic Items': 'Roll 1d6 times on Magic Item Table E'},
                        '53-58': {'Gems/Art': '1d10 l2500 gp art objects', 'Magic Items': 'Roll 1d6 times on Magic Item Table E'},
                        '59-63': {'Gems/Art': '1d4 l7500 gp art objects', 'Magic Items': 'Roll 1d6 times on Magic Item Table E'},
                        '64-68': {'Gems/Art': '1d8 l5000 gp gems', 'Magic Items': 'Roll 1d6 times on Magic Item Table E'},
                        '69-70': {'Gems/Art': '3d6 l1000 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table G'},
                        '71-72': {'Gems/Art': '1d10 l2500 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table G'},
                        '73-74': {'Gems/Art': '1d4 l7500 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table G'},
                        '75-76': {'Gems/Art': '1d8 l5000 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table G'},
                        '77-78': {'Gems/Art': '3d6 l1000 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table H'},
                        '79-80': {'Gems/Art': '1d10 l2500 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table H'},
                        '81-85': {'Gems/Art': '3d6 l1000 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table I'},
                        '86-90': {'Gems/Art': '1d10 l2500 gp art objects', 'Magic Items': 'Roll 1d4 times on Magic Item Table I'},
                        '91-95': {'Gems/Art': '1d4 l7500 gp art objects', 'Magic Items': 'Roll once on Magic Item Table F and 1d4 times on Magic Item Table G'},
                        '96-100': {'Gems/Art': '1d8 l5000 gp gems', 'Magic Items': 'Roll 1d4 times on Magic Item Table I'}
                    }
                }
            }
        }
        self.party_loot = {
        'Coins': {},
        'Gems': [],
        'Art Objects': [],
        'Magic Items': []
    }

        self.create_widgets()
        self.create_menu_bar()

    def create_widgets(self):
        """Set up the main UI components."""
        central_widget = QtWidgets.QWidget()
        self.setCentralWidget(central_widget)
        main_layout = QtWidgets.QVBoxLayout(central_widget)
        self.tabs = QtWidgets.QTabWidget()
        main_layout.addWidget(self.tabs)
        self.create_currency_tab()
        self.create_inventory_tab()
        self.create_treasure_tab()
        self.create_dice_rolls_tab()
        self.create_party_distribution_tab()
        self.create_settings_tab()
        self.create_help_tab()
        self.create_shop_tab() 
        self.tabs.currentChanged.connect(self.on_tab_changed)
        
    def on_tab_changed(self, index):
        """Handle actions when a different tab is selected."""
        selected_tab = self.tabs.tabText(index)
        if selected_tab == "Shop":
            logging.info("Shop tab selected. Refreshing sell table and updating currency holdings.")
            self.update_sell_table()
            self.currency_holdings_label.setText(self.get_currency_holdings_text())  
        
    def create_shop_tab(self):
        """Create the Shop tab where users can buy and sell items."""
        self.shop_tab = QtWidgets.QWidget()
        self.tabs.addTab(self.shop_tab, "Shop")
        
        layout = QtWidgets.QVBoxLayout(self.shop_tab)
        
        rate_layout = QtWidgets.QHBoxLayout()
        layout.addLayout(rate_layout)
        
        rate_label = QtWidgets.QLabel("Shop Sell Rate (%):")
        rate_layout.addWidget(rate_label)
        
        self.shop_rate_slider = QtWidgets.QSlider(QtCore.Qt.Horizontal)
        self.shop_rate_slider.setRange(0, 100)
        self.shop_rate_slider.setValue(50)
        self.shop_rate_slider.setTickInterval(10)
        rate_layout.addWidget(self.shop_rate_slider)
        self.shop_rate_slider.setTickPosition(QtWidgets.QSlider.TicksBelow)
        
        self.shop_rate_label = QtWidgets.QLabel("50%")
        rate_layout.addWidget(self.shop_rate_label)
        
        self.shop_rate_slider.valueChanged.connect(self.update_shop_rate_label)
       
        search_layout = QtWidgets.QHBoxLayout()
        layout.addLayout(search_layout)
        
        self.shop_search_input = QtWidgets.QLineEdit()
        self.shop_search_input.setPlaceholderText("Search for items")
        search_layout.addWidget(self.shop_search_input)
        
        search_button = QtWidgets.QPushButton("Search")
        search_layout.addWidget(search_button)
        search_button.clicked.connect(self.search_shop_items)
        
        self.shop_table = QtWidgets.QTableView()
        self.shop_model = QtGui.QStandardItemModel(0, 4)
        self.shop_model.setHorizontalHeaderLabels(['Name', 'Category', 'Cost (gp)', 'Weight (lbs)'])
        self.shop_table.setModel(self.shop_model)
        self.shop_table.setSortingEnabled(False)
        layout.addWidget(self.shop_table)
        
        buy_button = QtWidgets.QPushButton("Buy Selected Item")
        layout.addWidget(buy_button)
        buy_button.clicked.connect(self.buy_shop_item)
        
        separator = QtWidgets.QFrame()
        separator.setFrameShape(QtWidgets.QFrame.HLine)
        separator.setFrameShadow(QtWidgets.QFrame.Sunken)
        layout.addWidget(separator)
        
        sell_layout = QtWidgets.QHBoxLayout()
        layout.addLayout(sell_layout)
        
        sell_label = QtWidgets.QLabel("Your Inventory:")
        sell_layout.addWidget(sell_label)
        
        self.sell_category_combo = QtWidgets.QComboBox()
        self.sell_category_combo.addItems(['Weapons', 'Armor', 'Miscellaneous Items', 'Gems', 'Art Objects', 'Magic Items'])
        sell_layout.addWidget(self.sell_category_combo)
        self.sell_category_combo.currentIndexChanged.connect(self.update_sell_table)
        
        self.sell_table = QtWidgets.QTableView()
        self.sell_model = QtGui.QStandardItemModel(0, 5)  
        self.sell_model.setHorizontalHeaderLabels(['Name', 'Category', 'Value (gp)', 'Weight (lbs)', 'Bought from Shop'])
        self.sell_table.setModel(self.sell_model)
        self.sell_table.setSortingEnabled(False)
        layout.addWidget(self.sell_table)
        
        sell_button = QtWidgets.QPushButton("Sell Selected Item")
        layout.addWidget(sell_button)
        sell_button.clicked.connect(self.sell_inventory_item)
        
        currency_layout = QtWidgets.QHBoxLayout()
        layout.addLayout(currency_layout)

        currency_label = QtWidgets.QLabel("Current Holdings:")
        currency_layout.addWidget(currency_label)

        self.currency_holdings_label = QtWidgets.QLabel(self.get_currency_holdings_text())
        currency_layout.addWidget(self.currency_holdings_label)
        
        self.item_description = QtWidgets.QTextEdit()
        self.item_description.setReadOnly(True)
        layout.addWidget(self.item_description)

        self.shop_table.selectionModel().selectionChanged.connect(self.display_item_description)
       
        self.update_sell_table()
        
    def display_item_description(self, selected, deselected):
        indexes = self.shop_table.selectionModel().selectedRows()
        if indexes:
            index = indexes[0]
            name = self.shop_model.item(index.row(), 0).text()
            category = self.shop_model.item(index.row(), 1).text()
            
            item_url = self.shop_model.item(index.row(), 0).data(QtCore.Qt.UserRole)
            if not item_url:
                self.item_description.setText("Item URL is missing.")
                return

            item_response = requests.get(f"https://www.dnd5eapi.co{item_url}")
            if item_response.status_code == 200:
                try:
                    item_data = item_response.json()
                    description = '\n'.join(item_data.get('desc', ['No description available.']))
                    self.item_description.setText(f"Name: {name}\nCategory: {category}\n\nDescription:\n{description}")
                except json.JSONDecodeError:
                    self.item_description.setText("Invalid JSON response from the API.")
            else:
                self.item_description.setText("Unable to fetch item description.")
        else:
            self.item_description.clear()
        
    def update_dice_roll_list(self):
        self.dice_roll_list.clear()
        for roll in self.dice_rolls:
            self.dice_roll_list.addItem(roll)   
        
    def get_currency_holdings_text(self):
        holdings = []
        for currency in Currency:
            amount = self.currency_vars[currency.value]
            holdings.append(f"{amount} {currency.name}")
        return ", ".join(holdings)    

    def update_currency(self, currency, value):
        self.currency_vars[currency.value] = Decimal(value)
        self.update_total_wealth_and_weight()
        self.currency_holdings_label.setText(self.get_currency_holdings_text())  
       
    def update_shop_rate_label(self):
        rate = self.shop_rate_slider.value()
        self.shop_rate_label.setText(f"{rate}%")
        logging.info(f"Shop sell rate updated to {rate}%")
        
    def search_shop_items(self):
        search_term = self.shop_search_input.text().strip().lower()
        if not search_term:
            QtWidgets.QMessageBox.warning(self, "Warning", "Please enter a search term.")
            return

        self.shop_model.setRowCount(0)
        urls = [
            "https://www.dnd5eapi.co/api/equipment",
            "https://www.dnd5eapi.co/api/magic-items"
        ]

        try:
            results = []
            for url in urls:
                response = requests.get(url)
                if response.status_code != 200:
                    continue
                data = response.json()
                results.extend(data.get('results', []))

            filtered_items = [item for item in results if search_term in item['name'].lower()]

            if not filtered_items:
                QtWidgets.QMessageBox.information(self, "No Results", f"No items found for '{search_term}'.")
                return

            item_urls = [f"https://www.dnd5eapi.co{item['url']}" for item in filtered_items]

            def fetch_item_data(url):
                try:
                    item_response = requests.get(url)
                    if item_response.status_code != 200:
                        return None
                    return item_response.json()
                except requests.exceptions.RequestException as e:
                    logging.error(f"Error fetching {url}: {e}")
                    return None

            with concurrent.futures.ThreadPoolExecutor(max_workers=10) as executor:
                item_data_list = list(executor.map(fetch_item_data, item_urls))

            for item_data in item_data_list:
                if item_data is None:
                    continue
                name = item_data.get('name', 'Unknown')
                category = self.get_item_category(item_data)
                cost_gp = self.extract_cost_in_gp(item_data.get('cost', {}))
                weight = item_data.get('weight', 0)

                if cost_gp == Decimal('0'):
                    rarity_info = item_data.get('rarity', {})
                    rarity_name = rarity_info.get('name', '').lower()
                    if rarity_name in self.rarity_price_mapping:
                        price_range = self.rarity_price_mapping[rarity_name]
                        if price_range[0] == price_range[1]:

                            cost_gp = Decimal(price_range[0])
                        else:

                            cost_gp = Decimal(random.randint(price_range[0], price_range[1]))
                    else:

                        cost_gp = Decimal('0')

                name_item = QtGui.QStandardItem(name)
                name_item.setData(item_data.get('url', ''), QtCore.Qt.UserRole)

                row = [
                    name_item,
                    QtGui.QStandardItem(category),
                    QtGui.QStandardItem(str(cost_gp)),
                    QtGui.QStandardItem(str(weight))
                ]
                self.shop_model.appendRow(row)

        except requests.exceptions.RequestException as e:
            logging.error(f"Network error occurred: {e}")
            QtWidgets.QMessageBox.critical(self, "Network Error", "Failed to connect to the D&D API.")
        except Exception as e:
            logging.error(f"Unexpected error occurred: {e}")
            QtWidgets.QMessageBox.critical(self, "Error", f"An unexpected error occurred: {e}")
            
    def fetch_description_from_api(self, item_name, category):
        """
        Fetch the description of an item from the D&D 5e API with enhanced matching.
        
        :param item_name: Name of the item.
        :param category: Category of the item (e.g., 'magic items', 'weapons', etc.)
        :return: Description string or "No description available." if not found.
        """
        try:
            # Define API endpoints based on category
            if category.lower() in ['weapons', 'armor', 'miscellaneous items']:
                search_url = "https://www.dnd5eapi.co/api/equipment"
            elif category.lower() == 'magic items':
                search_url = "https://www.dnd5eapi.co/api/magic-items"
            else:
                # Categories like 'art objects' or 'gems' do not require descriptions
                return ""
            
            response = requests.get(search_url)
            if response.status_code != 200:
                logging.error(f"Failed to fetch from {search_url}: Status code {response.status_code}")
                return "No description available."
            
            data = response.json()
            results = data.get('results', [])
            
            # 1. Exact Match (Case-Insensitive)
            for item in results:
                if item['name'].lower() == item_name.lower():
                    item_url = f"https://www.dnd5eapi.co{item['url']}"
                    item_response = requests.get(item_url)
                    if item_response.status_code == 200:
                        item_data = item_response.json()
                        description = '\n'.join(item_data.get('desc', ["No description available."]))
                        return description
            
            # 2. Normalized Match (Remove punctuation and compare)
            normalized_input = re.sub(r'[^\w\s]', '', item_name).lower()
            for item in results:
                normalized_item_name = re.sub(r'[^\w\s]', '', item['name']).lower()
                if normalized_item_name in normalized_input or normalized_input in normalized_item_name:
                    item_url = f"https://www.dnd5eapi.co{item['url']}"
                    item_response = requests.get(item_url)
                    if item_response.status_code == 200:
                        item_data = item_response.json()
                        description = '\n'.join(item_data.get('desc', ["No description available."]))
                        return description
            
            # 3. Fuzzy Matching using difflib
            item_names = [item['name'] for item in results]
            close_matches = get_close_matches(item_name, item_names, n=1, cutoff=0.8)
            if close_matches:
                matched_item = close_matches[0]
                for item in results:
                    if item['name'] == matched_item:
                        item_url = f"https://www.dnd5eapi.co{item['url']}"
                        item_response = requests.get(item_url)
                        if item_response.status_code == 200:
                            item_data = item_response.json()
                            description = '\n'.join(item_data.get('desc', ["No description available."]))
                            return description
            
            # If all matching strategies fail
            logging.warning(f"No description found for item '{item_name}' in category '{category}'.")
            return "No description available."
        except Exception as e:
            logging.error(f"Error fetching description for '{item_name}': {e}")
            return "No description available."     
            
    def get_item_category(self, item_data):
        category = item_data.get('equipment_category', {}).get('name', 'Unknown')
        if category == 'Weapon':
            subcategory = item_data.get('weapon_category', '')
            if subcategory:
                category = f"{category} - {subcategory}"
        elif category == 'Armor':
            subcategory = item_data.get('armor_category', '')
            if subcategory:
                category = f"{category} - {subcategory}"
        elif 'rarity' in item_data: 
            rarity = item_data.get('rarity', {}).get('name', 'Unknown')
            category = f"Magic Item - {rarity}"
        return category        
            
    def extract_cost_in_gp(self, cost):
        if not cost or 'unit' not in cost or 'quantity' not in cost:
            return Decimal('0')
        unit = cost.get('unit', 'gp')
        quantity = cost.get('quantity', 0)
        return self.convert_cost_to_gp(quantity, unit)

    def convert_cost_to_gp(self, quantity, unit):
        unit = unit.lower()
        quantity = Decimal(quantity)
        conversion_rates = {
            'cp': Decimal('0.01'),
            'sp': Decimal('0.1'),
            'ep': Decimal('0.5'),
            'gp': Decimal('1'),
            'pp': Decimal('10')
        }
        rate = conversion_rates.get(unit, Decimal('1'))
        return (quantity * rate).quantize(Decimal('0.01'))
  
    def buy_shop_item(self):
        selected = self.shop_table.selectionModel().selectedRows()
        if not selected:
            QtWidgets.QMessageBox.warning(self, "Warning", "Please select an item to buy.")
            return
        index = selected[0]
        name = self.shop_model.item(index.row(), 0).text()
        category = self.shop_model.item(index.row(), 1).text()
        cost_gp_text = self.shop_model.item(index.row(), 2).text()
        weight_text = self.shop_model.item(index.row(), 3).text()
        
        try:
            weight = Decimal(weight_text)
        except InvalidOperation:
            weight = Decimal('0')
        
        new_total_weight = self.total_weight + weight
        if self.carrying_capacity > 0 and new_total_weight > self.carrying_capacity:
            QtWidgets.QMessageBox.warning(self, "Warning", "Cannot buy item. Carrying capacity exceeded.")
            return

        try:
            cost_gp = Decimal(cost_gp_text)
        except InvalidOperation:
            QtWidgets.QMessageBox.warning(self, "Warning", f"The item '{name}' does not have a valid cost.")
            return

        item_url = self.shop_model.item(index.row(), 0).data(QtCore.Qt.UserRole)
        if item_url:
            item_response = requests.get(f"https://www.dnd5eapi.co{item_url}")
            if item_response.status_code == 200:
                try:
                    item_data = item_response.json()
                    description = '\n'.join(item_data.get('desc', ['No description available.']))
                except json.JSONDecodeError:
                    description = 'No description available.'
            else:
                description = 'No description available.'
        else:
            description = 'No description available.'

        reply = QtWidgets.QMessageBox.question(
            self, "Confirm Purchase",
            f"Do you want to buy '{name}' for {cost_gp} gp?",
            QtWidgets.QMessageBox.Yes | QtWidgets.QMessageBox.No,
            QtWidgets.QMessageBox.No
        )
        if reply == QtWidgets.QMessageBox.No:
            return

        if not self.deduct_currency(cost_gp):
            QtWidgets.QMessageBox.warning(self, "Warning", "You do not have enough funds to buy this item.")
            return

        inventory_type = self.map_category_to_inventory(category)
        self.add_to_inventory_tab(inventory_type, name, cost_gp, weight, bought_from_shop=True, description=description)

        self.update_total_wealth_and_weight()
        self.update_inventory_tabs()
        QtWidgets.QMessageBox.information(self, "Success", f"You have bought {name} for {cost_gp} gp.")

        action = {
            'action_type': 'buy_item',
            'data': {
                'name': name,
                'category': category,
                'cost': str(cost_gp),
                'weight': str(weight),
                'description': description  
            }
        }
        
    def map_category_to_inventory(self, category):
        equipment_categories = {
            'Weapon': 'Weapons',
            'Weapon - Simple Melee': 'Weapons',
            'Weapon - Simple Ranged': 'Weapons',
            'Weapon - Martial Melee': 'Weapons',
            'Weapon - Martial Ranged': 'Weapons',
            'Armor': 'Armor',
            'Armor - Light': 'Armor',
            'Armor - Medium': 'Armor',
            'Armor - Heavy': 'Armor',
            'Adventuring Gear': 'Miscellaneous Items',
            'Tools': 'Miscellaneous Items',
            'Mounts and Vehicles': 'Miscellaneous Items',
            'Gemstones': 'Gems',
            'Gem': 'Gems',
            'Art Objects': 'Art Objects',
            'Art Object': 'Art Objects',
            'Magic Items': 'Magic Items',
            'Magic Item': 'Magic Items',
        }
        base_category = category.split(' - ')[0]
        return equipment_categories.get(category, equipment_categories.get(base_category, 'Miscellaneous Items'))    
        
    def update_inventory_tabs(self):
        self.update_sell_table()
        self.update_total_wealth_and_weight()    
        
    def add_to_inventory_tab(self, inventory_type, name, value, weight, bought_from_shop=False, description=''):
        if inventory_type == 'Weapons':
            self.weapons_model.appendRow([
                QtGui.QStandardItem(name),
                QtGui.QStandardItem(str(value)),
                QtGui.QStandardItem(str(weight)),
                QtGui.QStandardItem('Yes' if bought_from_shop else 'No'),
                QtGui.QStandardItem(description)
            ])
        elif inventory_type == 'Armor':
            self.armor_model.appendRow([
                QtGui.QStandardItem(name),
                QtGui.QStandardItem(str(value)),
                QtGui.QStandardItem(str(weight)),
                QtGui.QStandardItem('Yes' if bought_from_shop else 'No'),
                QtGui.QStandardItem(description)
            ])
        elif inventory_type == 'Miscellaneous Items':
            for row in range(self.misc_model.rowCount()):
                if (self.misc_model.item(row, 0).text() == name and
                    self.misc_model.item(row, 3).text() == ('Yes' if bought_from_shop else 'No')):
                    break
            else:
                self.misc_model.appendRow([
                    QtGui.QStandardItem(name),
                    QtGui.QStandardItem(str(value)),
                    QtGui.QStandardItem(str(weight)),
                    QtGui.QStandardItem('Yes' if bought_from_shop else 'No'),
                    QtGui.QStandardItem(description)  
                ])
        elif inventory_type == 'Gems':
            for row in range(self.gem_model.rowCount()):
                if (self.gem_model.item(row, 0).text() == name and
                    self.gem_model.item(row, 4).text() == ('Yes' if bought_from_shop else 'No')):
                    current_qty = int(self.gem_model.item(row, 1).text())
                    current_total = Decimal(self.gem_model.item(row, 2).text())
                    self.gem_model.setItem(row, 1, QtGui.QStandardItem(str(current_qty + 1)))
                    self.gem_model.setItem(row, 2, QtGui.QStandardItem(str(current_total + value)))
                    return
            self.gem_model.appendRow([
                QtGui.QStandardItem(name),
                QtGui.QStandardItem("1"),
                QtGui.QStandardItem(str(value)),
                QtGui.QStandardItem(str(weight)),
                QtGui.QStandardItem('Yes' if bought_from_shop else 'No')
            ])
        elif inventory_type == 'Art Objects':
            self.art_model.appendRow([
                QtGui.QStandardItem(name),
                QtGui.QStandardItem(str(value)),
                QtGui.QStandardItem(str(weight)),
                QtGui.QStandardItem(description),  
                QtGui.QStandardItem('Yes' if bought_from_shop else 'No') 
            ])
        elif inventory_type == 'Magic Items':
            self.magic_model.appendRow([
                QtGui.QStandardItem(name),
                QtGui.QStandardItem('Unknown'),  
                QtGui.QStandardItem('No'),  
                QtGui.QStandardItem(str(value)),
                QtGui.QStandardItem(str(weight)),
                QtGui.QStandardItem(description), 
                QtGui.QStandardItem('Yes' if bought_from_shop else 'No') 
            ])
        
    def get_total_currency_in_gp(self):
        total = Decimal('0')
        for currency in Currency:
            amount = self.currency_vars[currency.value]
            gp_value = amount * self.get_currency_value_in_gp(currency)
            total += gp_value
        return total

    def deduct_currency(self, amount_gp):
        total_currency_in_gp = self.get_total_currency_in_gp()
        if total_currency_in_gp < amount_gp:
            return False

        remaining = amount_gp
        currency_order = sorted(
            Currency,
            key=lambda c: self.get_currency_value_in_gp(c),
            reverse=True
        )
        for currency in currency_order:
            currency_value = self.get_currency_value_in_gp(currency)
            available_amount = self.currency_vars[currency.value]
            amount_needed = (remaining // currency_value).to_integral_value(rounding=ROUND_DOWN)
            if amount_needed > available_amount:
                amount_needed = available_amount
            self.currency_vars[currency.value] -= amount_needed
            remaining -= amount_needed * currency_value
            self.currency_inputs[currency.value].setValue(int(self.currency_vars[currency.value]))
            if remaining <= 0:
                break
        self.currency_holdings_label.setText(self.get_currency_holdings_text()) 
        return True

    def create_menu_bar(self):
        """Set up the menu bar with File, Edit, and Help menus."""
        menu_bar = self.menuBar()
        file_menu = menu_bar.addMenu('File')

        save_action = QtWidgets.QAction('Save Profile', self)
        file_menu.addAction(save_action)
        save_action.triggered.connect(self.save_profile)

        load_action = QtWidgets.QAction('Load Profile', self)
        file_menu.addAction(load_action)
        load_action.triggered.connect(self.load_profile)

        file_menu.addSeparator()

        exit_action = QtWidgets.QAction('Exit', self)
        exit_action.triggered.connect(self.close)
        file_menu.addAction(exit_action)

        help_menu = menu_bar.addMenu('Help')

        about_action = QtWidgets.QAction('About', self)
        help_menu.addAction(about_action)
        about_action.triggered.connect(self.show_about_dialog)

    def create_currency_tab(self):
        """Create the Currency management tab."""
        self.currency_tab = QtWidgets.QWidget()
        self.tabs.addTab(self.currency_tab, "Currency")

        main_layout = QtWidgets.QVBoxLayout(self.currency_tab)

        holdings_group = QtWidgets.QGroupBox("Actual Currency Holdings")
        holdings_layout = QtWidgets.QVBoxLayout()
        holdings_group.setLayout(holdings_layout)
        main_layout.addWidget(holdings_group)

        self.currency_inputs = {}
        for currency in Currency:
            row_layout = QtWidgets.QHBoxLayout()
            label = QtWidgets.QLabel(currency.name)
            spin_box = QtWidgets.QSpinBox()
            spin_box.setRange(0, 999999999)
            self.currency_inputs[currency.value] = spin_box
            row_layout.addWidget(label)
            row_layout.addWidget(spin_box)
            holdings_layout.addLayout(row_layout)

        for currency in Currency:
            spin_box = self.currency_inputs[currency.value]
            spin_box.valueChanged.connect(lambda value, currency=currency: self.update_currency(currency, value))

        converter_group = QtWidgets.QGroupBox("Currency Converter")
        converter_layout = QtWidgets.QHBoxLayout()
        converter_group.setLayout(converter_layout)
        main_layout.addWidget(converter_group)

        self.converter_inputs = {}
        self.converter_results = {}
        for currency in Currency:
            v_layout = QtWidgets.QVBoxLayout()
            label = QtWidgets.QLabel(currency.name)
            v_layout.addWidget(label)

            spin_box = QtWidgets.QSpinBox()
            spin_box.setRange(0, 1000000)
            v_layout.addWidget(spin_box)
            self.converter_inputs[currency.value] = spin_box

            result_label = QtWidgets.QLabel()
            result_label.setWordWrap(True)
            v_layout.addWidget(result_label)
            self.converter_results[currency.value] = result_label

            converter_layout.addLayout(v_layout)

        for result_label in self.converter_results.values():
            result_label.setText("")

        for currency_value, spin_box in self.converter_inputs.items():
            spin_box.valueChanged.connect(lambda value, currency=currency_value: self.convert_currency(currency))
            
    def update_currency(self, currency, value):
        self.currency_vars[currency.value] = Decimal(value)
        logging.info(f"Currency updated: {currency.name} = {value}")
        self.update_total_wealth_and_weight()
        self.currency_holdings_label.setText(self.get_currency_holdings_text())        

    def create_inventory_tab(self):
        """Create the Inventory management tab with sub-tabs."""
        self.inventory_tab = QtWidgets.QWidget()
        self.tabs.addTab(self.inventory_tab, "Inventory")

        layout = QtWidgets.QVBoxLayout(self.inventory_tab)

        self.inventory_tabs = QtWidgets.QTabWidget()
        layout.addWidget(self.inventory_tabs)

        self.create_weapons_tab()
        self.create_armor_tab()
        self.create_misc_tab()
        self.create_gems_tab()
        self.create_art_tab()
        self.create_magic_tab()

        total_layout = QtWidgets.QHBoxLayout()
        self.total_wealth_label = QtWidgets.QLabel("Total Wealth: 0 gp")
        self.total_weight_label = QtWidgets.QLabel("Total Weight: 0 lbs")
        total_layout.addWidget(self.total_wealth_label)
        total_layout.addWidget(self.total_weight_label)
        layout.addLayout(total_layout)
        
    def create_weapons_tab(self):
        """Create the Weapons sub-tab."""
        self.weapons_tab = QtWidgets.QWidget()
        self.inventory_tabs.addTab(self.weapons_tab, "Weapons")

        layout = QtWidgets.QVBoxLayout(self.weapons_tab)

        input_layout = QtWidgets.QGridLayout()
        layout.addLayout(input_layout)

        name_label = QtWidgets.QLabel("Name:")
        self.weapon_name_input = QtWidgets.QLineEdit()
        input_layout.addWidget(name_label, 0, 0)
        input_layout.addWidget(self.weapon_name_input, 0, 1)

        value_label = QtWidgets.QLabel("Value (gp):")
        self.weapon_value_input = QtWidgets.QDoubleSpinBox()
        self.weapon_value_input.setRange(0, 1000000)
        input_layout.addWidget(value_label, 0, 2)
        input_layout.addWidget(self.weapon_value_input, 0, 3)

        weight_label = QtWidgets.QLabel("Weight (lbs):")
        self.weapon_weight_input = QtWidgets.QDoubleSpinBox()
        self.weapon_weight_input.setRange(0, 1000000)
        input_layout.addWidget(weight_label, 0, 4)
        input_layout.addWidget(self.weapon_weight_input, 0, 5)

        desc_label = QtWidgets.QLabel("Description:")
        self.weapon_desc_input = QtWidgets.QLineEdit()
        input_layout.addWidget(desc_label, 1, 0)
        input_layout.addWidget(self.weapon_desc_input, 1, 1, 1, 5)

        add_button = QtWidgets.QPushButton("Add Weapon")
        input_layout.addWidget(add_button, 2, 0, 1, 6)
        add_button.clicked.connect(self.add_weapon_item)

        search_layout = QtWidgets.QHBoxLayout()
        layout.addLayout(search_layout)

        self.weapons_search_input = QtWidgets.QLineEdit()
        self.weapons_search_input.setPlaceholderText("Search Weapons")
        search_layout.addWidget(self.weapons_search_input)

        self.weapons_sort_combo = QtWidgets.QComboBox()
        self.weapons_sort_combo.addItems(['Name', 'Value', 'Weight'])
        search_layout.addWidget(self.weapons_sort_combo)

        self.weapons_table = QtWidgets.QTableView()
        self.weapons_model = QtGui.QStandardItemModel(0, 5)
        self.weapons_model.setHorizontalHeaderLabels(['Name', 'Value (gp)', 'Weight (lbs)', 'Bought from Shop', 'Description'])

        self.weapons_proxy_model = QtCore.QSortFilterProxyModel()
        self.weapons_proxy_model.setSourceModel(self.weapons_model)
        self.weapons_proxy_model.setFilterKeyColumn(0)
        self.weapons_table.setModel(self.weapons_proxy_model)
        self.weapons_table.setSortingEnabled(False)

        self.weapons_search_input.textChanged.connect(self.weapons_proxy_model.setFilterRegularExpression)
        self.weapons_sort_combo.currentIndexChanged.connect(self.sort_weapons_items)

        layout.addWidget(self.weapons_table)

        remove_button = QtWidgets.QPushButton("Remove Selected")
        layout.addWidget(remove_button)
        remove_button.clicked.connect(self.remove_weapons_item)

        self.weapons_table.selectionModel().selectionChanged.connect(self.display_weapon_description)

        self.weapon_description = QtWidgets.QTextEdit()
        self.weapon_description.setReadOnly(True)
        layout.addWidget(self.weapon_description)
        
    def add_weapon_item(self):
        name = self.weapon_name_input.text()
        value = self.weapon_value_input.value()
        weight = self.weapon_weight_input.value()
        description = self.weapon_desc_input.text().strip()  
        
        if not name:
            QtWidgets.QMessageBox.warning(self, "Warning", "Please enter a weapon name.")
            return
        if value <= 0:
            QtWidgets.QMessageBox.warning(self, "Warning", "Value must be greater than zero.")
            return
        if weight < 0:
            QtWidgets.QMessageBox.warning(self, "Warning", "Weight cannot be negative.")
            return

        new_total_weight = self.total_weight + Decimal(weight)
        if self.carrying_capacity > 0 and new_total_weight > self.carrying_capacity:
            QtWidgets.QMessageBox.warning(self, "Warning", "Cannot add item. Carrying capacity exceeded.")
            return

        # Fetch description if not provided
        if not description:
            description = self.fetch_description_from_api(name, 'weapons')

        self.weapons_model.appendRow([
            QtGui.QStandardItem(name),
            QtGui.QStandardItem(str(value)),
            QtGui.QStandardItem(str(weight)),
            QtGui.QStandardItem('No'),  # Bought from Shop
            QtGui.QStandardItem(description if description else '')  # Description
        ])

        # Clear input fields
        self.weapon_name_input.clear()
        self.weapon_value_input.setValue(0)
        self.weapon_weight_input.setValue(0)
        self.weapon_desc_input.clear()

        # Update total wealth and weight
        self.update_total_wealth_and_weight()
            
    def display_weapon_description(self, selected, deselected):
        indexes = self.weapons_table.selectionModel().selectedRows()
        if indexes:
            index = indexes[0]
            description = self.weapons_model.item(index.row(), 4).text()
            self.weapon_description.setText(description)
        else:
            self.weapon_description.clear()

    def sort_weapons_items(self):
        sort_key = self.weapons_sort_combo.currentText()
        if sort_key == 'Name':
            column = 0
        elif sort_key == 'Value':
            column = 1
        elif sort_key == 'Weight':
            column = 2
        else:
            column = 0
        self.weapons_table.sortByColumn(column, QtCore.Qt.AscendingOrder)

    def remove_weapons_item(self):
        selected = self.weapons_table.selectionModel().selectedRows()
        for index in sorted(selected, reverse=True):
            row_data = {
                'name': self.weapons_model.item(index.row(), 0).text(),
                'value': float(self.weapons_model.item(index.row(), 1).text()),
                'weight': float(self.weapons_model.item(index.row(), 2).text())
            }
            self.weapons_model.removeRow(index.row())
            action = {
                'action_type': 'remove_weapons_item',
                'data': row_data
            }
            
        self.update_total_wealth_and_weight()   
        
    def create_armor_tab(self):
        """Create the Armor sub-tab."""
        self.armor_tab = QtWidgets.QWidget()
        self.inventory_tabs.addTab(self.armor_tab, "Armor")

        layout = QtWidgets.QVBoxLayout(self.armor_tab)

        input_layout = QtWidgets.QGridLayout()
        layout.addLayout(input_layout)

        name_label = QtWidgets.QLabel("Name:")
        self.armor_name_input = QtWidgets.QLineEdit()
        input_layout.addWidget(name_label, 0, 0)
        input_layout.addWidget(self.armor_name_input, 0, 1)

        value_label = QtWidgets.QLabel("Value (gp):")
        self.armor_value_input = QtWidgets.QDoubleSpinBox()
        self.armor_value_input.setRange(0, 1000000)
        input_layout.addWidget(value_label, 0, 2)
        input_layout.addWidget(self.armor_value_input, 0, 3)

        weight_label = QtWidgets.QLabel("Weight (lbs):")
        self.armor_weight_input = QtWidgets.QDoubleSpinBox()
        self.armor_weight_input.setRange(0, 1000000)
        input_layout.addWidget(weight_label, 0, 4)
        input_layout.addWidget(self.armor_weight_input, 0, 5)

        desc_label = QtWidgets.QLabel("Description:")
        self.armor_desc_input = QtWidgets.QLineEdit()
        input_layout.addWidget(desc_label, 1, 0)
        input_layout.addWidget(self.armor_desc_input, 1, 1, 1, 5)

        add_button = QtWidgets.QPushButton("Add Armor")
        input_layout.addWidget(add_button, 2, 0, 1, 6)
        add_button.clicked.connect(self.add_armor_item)

        search_layout = QtWidgets.QHBoxLayout()
        layout.addLayout(search_layout)

        self.armor_search_input = QtWidgets.QLineEdit()
        self.armor_search_input.setPlaceholderText("Search Armor")
        search_layout.addWidget(self.armor_search_input)

        self.armor_sort_combo = QtWidgets.QComboBox()
        self.armor_sort_combo.addItems(['Name', 'Value', 'Weight'])
        search_layout.addWidget(self.armor_sort_combo)

        self.armor_table = QtWidgets.QTableView()
        self.armor_model = QtGui.QStandardItemModel(0, 5)
        self.armor_model.setHorizontalHeaderLabels(['Name', 'Value (gp)', 'Weight (lbs)', 'Bought from Shop', 'Description'])

        self.armor_proxy_model = QtCore.QSortFilterProxyModel()
        self.armor_proxy_model.setSourceModel(self.armor_model)
        self.armor_proxy_model.setFilterKeyColumn(0)
        self.armor_table.setModel(self.armor_proxy_model)
        self.armor_table.setSortingEnabled(False)

        self.armor_search_input.textChanged.connect(self.armor_proxy_model.setFilterRegularExpression)
        self.armor_sort_combo.currentIndexChanged.connect(self.sort_armor_items)

        layout.addWidget(self.armor_table)

        remove_button = QtWidgets.QPushButton("Remove Selected")
        layout.addWidget(remove_button)
        remove_button.clicked.connect(self.remove_armor_item)

        self.armor_table.selectionModel().selectionChanged.connect(self.display_armor_description)

        self.armor_description = QtWidgets.QTextEdit()
        self.armor_description.setReadOnly(True)
        layout.addWidget(self.armor_description)
        
    def add_armor_item(self):
        name = self.armor_name_input.text()
        value = self.armor_value_input.value()
        weight = self.armor_weight_input.value()
        description = self.armor_desc_input.text()
        if not name:
            QtWidgets.QMessageBox.warning(self, "Warning", "Please enter an armor name.")
            return
        if value <= 0:
            QtWidgets.QMessageBox.warning(self, "Warning", "Value must be greater than zero.")
            return
        if weight < 0:
            QtWidgets.QMessageBox.warning(self, "Warning", "Weight cannot be negative.")
            return

        new_total_weight = self.total_weight + Decimal(weight)
        if self.carrying_capacity > 0 and new_total_weight > self.carrying_capacity:
            QtWidgets.QMessageBox.warning(self, "Warning", "Cannot add item. Carrying capacity exceeded.")
            return

        self.armor_model.appendRow([
            QtGui.QStandardItem(name),
            QtGui.QStandardItem(str(value)),
            QtGui.QStandardItem(str(weight)),
            QtGui.QStandardItem('No'),
            QtGui.QStandardItem(description)
        ])
        self.armor_name_input.clear()
        self.armor_value_input.setValue(0)
        self.armor_weight_input.setValue(0)
        self.armor_desc_input.clear()
        self.update_total_wealth_and_weight()  
        
    def display_armor_description(self, selected, deselected):
        indexes = self.armor_table.selectionModel().selectedRows()
        if indexes:
            index = indexes[0]
            description = self.armor_model.item(index.row(), 4).text()
            self.armor_description.setText(description)
        else:
            self.armor_description.clear()

    def sort_armor_items(self):
        sort_key = self.armor_sort_combo.currentText()
        if sort_key == 'Name':
            column = 0
        elif sort_key == 'Value':
            column = 1
        elif sort_key == 'Weight':
            column = 2
        else:
            column = 0
        self.armor_table.sortByColumn(column, QtCore.Qt.AscendingOrder)

    def remove_armor_item(self):
        selected = self.armor_table.selectionModel().selectedRows()
        for index in sorted(selected, reverse=True):
            row_data = {
                'name': self.armor_model.item(index.row(), 0).text(),
                'value': float(self.armor_model.item(index.row(), 1).text()),
                'weight': float(self.armor_model.item(index.row(), 2).text())
            }
            self.armor_model.removeRow(index.row())
            action = {
                'action_type': 'remove_armor_item',
                'data': row_data
            }
        self.update_total_wealth_and_weight()   

    def create_misc_tab(self):
        """Create the Miscellaneous Items sub-tab."""
        self.misc_tab = QtWidgets.QWidget()
        self.inventory_tabs.addTab(self.misc_tab, "Miscellaneous Items")

        layout = QtWidgets.QVBoxLayout(self.misc_tab)

        # Input Layout
        input_layout = QtWidgets.QGridLayout()
        layout.addLayout(input_layout)

        # Name Input
        name_label = QtWidgets.QLabel("Name:")
        self.misc_name_input = QtWidgets.QLineEdit()
        self.misc_name_input.setPlaceholderText("Item Name")
        input_layout.addWidget(name_label, 0, 0)
        input_layout.addWidget(self.misc_name_input, 0, 1)

        # Value Input
        value_label = QtWidgets.QLabel("Value (gp):")
        self.misc_value_input = QtWidgets.QDoubleSpinBox()
        self.misc_value_input.setRange(0, 1000000)
        input_layout.addWidget(value_label, 0, 2)
        input_layout.addWidget(self.misc_value_input, 0, 3)

        # Weight Input
        weight_label = QtWidgets.QLabel("Weight (lbs):")
        self.misc_weight_input = QtWidgets.QDoubleSpinBox()
        self.misc_weight_input.setRange(0, 1000000)
        input_layout.addWidget(weight_label, 0, 4)
        input_layout.addWidget(self.misc_weight_input, 0, 5)

        # Description Input
        desc_label = QtWidgets.QLabel("Description:")
        self.misc_desc_input = QtWidgets.QLineEdit()
        self.misc_desc_input.setPlaceholderText("Enter item description")
        input_layout.addWidget(desc_label, 1, 0)
        input_layout.addWidget(self.misc_desc_input, 1, 1, 1, 5)

        # Add Button
        add_button = QtWidgets.QPushButton("Add Item")
        input_layout.addWidget(add_button, 2, 0, 1, 6)
        add_button.clicked.connect(self.add_misc_item)

        # Search and Sort Layout
        search_layout = QtWidgets.QHBoxLayout()
        layout.addLayout(search_layout)

        self.misc_search_input = QtWidgets.QLineEdit()
        self.misc_search_input.setPlaceholderText("Search Items")
        search_layout.addWidget(self.misc_search_input)

        self.misc_sort_combo = QtWidgets.QComboBox()
        self.misc_sort_combo.addItems(['Name', 'Value', 'Weight'])
        search_layout.addWidget(self.misc_sort_combo)

        # Table View
        self.misc_table = QtWidgets.QTableView()
        self.misc_model = QtGui.QStandardItemModel(0, 5)  # Increased to 5 columns
        self.misc_model.setHorizontalHeaderLabels(['Name', 'Value (gp)', 'Weight (lbs)', 'Bought from Shop', 'Description'])  # Added 'Description'

        self.misc_proxy_model = QtCore.QSortFilterProxyModel()
        self.misc_proxy_model.setSourceModel(self.misc_model)
        self.misc_proxy_model.setFilterKeyColumn(0)
        self.misc_table.setModel(self.misc_proxy_model)
        self.misc_table.setSortingEnabled(False)

        self.misc_search_input.textChanged.connect(self.misc_proxy_model.setFilterRegularExpression)
        self.misc_sort_combo.currentIndexChanged.connect(self.sort_misc_items)

        layout.addWidget(self.misc_table)

        # Remove Button
        remove_button = QtWidgets.QPushButton("Remove Selected")
        layout.addWidget(remove_button)
        remove_button.clicked.connect(self.remove_misc_item)

        # Description Display
        self.misc_description = QtWidgets.QTextEdit()
        self.misc_description.setReadOnly(True)
        layout.addWidget(self.misc_description)

        # Connect selection to description display
        self.misc_table.selectionModel().selectionChanged.connect(self.display_misc_description)
        
    def display_misc_description(self, selected, deselected):
        indexes = self.misc_table.selectionModel().selectedRows()
        if indexes:
            index = indexes[0]
            description_item = self.misc_model.item(index.row(), 4)  # Column 4 is Description
            description = description_item.text() if description_item else ''
            self.misc_description.setText(description)
        else:
            self.misc_description.clear() 
            
    def sort_misc_items(self):
        sort_key = self.misc_sort_combo.currentText()
        if sort_key == 'Name':
            column = 0
        elif sort_key == 'Value':
            column = 1
        elif sort_key == 'Weight':
            column = 2
        else:
            column = 0
        self.misc_table.sortByColumn(column, QtCore.Qt.AscendingOrder)    

    def create_gems_tab(self):
        """Create the Gems sub-tab."""
        self.gems_tab = QtWidgets.QWidget()
        self.inventory_tabs.addTab(self.gems_tab, "Gems")

        layout = QtWidgets.QVBoxLayout(self.gems_tab)

        input_layout = QtWidgets.QGridLayout()
        layout.addLayout(input_layout)

        gem_type_label = QtWidgets.QLabel("Gem Type:")
        input_layout.addWidget(gem_type_label, 0, 0)
        self.gem_type_combo = QtWidgets.QComboBox()
        gem_types = []
        for tier_name, gems in self.gems_data.items():
            match = re.match(r'(\d+)\s+GP\s+Gemstones', tier_name)
            if match:
                value_per_item = int(match.group(1))
                for gem in gems:
                    gem_display_name = f"{gem} ({value_per_item} GP)"
                    gem_types.append(gem_display_name)
        self.gem_type_combo.addItems(gem_types)
        input_layout.addWidget(self.gem_type_combo, 0, 1)

        gem_quantity_label = QtWidgets.QLabel("Quantity:")
        input_layout.addWidget(gem_quantity_label, 0, 2)
        self.gem_quantity_input = QtWidgets.QSpinBox()
        self.gem_quantity_input.setRange(1, 100000)
        self.gem_quantity_input.setValue(1)
        input_layout.addWidget(self.gem_quantity_input, 0, 3)

        add_button = QtWidgets.QPushButton("Add Gem")
        input_layout.addWidget(add_button, 0, 4)
        add_button.clicked.connect(self.add_gem_item)

        search_layout = QtWidgets.QHBoxLayout()
        layout.addLayout(search_layout)

        self.gem_search_input = QtWidgets.QLineEdit()
        self.gem_search_input.setPlaceholderText("Search Gems")
        search_layout.addWidget(self.gem_search_input)

        self.gem_sort_combo = QtWidgets.QComboBox()
        self.gem_sort_combo.addItems(['Type', 'Total Value', 'Weight'])
        search_layout.addWidget(self.gem_sort_combo)

        self.gem_table = QtWidgets.QTableView()
        self.gem_model = QtGui.QStandardItemModel(0, 5)  
        self.gem_model.setHorizontalHeaderLabels(['Type', 'Quantity', 'Total Value (gp)', 'Weight (lbs)', 'Bought from Shop']) 

        self.gem_proxy_model = QtCore.QSortFilterProxyModel()
        self.gem_proxy_model.setSourceModel(self.gem_model)
        self.gem_proxy_model.setFilterKeyColumn(0)  
        self.gem_table.setModel(self.gem_proxy_model)
        self.gem_table.setSortingEnabled(False)

        self.gem_search_input.textChanged.connect(self.gem_proxy_model.setFilterRegularExpression)
        self.gem_sort_combo.currentIndexChanged.connect(self.sort_gem_items)

        layout.addWidget(self.gem_table)

        remove_button = QtWidgets.QPushButton("Remove Selected")
        layout.addWidget(remove_button)
        remove_button.clicked.connect(self.remove_gem_item)
        
    def sort_gem_items(self):
        sort_key = self.gem_sort_combo.currentText()
        if sort_key == 'Type':
            column = 0
        elif sort_key == 'Total Value':
            column = 2
        elif sort_key == 'Weight':
            column = 3
        else:
            column = 0
        self.gem_table.sortByColumn(column, QtCore.Qt.AscendingOrder)    

    def create_art_tab(self):
        """Create the Art Objects sub-tab."""
        self.art_tab = QtWidgets.QWidget()
        self.inventory_tabs.addTab(self.art_tab, "Art Objects")

        layout = QtWidgets.QVBoxLayout(self.art_tab)

        input_layout = QtWidgets.QHBoxLayout()
        layout.addLayout(input_layout)

        self.art_name_input = QtWidgets.QLineEdit()
        self.art_name_input.setPlaceholderText("Art Object Name")
        input_layout.addWidget(self.art_name_input)

        self.art_value_input = QtWidgets.QDoubleSpinBox()
        self.art_value_input.setRange(0, 1000000)
        self.art_value_input.setPrefix("Value (gp): ")
        input_layout.addWidget(self.art_value_input)

        self.art_weight_input = QtWidgets.QDoubleSpinBox()
        self.art_weight_input.setRange(0, 1000000)
        self.art_weight_input.setPrefix("Weight (lbs): ")
        input_layout.addWidget(self.art_weight_input)

        self.art_desc_input = QtWidgets.QLineEdit()
        self.art_desc_input.setPlaceholderText("Description")
        input_layout.addWidget(self.art_desc_input)

        add_button = QtWidgets.QPushButton("Add Art Object")
        input_layout.addWidget(add_button)
        add_button.clicked.connect(self.add_art_item)

        search_layout = QtWidgets.QHBoxLayout()
        layout.addLayout(search_layout)

        self.art_search_input = QtWidgets.QLineEdit()
        self.art_search_input.setPlaceholderText("Search Art Objects")
        search_layout.addWidget(self.art_search_input)

        self.art_sort_combo = QtWidgets.QComboBox()
        self.art_sort_combo.addItems(['Name', 'Value', 'Weight'])
        search_layout.addWidget(self.art_sort_combo)

        self.art_table = QtWidgets.QTableView()
        self.art_model = QtGui.QStandardItemModel(0, 5)  # Increased column count to 5
        self.art_model.setHorizontalHeaderLabels(['Name', 'Value (gp)', 'Weight (lbs)', 'Description', 'Bought from Shop'])  # Added 'Description'

        self.art_proxy_model = QtCore.QSortFilterProxyModel()
        self.art_proxy_model.setSourceModel(self.art_model)
        self.art_proxy_model.setFilterKeyColumn(0)
        self.art_table.setModel(self.art_proxy_model)
        self.art_table.setSortingEnabled(False)

        self.art_search_input.textChanged.connect(self.art_proxy_model.setFilterRegularExpression)
        self.art_sort_combo.currentIndexChanged.connect(self.sort_art_items)

        layout.addWidget(self.art_table)

        remove_button = QtWidgets.QPushButton("Remove Selected")
        layout.addWidget(remove_button)
        remove_button.clicked.connect(self.remove_art_item)
        
        self.art_table.selectionModel().selectionChanged.connect(self.display_art_description)

        self.art_description = QtWidgets.QTextEdit()
        self.art_description.setReadOnly(True)
        layout.addWidget(self.art_description)
        
    def display_art_description(self, selected, deselected):
        indexes = self.art_table.selectionModel().selectedRows()
        if indexes:
            index = indexes[0]
            description = self.art_model.item(index.row(), 3).text()
            self.art_description.setText(description)
        else:
            self.art_description.clear()
        
    def sort_art_items(self):
        sort_key = self.art_sort_combo.currentText()
        if sort_key == 'Name':
            column = 0
        elif sort_key == 'Value':
            column = 1
        elif sort_key == 'Weight':
            column = 2
        else:
            column = 0
        self.art_table.sortByColumn(column, QtCore.Qt.AscendingOrder)    

    def create_magic_tab(self):
        """Create the Magic Items sub-tab."""
        self.magic_tab = QtWidgets.QWidget()
        self.inventory_tabs.addTab(self.magic_tab, "Magic Items")

        layout = QtWidgets.QVBoxLayout(self.magic_tab)

        input_layout = QtWidgets.QGridLayout()
        layout.addLayout(input_layout)

        self.magic_name_input = QtWidgets.QLineEdit()
        self.magic_name_input.setPlaceholderText("Magic Item Name")
        input_layout.addWidget(QtWidgets.QLabel("Name:"), 0, 0)
        input_layout.addWidget(self.magic_name_input, 0, 1)

        self.magic_rarity_combo = QtWidgets.QComboBox()
        self.magic_rarity_combo.addItems(['Common', 'Uncommon', 'Rare', 'Very Rare', 'Legendary'])
        input_layout.addWidget(QtWidgets.QLabel("Rarity:"), 0, 2)
        input_layout.addWidget(self.magic_rarity_combo, 0, 3)

        self.magic_attunement_checkbox = QtWidgets.QCheckBox("Requires Attunement")
        input_layout.addWidget(self.magic_attunement_checkbox, 0, 4)

        self.magic_value_input = QtWidgets.QDoubleSpinBox()
        self.magic_value_input.setRange(0, 1000000)
        self.magic_value_input.setPrefix("Value (gp): ")
        input_layout.addWidget(QtWidgets.QLabel("Value:"), 1, 0)
        input_layout.addWidget(self.magic_value_input, 1, 1)

        self.magic_weight_input = QtWidgets.QDoubleSpinBox()
        self.magic_weight_input.setRange(0, 1000000)
        self.magic_weight_input.setPrefix("Weight (lbs): ")
        input_layout.addWidget(QtWidgets.QLabel("Weight:"), 1, 2)
        input_layout.addWidget(self.magic_weight_input, 1, 3)

        self.magic_desc_input = QtWidgets.QLineEdit()
        self.magic_desc_input.setPlaceholderText("Description")
        input_layout.addWidget(QtWidgets.QLabel("Description:"), 2, 0)
        input_layout.addWidget(self.magic_desc_input, 2, 1, 1, 4)

        add_button = QtWidgets.QPushButton("Add Magic Item")
        input_layout.addWidget(add_button, 3, 0, 1, 5)
        add_button.clicked.connect(self.add_magic_item)

        search_layout = QtWidgets.QHBoxLayout()
        layout.addLayout(search_layout)

        self.magic_search_input = QtWidgets.QLineEdit()
        self.magic_search_input.setPlaceholderText("Search Magic Items")
        search_layout.addWidget(self.magic_search_input)

        self.magic_sort_combo = QtWidgets.QComboBox()
        self.magic_sort_combo.addItems(['Name', 'Rarity', 'Value', 'Weight'])
        search_layout.addWidget(self.magic_sort_combo)

        self.magic_table = QtWidgets.QTableView()
        self.magic_model = QtGui.QStandardItemModel(0, 6)  # Increased column count to 6
        self.magic_model.setHorizontalHeaderLabels(['Name', 'Rarity', 'Requires Attunement', 'Value (gp)', 'Weight (lbs)', 'Description', 'Bought from Shop'])  # Added 'Description'

        self.magic_proxy_model = QtCore.QSortFilterProxyModel()
        self.magic_proxy_model.setSourceModel(self.magic_model)
        self.magic_proxy_model.setFilterKeyColumn(0)
        self.magic_table.setModel(self.magic_proxy_model)
        self.magic_table.setSortingEnabled(False)

        self.magic_search_input.textChanged.connect(self.magic_proxy_model.setFilterRegularExpression)
        self.magic_sort_combo.currentIndexChanged.connect(self.sort_magic_items)

        layout.addWidget(self.magic_table)

        remove_button = QtWidgets.QPushButton("Remove Selected")
        layout.addWidget(remove_button)
        remove_button.clicked.connect(self.remove_magic_item)
        
        self.magic_table.selectionModel().selectionChanged.connect(self.display_magic_description)

        self.magic_description = QtWidgets.QTextEdit()
        self.magic_description.setReadOnly(True)
        layout.addWidget(self.magic_description)
        
    def display_magic_description(self, selected, deselected):
        indexes = self.magic_table.selectionModel().selectedRows()
        if indexes:
            index = indexes[0]
            description_item = self.magic_model.item(index.row(), 5)  # Column 5 is Description
            description = description_item.text() if description_item else ''
            self.magic_description.setText(description)
        else:
            self.magic_description.clear()

    def sort_magic_items(self):
        sort_key = self.magic_sort_combo.currentText()
        if sort_key == 'Name':
            column = 0
        elif sort_key == 'Rarity':
            column = 1
        elif sort_key == 'Value':
            column = 3
        elif sort_key == 'Weight':
            column = 4
        else:
            column = 0
        self.magic_table.sortByColumn(column, QtCore.Qt.AscendingOrder)

    def remove_item_from_inventory_by_name(self, category, name, bought_from_shop):
        if category == 'Weapons':
            for row in range(self.weapons_model.rowCount()):
                if (self.weapons_model.item(row, 0).text() == name and
                    self.weapons_model.item(row, 3).text() == ('Yes' if bought_from_shop else 'No')):
                    self.weapons_model.removeRow(row)
                    break
        elif category == 'Armor':
            for row in range(self.armor_model.rowCount()):
                if (self.armor_model.item(row, 0).text() == name and
                    self.armor_model.item(row, 3).text() == ('Yes' if bought_from_shop else 'No')):
                    self.armor_model.removeRow(row)
                    break
        elif category == 'Miscellaneous Items':
            for row in range(self.misc_model.rowCount()):
                if (self.misc_model.item(row, 0).text() == name and
                    self.misc_model.item(row, 3).text() == ('Yes' if bought_from_shop else 'No')):
                    self.misc_model.removeRow(row)
                    break
        elif category == 'Gems':
            for row in range(self.gem_model.rowCount()):
                if (self.gem_model.item(row, 0).text() == name and
                    self.gem_model.item(row, 4).text() == ('Yes' if bought_from_shop else 'No')):
                    quantity = int(self.gem_model.item(row, 1).text())
                    if quantity > 1:
                        current_total = Decimal(self.gem_model.item(row, 2).text())
                        value_per_item = current_total / quantity
                        new_total = current_total - value_per_item
                        self.gem_model.setItem(row, 1, QtGui.QStandardItem(str(quantity - 1)))
                        self.gem_model.setItem(row, 2, QtGui.QStandardItem(str(new_total)))
                    else:
                        self.gem_model.removeRow(row)
                    break
        elif category == 'Art Objects':
            for row in range(self.art_model.rowCount()):
                if self.art_model.item(row, 0).text() == name and self.art_model.item(row, 3).text() == ('Yes' if bought_from_shop else 'No'):
                    self.art_model.removeRow(row)
                    break
        elif category == 'Magic Items':
            for row in range(self.magic_model.rowCount()):
                if self.magic_model.item(row, 0).text() == name and self.magic_model.item(row, 5).text() == ('Yes' if bought_from_shop else 'No'):
                    self.magic_model.removeRow(row)
                    break

    def add_item_back_to_inventory(self, category, name, sell_price):
        if category == 'Miscellaneous Items':
            self.misc_model.appendRow([
                QtGui.QStandardItem(name),
                QtGui.QStandardItem(str(sell_price)),
                QtGui.QStandardItem("0"), 
                QtGui.QStandardItem('Yes')
            ])
        elif category == 'Gems':
            self.gem_model.appendRow([
                QtGui.QStandardItem(name),
                QtGui.QStandardItem("1"),
                QtGui.QStandardItem(str(sell_price)),
                QtGui.QStandardItem("0.01"),
                QtGui.QStandardItem('Yes')
            ])
        elif category == 'Art Objects':
            self.art_model.appendRow([
                QtGui.QStandardItem(name),
                QtGui.QStandardItem(str(sell_price)),
                QtGui.QStandardItem("1"),  
                QtGui.QStandardItem('Yes')
            ])
        elif category == 'Magic Items':
            self.magic_model.appendRow([
                QtGui.QStandardItem(name),
                QtGui.QStandardItem('Unknown'),  
                QtGui.QStandardItem('Yes'),
                QtGui.QStandardItem(str(sell_price)),
                QtGui.QStandardItem("0"),  
                QtGui.QStandardItem('Yes')
            ])

    def create_treasure_tab(self):
        """Create the Treasure Generator tab."""
        self.treasure_tab = QtWidgets.QWidget()
        self.tabs.addTab(self.treasure_tab, "Treasure Generator")

        layout = QtWidgets.QVBoxLayout(self.treasure_tab)

        cr_layout = QtWidgets.QHBoxLayout()
        layout.addLayout(cr_layout)

        cr_label = QtWidgets.QLabel("Challenge Rating:")
        cr_layout.addWidget(cr_label)

        self.cr_input = QtWidgets.QComboBox()
        self.cr_input.addItems(['0-4', '5-10', '11-16', '17+'])
        cr_layout.addWidget(self.cr_input)

        treasure_type_label = QtWidgets.QLabel("Treasure Type:")
        cr_layout.addWidget(treasure_type_label)

        self.treasure_type_combo = QtWidgets.QComboBox()
        self.treasure_type_combo.addItems(['Individual', 'Hoard'])
        cr_layout.addWidget(self.treasure_type_combo)

        generate_button = QtWidgets.QPushButton("Generate Treasure")
        cr_layout.addWidget(generate_button)
        generate_button.clicked.connect(self.on_generate)

        self.send_to_party_checkbox = QtWidgets.QCheckBox("Send to Party Distribution")
        cr_layout.addWidget(self.send_to_party_checkbox)

        self.treasure_output = QtWidgets.QTextEdit()
        self.treasure_output.setReadOnly(True)
        layout.addWidget(self.treasure_output)

        add_to_inventory_button = QtWidgets.QPushButton("Add to Inventory")
        layout.addWidget(add_to_inventory_button)
        add_to_inventory_button.clicked.connect(self.add_treasure_to_inventory)

    def create_dice_rolls_tab(self):
        """Create the Dice Rolls tab."""
        self.dice_rolls_tab = QtWidgets.QWidget()
        self.tabs.addTab(self.dice_rolls_tab, "Dice Rolls")

        layout = QtWidgets.QVBoxLayout(self.dice_rolls_tab)

        self.dice_roll_list = QtWidgets.QListWidget()
        layout.addWidget(self.dice_roll_list)

        clear_button = QtWidgets.QPushButton("Clear")
        clear_button.clicked.connect(self.clear_dice_rolls)
        layout.addWidget(clear_button)
        
    def clear_dice_rolls(self):
        self.dice_rolls.clear()
        self.update_dice_roll_list()
        self.generation_counter = 0

    def create_party_distribution_tab(self):
        """Create the Party Distribution tab."""
        self.party_tab = QtWidgets.QWidget()
        self.tabs.addTab(self.party_tab, "Party Distribution")

        layout = QtWidgets.QVBoxLayout(self.party_tab)

        member_layout = QtWidgets.QHBoxLayout()
        layout.addLayout(member_layout)

        member_count_label = QtWidgets.QLabel("Number of Members:")
        member_layout.addWidget(member_count_label)

        self.member_count_input = QtWidgets.QSpinBox()
        self.member_count_input.setRange(1, 10)
        member_layout.addWidget(self.member_count_input)
        self.member_count_input.valueChanged.connect(self.update_member_inputs)

        self.member_inputs_layout = QtWidgets.QVBoxLayout()
        layout.addLayout(self.member_inputs_layout)

        method_layout = QtWidgets.QHBoxLayout()
        layout.addLayout(method_layout)

        method_label = QtWidgets.QLabel("Distribution Method:")
        method_layout.addWidget(method_label)

        self.distribution_method_combo = QtWidgets.QComboBox()
        self.distribution_method_combo.addItems([
            "Random Extra",
            "Split into Smaller Denominations"
        ])
        method_layout.addWidget(self.distribution_method_combo)

        distribute_button = QtWidgets.QPushButton("Distribute Loot")
        layout.addWidget(distribute_button)
        distribute_button.clicked.connect(self.distribute_loot)

        self.distribution_results = QtWidgets.QTextEdit()
        self.distribution_results.setReadOnly(True)
        layout.addWidget(self.distribution_results)

        self.update_member_inputs()

    def update_member_inputs(self):
        for i in reversed(range(self.member_inputs_layout.count())):
            widget = self.member_inputs_layout.takeAt(i).widget()
            if widget is not None:
                widget.setParent(None)

        num_members = self.member_count_input.value()
        self.member_inputs = []
        for i in range(num_members):
            member_input = QtWidgets.QLineEdit()
            member_input.setPlaceholderText(f"Member {i + 1} Name")
            self.member_inputs_layout.addWidget(member_input)
            self.member_inputs.append(member_input)

    def create_settings_tab(self):
        """Create the Settings tab."""
        self.settings_tab = QtWidgets.QWidget()
        self.tabs.addTab(self.settings_tab, "Settings")

        layout = QtWidgets.QFormLayout(self.settings_tab)

        self.carrying_capacity_input = QtWidgets.QDoubleSpinBox()
        self.carrying_capacity_input.setRange(0, 100000)
        self.carrying_capacity_input.setSuffix(" lbs")
        self.carrying_capacity_input.valueChanged.connect(self.update_carrying_capacity)
        layout.addRow("Carrying Capacity:", self.carrying_capacity_input)

        self.default_save_location = QtWidgets.QLineEdit()
        browse_button = QtWidgets.QPushButton("Browse")
        browse_button.clicked.connect(self.browse_save_location) 
        save_location_layout = QtWidgets.QHBoxLayout()
        save_location_layout.addWidget(self.default_save_location)
        save_location_layout.addWidget(browse_button)
        layout.addRow("Default Save Location:", save_location_layout)

        self.currency_customization_button = QtWidgets.QPushButton("Customize Currency Rates")
        self.currency_customization_button.clicked.connect(self.customize_currency_rates)  
        layout.addRow("Currency Customization:", self.currency_customization_button)
        
    def update_carrying_capacity(self, value):
        self.carrying_capacity = Decimal(value)    

    def browse_save_location(self):
        options = QtWidgets.QFileDialog.Options()
        directory = QtWidgets.QFileDialog.getExistingDirectory(self, "Select Default Save Location", options=options)
        if directory:
            self.default_save_location.setText(directory)

    def customize_currency_rates(self):
        dialog = CurrencyCustomizationDialog(self)
        if dialog.exec_():
            self.conversion_rates = dialog.get_conversion_rates()
            for currency in Currency:
                self.convert_currency(currency.value)

    def get_currency_value_in_gp(self, currency):
        if currency == Currency.GP:
            return Decimal('1')
        else:
            rate = self.get_conversion_rate(currency.value, 'gp')
            if rate:
                return Decimal(rate)
            else:
                conversion_rates_to_gp = {
                    'cp': Decimal('0.01'),
                    'sp': Decimal('0.1'),
                    'ep': Decimal('0.5'),
                    'gp': Decimal('1'),
                    'pp': Decimal('10'),
                }
                return conversion_rates_to_gp.get(currency.value, Decimal('0'))

    def create_help_tab(self):
        """Create the Help tab."""
        self.help_tab = QtWidgets.QWidget()
        self.tabs.addTab(self.help_tab, "Help")

        layout = QtWidgets.QVBoxLayout(self.help_tab)
        scroll_area = QtWidgets.QScrollArea()
        scroll_area.setWidgetResizable(True)
        content_widget = QtWidgets.QWidget()
        scroll_area.setWidget(content_widget)
        content_layout = QtWidgets.QVBoxLayout(content_widget)

        help_text = QtWidgets.QLabel("""
        <h2>D&D Wealth Manager Help</h2>
        <p>Welcome to the D&D Wealth Manager! Here's how to use the application:</p>
        <ul>
            <li><b>Currency:</b> Manage your coins here - add your currency holdings, and convert using the currency converter.</li>
            <li><b>Inventory:</b> Manage different types of items, including adding custom items by using the editable fields (name, value, weight, description). To select an item, for example to show its description, click on the number next to the item.</li>
            <li><b>Treasure Generator:</b> Generate random treasure based on Challenge Rating (CR). First, select the Challenge Rating, then select Treasure Type (Individual or Hoard), and click on Generate Treasure. To send the treasure to the Party Distribution tab, check the "Send to Party Distribution" box before generating. Clicking on Add to Inventory at the bottom of the screen will send all the generated treasure and currency to your inventory and currency tab; this will not work for Party Distribution.</li>
            <li><b>Dice Rolls:</b> View the history of all your dice rolls - Treasure Generator and Party Distribution.</li>
            <li><b>Settings:</b> Adjust application settings, including customization of currency exchange rates, setting up the weight limit (to keep the carrying capacity limitless, do not set it), and the location of your saved profiles.</li>
            <li><b>Shop:</b> Buy and sell on the go using your currency holdings. The shop function only works if there is an internet connection. Type in the name of the item you wish to buy in the search field and click search - the item will appear below. The Shop Sell Rate is adjustable. To sell an item, select the category in the inventory, then select the item you wish to sell from the list below. To select an item to buy or sell, click on the number next to the item. Your currency holdings will automatically change after the transaction. Current Holdings displays your current coins, not the total wealth (the total wealth can be found in the Inventory section).</li>
            <li><b>Party Distribution:</b> After sending generated treasure to party distribution, use this tab to split the loot. Select the number of members, use the name fields to add the members' names, and then select the Distribution Method - Random Extra will randomly distribute the excess loot, while Split into Smaller Denominations will guarantee an equal split among all the party members. After selecting your method of choice, click on Distribute Loot.</li>
            <li><b>Help:</b> Access this help guide.</li>
        </ul>
        """)
        help_text.setWordWrap(True)
        help_text.setAlignment(QtCore.Qt.AlignTop)
        content_layout.addWidget(help_text)
        layout.addWidget(scroll_area)

    def roll_dice(self, number, sides, note=''):
        rolls = [random.randint(1, sides) for _ in range(number)]
        total = sum(rolls)

        roll_str = f"Rolled {number}d{sides}: {rolls} = {total}"
        if note:
            roll_str += f" ({note})"
        self.dice_rolls.append(roll_str)

        if hasattr(self, 'dice_roll_list'):
            self.update_dice_roll_list()
        return total

    def validate_json_data(self, magic_item_tables, base_items, gems, art_objects):
        for table in [f"Magic Item Table {chr(i)}" for i in range(65, 74)]:
            if table not in magic_item_tables:
                logging.error(f"{table} is missing from base-item-tables.json.")
                QtWidgets.QMessageBox.critical(self, "Error", f"{table} is missing from base-item-tables.json.")
                return False

        for table, items in magic_item_tables.items():
            for item in items:
                if item['id'] not in base_items:
                    logging.error(f"Item '{item['id']}' from {table} is missing in base-items.json.")
                    QtWidgets.QMessageBox.critical(self, "Error", f"Item '{item['id']}' from {table} is missing in base-items.json.")
                    return False

        required_gem_tiers = ['10 GP Gemstones', '50 GP Gemstones', '100 GP Gemstones',
                              '500 GP Gemstones', '1000 GP Gemstones', '5000 GP Gemstones']
        for tier in required_gem_tiers:
            if tier not in gems:
                logging.error(f"Gem tier '{tier}' is missing from gems.json.")
                QtWidgets.QMessageBox.critical(self, "Error", f"Gem tier '{tier}' is missing from gems.json.")
                return False

        required_art_tiers = ['25 GP Art Objects', '250 GP Art Objects', '750 GP Art Objects',
                              '2500 GP Art Objects', '7500 GP Art Objects']
        for tier in required_art_tiers:
            if tier not in art_objects:
                logging.error(f"Art object tier '{tier}' is missing from art_objects.json.")
                QtWidgets.QMessageBox.critical(self, "Error", f"Art object tier '{tier}' is missing from art_objects.json.")
                return False

        gem_tiers = ['10 GP Gemstones', '50 GP Gemstones', '100 GP Gemstones',
                     '500 GP Gemstones', '1000 GP Gemstones', '5000 GP Gemstones']
        all_gems = set()
        for tier in gem_tiers:
            gems_in_tier = gems.get(tier, [])
            duplicates = set(gems_in_tier) & all_gems
            if duplicates:
                logging.error(f"Duplicate gems found across tiers: {duplicates}")
                QtWidgets.QMessageBox.critical(self, "Error", f"Duplicate gems found across tiers: {duplicates}")
                return False
            all_gems.update(gems_in_tier)

        art_tiers = ['25 GP Art Objects', '250 GP Art Objects', '750 GP Art Objects',
                    '2500 GP Art Objects', '7500 GP Art Objects']
        all_art = set()
        for tier in art_tiers:
            art_in_tier = art_objects.get(tier, [])
            duplicates = set(art_in_tier) & all_art
            if duplicates:
                logging.error(f"Duplicate art objects found across tiers: {duplicates}")
                QtWidgets.QMessageBox.critical(self, "Error", f"Duplicate art objects found across tiers: {duplicates}")
                return False
            all_art.update(art_in_tier)

        for item_name, details in base_items.items():
            required_fields = ['id', 'type', 'rarity']
            for field in required_fields:
                if field not in details:
                    logging.error(f"Field '{field}' missing for item '{item_name}' in base-items.json.")
                    QtWidgets.QMessageBox.critical(self, "Error", f"Field '{field}' missing for item '{item_name}' in base-items.json.")
                    return False

        return True

    def parse_expression(self, expr, default_category=None):
        if not expr or expr.strip() in ['–', '-', '']:
            return None
        expr = expr.strip().lower()

        parts = re.split(r'\s*\+\s*', expr)
        results = []

        for part in parts:
            part = part.strip()
            if not part or part in ['–', '-', '']:
                continue

            match_multiplier = re.match(r'^(\d+)d(\d+)\s*[*x×]\s*(\d+)\s*(cp|sp|ep|gp|pp)?$', part)
            if match_multiplier:
                num, die, multiplier, coin_type = match_multiplier.groups()
                dice_total = self.roll_dice(int(num), int(die), note=f"{num}d{die} x {multiplier}")
                total = dice_total * int(multiplier)
                category = coin_type.upper() if coin_type else (default_category.upper() if default_category else None)
                if category is None:
                    logging.warning(f"Coin type not specified for expression part: '{part}' and no default category provided.")
                    continue
                results.append({
                    'total': total,
                    'category': category
                })
                continue

            match_l = re.match(r'^(\d+)d(\d+)\s*l(\d+)\s*(gp|sp|cp|ep|pp)?\s*(gems|art objects)?$', part)
            if match_l:
                num, die, value_per_item, coin_type, category_type = match_l.groups()
                count = self.roll_dice(int(num), int(die), note=f"{num}d{die} l{value_per_item} {coin_type if coin_type else ''} {category_type if category_type else ''}".strip())
                value_per_item = int(value_per_item)
                if category_type:
                    category = category_type.lower()
                elif coin_type:
                    category = 'gems' if coin_type.lower() == 'gp' else None
                else:
                    category = default_category.lower() if default_category else None
                if not category:
                    logging.warning(f"Category not specified for expression part: '{part}'.")
                    continue
                results.append({
                    'count': count,
                    'value_per_item': value_per_item,
                    'category': category
                })
                continue

            match_simple = re.match(r'^(\d+)d(\d+)$', part)
            if match_simple:
                num, die = match_simple.groups()
                total = self.roll_dice(int(num), int(die), note=part)
                if default_category:
                    results.append({
                        'total': total,
                        'category': default_category.upper()
                    })
                else:
                    logging.warning(f"No default category provided for simple dice roll: '{part}'.")
                continue

            match_fixed = re.match(r'^(\d+)\s*(cp|sp|ep|gp|pp)?$', part)
            if match_fixed:
                fixed_amount, coin_type = match_fixed.groups()
                if not fixed_amount:
                    logging.warning(f"No fixed amount found in expression part: '{part}'.")
                    continue
                fixed_amount = int(fixed_amount)
                category = coin_type.upper() if coin_type else (default_category.upper() if default_category else None)
                if category is None:
                    logging.warning(f"Coin type not specified for fixed amount part: '{part}' and no default category provided.")
                    continue
                results.append({
                    'total': fixed_amount,
                    'category': category
                })
                continue

            logging.warning(f"Unrecognized expression part: '{part}'")

        return results if len(results) > 1 else (results[0] if results else None)

    def weighted_choice(self, items, table_name):
        total_weight = sum(item['weight'] for item in items)
        cumulative_weights = []
        cumsum = 0
        for item in items:
            cumsum += item['weight']
            cumulative_weights.append(cumsum)
        die_size = total_weight
        roll = self.roll_dice(1, die_size, note=f"Rolling on {table_name}")
        for item, cum_weight in zip(items, cumulative_weights):
            if roll <= cum_weight:
                return item['id']
        return items[-1]['id']

    def load_json(self, file_name, required_keys=None):
        try:
            with open(file_name, 'r') as f:
                data = json.load(f)
            if required_keys:
                for key in required_keys:
                    if key not in data:
                        QtWidgets.QMessageBox.warning(self, "Warning", f"Key '{key}' not found in {file_name}.")
                        logging.warning(f"Key '{key}' not found in {file_name}.")
            return data
        except FileNotFoundError:
            QtWidgets.QMessageBox.critical(self, "Error", f"File not found: {file_name}")
            logging.error(f"File not found: {file_name}")
            return {}
        except json.JSONDecodeError as e:
            QtWidgets.QMessageBox.critical(self, "Error", f"Invalid JSON format in {file_name}: {e}")
            logging.error(f"Invalid JSON format in {file_name}: {e}")
            return {}

    def generate_magic_items(self, magic_items_instructions):
        generated_magic_items = []
        rarities = ['Common', 'Uncommon', 'Rare', 'Very Rare', 'Legendary']
        weights = [self.magic_item_rarity_distribution.get(rarity, 0) for rarity in rarities]
        total_weight = sum(weights)
        if total_weight == 0:
            QtWidgets.QMessageBox.warning(self, "Warning", "Magic Item Rarity Distribution sums to zero.")
            return generated_magic_items
        cumulative_weights = []
        cumsum = 0
        for weight in weights:
            cumsum += weight
            cumulative_weights.append(cumsum / total_weight)
        instructions = magic_items_instructions.split('and')
        for instruction in instructions:
            instruction = instruction.strip()
            mi_matches = re.findall(r'(?:Roll\s+)?(\d+)d(\d+)\s*times\s*on\s*Magic Item Table\s*([A-I])', instruction, re.IGNORECASE)
            for num, die, table_letter in mi_matches:
                times = self.roll_dice(int(num), int(die), note=f"{num}d{die} times on Magic Item Table {table_letter.upper()}")
                for _ in range(times):
                    rand = random.random()
                    for rarity, cumulative_weight in zip(rarities, cumulative_weights):
                        if rand <= cumulative_weight:
                            selected_rarity = rarity
                            break
                    table_items = [
                        item for item in self.magic_item_tables.get(f"Magic Item Table {table_letter.upper()}", [])
                        if self.base_items.get(item['id'], {}).get('rarity', '') == selected_rarity
                    ]
                    if not table_items:
                        table_items = self.magic_item_tables.get(f"Magic Item Table {table_letter.upper()}", [])
                    if not table_items:
                        QtWidgets.QMessageBox.warning(self, "Warning", f"No items found in Magic Item Table {table_letter.upper()}.")
                        continue
                    item_id = self.weighted_choice(table_items, f"Magic Item Table {table_letter.upper()}")
                    item = self.base_items.get(item_id, {}).get('id', item_id)
                    item = self.generate_special_magic_items(item)
                    generated_magic_items.append(item)
            single_roll_match = re.findall(r'(?:Roll\s+)?once\s*on\s*Magic Item Table\s*([A-I])', instruction, re.IGNORECASE)
            for table_letter in single_roll_match:
                table_letter = table_letter.upper()
                logging.debug(f"Rolling once on Magic Item Table {table_letter}")
                table = self.magic_item_tables.get(f"Magic Item Table {table_letter}", [])
                if not table:
                    QtWidgets.QMessageBox.warning(self, "Warning", f"Magic Item Table {table_letter.upper()} not found.")
                    logging.warning(f"Magic Item Table {table_letter.upper()} not found.")
                    continue
                item_id = self.weighted_choice(table, f"Magic Item Table {table_letter}")
                logging.debug(f"Selected Magic Item: {item_id} from Table {table_letter.upper()}")
                item = self.base_items.get(item_id, {}).get('id', item_id)
                item = self.generate_special_magic_items(item)
                generated_magic_items.append(item)
            if not mi_matches and not single_roll_match:
                QtWidgets.QMessageBox.warning(self, "Warning", f"Unrecognized magic item instruction: '{instruction}'")
                logging.warning(f"Unrecognized magic item instruction: '{instruction}'")
        return generated_magic_items

    def generate_complete_treasure(self, treasure_type, cr_level):
        treasure = {
            'Coins': {},
            'Gems': [],         
            'Art Objects': [],  
            'Magic Items': []
        }
        if treasure_type == 'Individual':
            cr_key = cr_level
            table = self.treasure_tables['Individual'].get(cr_key)
            if not table:
                QtWidgets.QMessageBox.critical(self, "Error", f"No treasure table for CR {cr_level}")
                return
            d100_roll = self.roll_dice(1, 100, note='Treasure Table Roll')
            for range_key, rewards in table['d100'].items():
                if '00' in range_key:
                    range_key = range_key.replace('00', '100')
                start, end = map(int, range_key.split('-'))
                if start <= d100_roll <= end:
                    for coin_type, expr in rewards.items():
                        if expr and expr not in ['–', '-', '']:
                            parsed = self.parse_expression(expr, default_category=coin_type)
                            if parsed:
                                if isinstance(parsed, list):
                                    for item in parsed:
                                        if 'total' in item and 'category' in item:
                                            treasure['Coins'][item['category'].lower()] = treasure['Coins'].get(item['category'].lower(), 0) + item['total']
                                else:
                                    if 'total' in parsed and 'category' in parsed:
                                        treasure['Coins'][parsed['category']] = treasure['Coins'].get(parsed['category'], 0) + parsed['total']
                    break
        elif treasure_type == 'Hoard':
            cr_key = cr_level
            table = self.treasure_tables['Hoard'].get(cr_key)
            if not table:
                QtWidgets.QMessageBox.critical(self, "Error", f"No treasure table for CR {cr_level}")
                return
            for coin_type, expr in table['Coins'].items():
                if expr and expr not in ['–', '-', '']:
                    parsed = self.parse_expression(expr, default_category=coin_type)
                    if parsed:
                        if isinstance(parsed, list):
                            for item in parsed:
                                if 'total' in item and 'category' in item:
                                    treasure['Coins'][item['category'].lower()] = treasure['Coins'].get(item['category'].lower(), 0) + item['total']
                                elif 'count' in item and 'value_per_item' in item:
                                    if item['category'] == 'gems':
                                        gems_generated = self.generate_gems(count=item['count'], value_per_item=item['value_per_item'])
                                        treasure['Gems'].extend(gems_generated)
                                    elif item['category'] == 'art objects':
                                        arts_generated = self.generate_art_objects(count=item['count'], value_per_item=item['value_per_item'])
                                        treasure['Art Objects'].extend(arts_generated)
                        else:
                            if 'total' in parsed and 'category' in parsed:
                                treasure['Coins'][parsed['category']] = treasure['Coins'].get(parsed['category'], 0) + parsed['total']
                            elif 'count' in parsed and 'value_per_item' in parsed:
                                if parsed['category'] == 'gems':
                                    gems_generated = self.generate_gems(count=parsed['count'], value_per_item=parsed['value_per_item'])
                                    treasure['Gems'].extend(gems_generated)
                                elif parsed['category'] == 'art objects':
                                    arts_generated = self.generate_art_objects(count=parsed['count'], value_per_item=parsed['value_per_item'])
                                    treasure['Art Objects'].extend(arts_generated)
            d100_roll = self.roll_dice(1, 100)
            for range_key, rewards in table['d100'].items():
                if '00' in range_key:
                    range_key = range_key.replace('00', '100')
                start, end = map(int, range_key.split('-'))
                if start <= d100_roll <= end:
                    gems_art = rewards.get('Gems/Art')
                    magic_items = rewards.get('Magic Items')
                    if gems_art and gems_art != '–':
                        parsed = self.parse_expression(gems_art, default_category='gems')
                        if parsed:
                            if isinstance(parsed, list):
                                for item in parsed:
                                    if 'count' in item and 'value_per_item' in item and 'category' in item:
                                        count = item['count']
                                        value_per_item = item['value_per_item']
                                        category = item['category']
                                        if category == 'gems':
                                            gems_generated = self.generate_gems(count=count, value_per_item=value_per_item)
                                            treasure['Gems'].extend(gems_generated)
                                        elif category == 'art objects':
                                            arts_generated = self.generate_art_objects(count=count, value_per_item=value_per_item)
                                            treasure['Art Objects'].extend(arts_generated)
                            else:
                                if 'count' in parsed and 'value_per_item' in parsed and 'category' in parsed:
                                    count = parsed['count']
                                    value_per_item = parsed['value_per_item']
                                    category = parsed['category']
                                    if category == 'gems':
                                        gems_generated = self.generate_gems(count=count, value_per_item=value_per_item)
                                        treasure['Gems'].extend(gems_generated)
                                    elif category == 'art objects':
                                        arts_generated = self.generate_art_objects(count=count, value_per_item=value_per_item)
                                        treasure['Art Objects'].extend(arts_generated)
                    if magic_items and magic_items != '–':
                        magic_items_generated = self.generate_magic_items(magic_items)
                        treasure['Magic Items'].extend(magic_items_generated)
                    break
        return treasure

    def generate_special_magic_items(self, item_name):
        if 'figurine of wondrous power' in item_name.lower():
            figurine_types = [
                "Bronze Griffon",
                "Ebony Fly",
                "Golden Lions",
                "Ivory Goats",
                "Marble Elephant",
                "Onyx Dog",
                "Serpentine Owl"
            ]
            sub_roll = self.roll_dice(1, len(figurine_types))
            selected_figurine = figurine_types[sub_roll - 1] if sub_roll <= len(figurine_types) else "Unknown Figurine"
            return f"{item_name} ({selected_figurine})"

        elif 'deck of many things' in item_name.lower():
            outcomes = [
                "The Void", "Donjon", "Flames", "Fates", "Fool", "Gem", "Idiot",
                "Jester", "Moon", "Rogue", "Ruination", "Star", "Throne",
                "Sun", "Talons"
            ]
            selected_outcome = random.choice(outcomes)
            return f"{item_name} (Outcome: {selected_outcome})"
         
        elif 'portable hole' in item_name.lower():
            return f"{item_name} (Generates extra space for storage)" 

        elif 'bag of tricks' in item_name.lower():
            bag_types = ['Gray', 'Rust', 'Tan']
            selected_type = random.choice(bag_types)
            return f"{item_name} ({selected_type} type)"
        elif 'robe of the archmagi' in item_name.lower():
            return f"{item_name} (Provides magical protection and enhances spellcasting)"
        elif 'wand of polymorph' in item_name.lower():
            return f"{item_name} (Transmutes creatures and objects)"
        elif 'rod of lordly might' in item_name.lower():
            powers = [
                "Extra attack", "Summon Elemental", "Control Weather",
                "Fly", "Invisibility", "Teleport"
            ]
            selected_power = random.choice(powers)
            return f"{item_name} (Ability: {selected_power})"
        elif 'tome of clear thought' in item_name.lower():
            return f"{item_name} (Increases Intelligence by 2 permanently)"
        elif 'tome of leadership and influence' in item_name.lower():
            return f"{item_name} (Increases Charisma by 2 permanently)"
        elif 'tome of understanding' in item_name.lower():
            return f"{item_name} (Increases Wisdom by 2 permanently)"
        elif 'sphere of annihilation' in item_name.lower():
            return f"{item_name} (Annihilates matter on contact)"
        elif 'well of many worlds' in item_name.lower():
            return f"{item_name} (Creates portals to other planes)"
        elif re.match(r'magic armor\s*\(roll\s*d(\d+)\)', item_name, re.IGNORECASE):
            match = re.match(r'magic armor\s*\(roll\s*d(\d+)\)', item_name, re.IGNORECASE)
            die = int(match.group(1))
            roll = self.roll_dice(1, die)
            armor_types = {
                1: "Armor, +2 Half Plate",
                2: "Armor, +2 Plate",
                3: "Armor, +3 Studded Leather",
                4: "Armor, +3 Breastplate",
                5: "Armor, +3 Splint",
                6: "Armor, +3 Half Plate",
                7: "Armor, +3 Plate",
                8: "Armor, +2 Chain Mail",
                9: "Armor, +2 Chain Shirt",
                10: "Armor, +3 Chain Mail",
                11: "Armor, +3 Chain Shirt",
                12: "Armor, +3 Scale Mail"
            }
            selected_armor = armor_types.get(roll, "Unknown Magic Armor")
            return f"{selected_armor} (Magic Armor)"
        else:
            return item_name

    def generate_gems(self, count, value_per_item):
        generated_gems = []
        if value_per_item >= 5000:
            tier_name = '5000 GP Gemstones'
        elif value_per_item >= 1000:
            tier_name = '1000 GP Gemstones'
        elif value_per_item >= 500:
            tier_name = '500 GP Gemstones'
        elif value_per_item >= 100:
            tier_name = '100 GP Gemstones'
        elif value_per_item >= 50:
            tier_name = '50 GP Gemstones'
        elif value_per_item >= 10:
            tier_name = '10 GP Gemstones'
        else:
            logging.error(f"Invalid gem value per item: {value_per_item} GP.")
            return generated_gems

        available_gems = self.gems_data.get(tier_name, [])
        if not available_gems:
            logging.error(f"No gems found for tier '{tier_name}'.")
            return generated_gems

        gem_weight_per_item = Decimal('0.01')
        for _ in range(count):
            gem = random.choice(available_gems)
            generated_gems.append({
                'Name': f"{gem} ({value_per_item} GP)",
                'Value': value_per_item,
                'Weight': gem_weight_per_item
            })
        return generated_gems

    def generate_art_objects(self, count, value_per_item):
        generated_art = []
        if value_per_item >= 7500:
            tier_name = '7500 GP Art Objects'
        elif value_per_item >= 2500:
            tier_name = '2500 GP Art Objects'
        elif value_per_item >= 750:
            tier_name = '750 GP Art Objects'
        elif value_per_item >= 250:
            tier_name = '250 GP Art Objects'
        elif value_per_item >= 25:
            tier_name = '25 GP Art Objects'
        else:
            logging.error(f"Invalid art object value per item: {value_per_item} GP.")
            return generated_art

        available_art = self.art_objects_data.get(tier_name, [])
        if not available_art:
            logging.error(f"No art objects found for tier '{tier_name}'.")
            return generated_art

        art_weight_per_item = Decimal('1')
        for _ in range(count):
            art = random.choice(available_art)
            generated_art.append({
                'Name': f"{art} ({value_per_item} GP)",
                'Value': value_per_item,
                'Weight': art_weight_per_item
            })
        return generated_art

    def select_magic_items(self, magic_items):
        selected = []
        for item in magic_items:
            details = self.base_items.get(item)
            if not details:
                selected.append(f"{item} (Details not found)")
                continue
            item_description = f"{details.get('id', item)} (Type: {details.get('type', 'Unknown')}, Rarity: {details.get('rarity', 'Unknown')})"
            additional_details = details.get('additional_info')
            if additional_details:
                item_description += f", {additional_details}"
            selected.append(item_description)
        return selected

    def on_generate(self):
        self.generation_counter += 1
        separator = f"=======({self.generation_counter})======="
        self.dice_rolls.append(separator)
        self.update_dice_roll_list()
        treasure_type = self.treasure_type_combo.currentText()
        treasure_type = treasure_type.capitalize()
        cr_key = self.cr_input.currentText()
        if not treasure_type or not cr_key:
            QtWidgets.QMessageBox.critical(self, "Error", "Please select both Treasure Type and CR Level.")
            return
        treasure = self.generate_complete_treasure(treasure_type, cr_key)
        if not treasure:
            return
        self.treasure_output.clear()
        if treasure['Coins']:
            self.treasure_output.append("=== Coins ===")
            for coin, amount in treasure['Coins'].items():
                self.treasure_output.append(f"- {coin}: {amount}")
        if treasure['Gems']:
            self.treasure_output.append("\n=== Gems ===")
            gem_counter = Counter([gem['Name'] for gem in treasure['Gems']])
            for gem_name, count in gem_counter.items():
                self.treasure_output.append(f"- {gem_name}: {count}")
        if treasure['Art Objects']:
            self.treasure_output.append("\n=== Art Objects ===")
            art_counter = Counter([art['Name'] for art in treasure['Art Objects']])
            for art_name, count in art_counter.items():
                self.treasure_output.append(f"- {art_name}: {count}")
        if treasure['Magic Items']:
            self.treasure_output.append("\n=== Magic Items ===")
            magic_details = self.select_magic_items(treasure['Magic Items'])
            magic_counter = Counter(magic_details)
            for mi, count in magic_counter.items():
                self.treasure_output.append(f"- {mi} x{count}")

        self.treasure = treasure

        if self.send_to_party_checkbox.isChecked():
            self.add_treasure_to_party(treasure)
            
    def add_treasure_to_inventory(self):
        if not hasattr(self, 'treasure') or not self.treasure:
            QtWidgets.QMessageBox.warning(self, "Warning", "No treasure to add. Please generate treasure first.")
            return

        # Calculate weights
        coin_weight = Decimal('0')
        for coin, amount in self.treasure['Coins'].items():
            coin_weight += Decimal(amount) / Decimal('50') 

        gem_weight = sum(Decimal(gem['Weight']) for gem in self.treasure['Gems'])

        art_weight = sum(Decimal(art['Weight']) for art in self.treasure['Art Objects'])

        magic_weight = Decimal('0')
        for mi in self.treasure['Magic Items']:
            details = self.base_items.get(mi)
            if not details:
                item_name = mi
                rarity = "Unknown"
                requires_attunement = "No"
                value = "0"
                weight = "0"
                description = ""
            else:
                item_name = details.get('id', mi)
                rarity = details.get('rarity', 'Unknown')
                requires_attunement = "Yes" if details.get('requires_attunement', False) else "No"
                value = str(details.get('value', 0))
                weight = str(details.get('weight', 0))
                description = details.get('description', "")
            
            # Fetch description if not provided and category is applicable
            if not description and rarity.lower() in ['common', 'uncommon', 'rare', 'very rare', 'legendary']:
                description = self.fetch_description_from_api(item_name, 'magic items')
            
            self.magic_model.appendRow([
                QtGui.QStandardItem(item_name),
                QtGui.QStandardItem(rarity),
                QtGui.QStandardItem(requires_attunement),
                QtGui.QStandardItem(str(value)),
                QtGui.QStandardItem(str(weight)),
                QtGui.QStandardItem(description),  # Description column
                QtGui.QStandardItem('No')  # Bought from Shop column
            ])

        # Add Coins
        for coin, amount in self.treasure['Coins'].items():
            coin_lower = coin.lower()
            if coin_lower in self.currency_vars:
                self.currency_vars[coin_lower] += Decimal(amount)
                self.currency_inputs[coin_lower].setValue(int(self.currency_vars[coin_lower]))
            else:
                QtWidgets.QMessageBox.warning(self, "Warning", f"Unknown coin type: {coin}")

        # Add Gems
        for gem in self.treasure['Gems']:
            gem_name = gem['Name']
            gem_value = gem['Value']
            gem_weight = gem['Weight']
            found = False
            for row in range(self.gem_model.rowCount()):
                if self.gem_model.item(row, 0).text() == gem_name:
                    quantity_item = self.gem_model.item(row, 1)
                    quantity = int(quantity_item.text()) + 1
                    quantity_item.setText(str(quantity))
                    total_value_item = self.gem_model.item(row, 2)
                    total_value = Decimal(total_value_item.text()) + Decimal(gem_value)
                    total_value_item.setText(str(total_value))
                    found = True
                    break
            if not found:
                row = [
                    QtGui.QStandardItem(gem_name),
                    QtGui.QStandardItem("1"),
                    QtGui.QStandardItem(str(gem_value)),
                    QtGui.QStandardItem(str(gem_weight)),
                    QtGui.QStandardItem('No')  # Bought from Shop column
                ]
                self.gem_model.appendRow(row)

        # Add Art Objects
        for art in self.treasure['Art Objects']:
            art_name = art['Name']
            art_value = art['Value']
            art_weight = art['Weight']
            description = art.get('Description', '')  # Use a default if Description is missing
            found = False
            for row in range(self.art_model.rowCount()):
                if self.art_model.item(row, 0).text() == art_name:
                    value_item = self.art_model.item(row, 1)
                    total_value = Decimal(value_item.text()) + Decimal(art_value)
                    value_item.setText(str(total_value))
                    found = True
                    break
            if not found:
                row = [
                    QtGui.QStandardItem(art_name),
                    QtGui.QStandardItem(str(art_value)),
                    QtGui.QStandardItem(str(art_weight)),
                    QtGui.QStandardItem(description),        # Description column
                    QtGui.QStandardItem('No')               # Bought from Shop column
                ]
                self.art_model.appendRow(row)

        # Update Total Weight and Capacity Check
        total_weight_to_add = coin_weight + gem_weight + art_weight + magic_weight
        new_total_weight = self.total_weight + total_weight_to_add
        if self.carrying_capacity > 0 and new_total_weight > self.carrying_capacity:
            QtWidgets.QMessageBox.warning(self, "Warning", "Cannot add treasure. Carrying capacity exceeded.")
            return

        # Update Total Wealth and Weight
        self.update_total_wealth_and_weight()

        # Reset Treasure Data
        self.treasure = None
        QtWidgets.QMessageBox.information(self, "Success", "Treasure added to inventory.")
            
    def add_treasure_to_party(self, treasure):
        for coin, amount in treasure['Coins'].items():
            self.party_loot['Coins'][coin.lower()] = self.party_loot['Coins'].get(coin.lower(), 0) + amount
        self.party_loot['Gems'].extend(treasure['Gems'])
        self.party_loot['Art Objects'].extend(treasure['Art Objects'])
        self.party_loot['Magic Items'].extend(treasure['Magic Items'])

        self.distribution_results.append("=== New Treasure Added to Party Loot ===")
        if treasure['Coins']:
            self.distribution_results.append("=== Coins ===")
            for coin, amount in treasure['Coins'].items():
                self.distribution_results.append(f"- {coin.upper()}: {amount}")
        if treasure['Gems']:
            self.distribution_results.append("\n=== Gems ===")
            gem_counter = Counter([gem['Name'] for gem in treasure['Gems']])
            for gem_name, count in gem_counter.items():
                self.distribution_results.append(f"- {gem_name}: {count}")
        if treasure['Art Objects']:
            self.distribution_results.append("\n=== Art Objects ===")
            art_counter = Counter([art['Name'] for art in treasure['Art Objects']])
            for art_name, count in art_counter.items():
                self.distribution_results.append(f"- {art_name}: {count}")
        if treasure['Magic Items']:
            self.distribution_results.append("\n=== Magic Items ===")
            magic_details = self.select_magic_items(treasure['Magic Items'])
            magic_counter = Counter(magic_details)
            for mi, count in magic_counter.items():
                self.distribution_results.append(f"- {mi} x{count}")
                    
    def add_misc_item(self):
        name = self.misc_name_input.text().strip()
        value = self.misc_value_input.value()
        weight = self.misc_weight_input.value()
        description = self.misc_desc_input.text().strip()

        if not name:
            QtWidgets.QMessageBox.warning(self, "Warning", "Please enter an item name.")
            return
        if value <= 0:
            QtWidgets.QMessageBox.warning(self, "Warning", "Value must be greater than zero.")
            return
        if weight < 0:
            QtWidgets.QMessageBox.warning(self, "Warning", "Weight cannot be negative.")
            return

        new_total_weight = self.total_weight + Decimal(weight)
        if self.carrying_capacity > 0 and new_total_weight > self.carrying_capacity:
            QtWidgets.QMessageBox.warning(self, "Warning", "Cannot add item. Carrying capacity exceeded.")
            return

        # Fetch description if not provided
        if not description:
            description = self.fetch_description_from_api(name, 'miscellaneous items')

        # Add the new item with description
        self.misc_model.appendRow([
            QtGui.QStandardItem(name),
            QtGui.QStandardItem(str(value)),
            QtGui.QStandardItem(str(weight)),
            QtGui.QStandardItem('No'),  # Bought from Shop
            QtGui.QStandardItem(description)  # Description
        ])

        # Clear input fields
        self.misc_name_input.clear()
        self.misc_value_input.setValue(0)
        self.misc_weight_input.setValue(0)
        self.misc_desc_input.clear()

        # Update total wealth and weight
        self.update_total_wealth_and_weight()
        
    def update_sell_table(self):
        category = self.sell_category_combo.currentText()
        self.sell_model.setRowCount(0)
        def get_item_text(model, row, column, default=''):
            item = model.item(row, column)
            return item.text() if item else default
        
        if category == 'Weapons':
            for row in range(self.weapons_model.rowCount()):
                name = get_item_text(self.weapons_model, row, 0)
                value = get_item_text(self.weapons_model, row, 1)
                weight = get_item_text(self.weapons_model, row, 2)
                bought_from_shop = get_item_text(self.weapons_model, row, 3)
                row_items = [
                    QtGui.QStandardItem(name),
                    QtGui.QStandardItem('Weapons'),
                    QtGui.QStandardItem(value),
                    QtGui.QStandardItem(weight),
                    QtGui.QStandardItem(bought_from_shop)
                ]
                self.sell_model.appendRow(row_items)
        
        elif category == 'Armor':
            for row in range(self.armor_model.rowCount()):
                name = get_item_text(self.armor_model, row, 0)
                value = get_item_text(self.armor_model, row, 1)
                weight = get_item_text(self.armor_model, row, 2)
                bought_from_shop = get_item_text(self.armor_model, row, 3)
                row_items = [
                    QtGui.QStandardItem(name),
                    QtGui.QStandardItem('Armor'),
                    QtGui.QStandardItem(value),
                    QtGui.QStandardItem(weight),
                    QtGui.QStandardItem(bought_from_shop)
                ]
                self.sell_model.appendRow(row_items)
        
        elif category == 'Miscellaneous Items':
            for row in range(self.misc_model.rowCount()):
                name = get_item_text(self.misc_model, row, 0)
                value = get_item_text(self.misc_model, row, 1)
                weight = get_item_text(self.misc_model, row, 2)
                bought_from_shop = get_item_text(self.misc_model, row, 3)
                row_items = [
                    QtGui.QStandardItem(name),
                    QtGui.QStandardItem('Miscellaneous Items'),
                    QtGui.QStandardItem(value),
                    QtGui.QStandardItem(weight),
                    QtGui.QStandardItem(bought_from_shop)
                ]
                self.sell_model.appendRow(row_items)
        
        elif category == 'Gems':
            for row in range(self.gem_model.rowCount()):
                name = get_item_text(self.gem_model, row, 0)
                quantity = get_item_text(self.gem_model, row, 1, '1')
                total_value = get_item_text(self.gem_model, row, 2, '0')
                weight = get_item_text(self.gem_model, row, 3, '0.01')
                bought_from_shop = get_item_text(self.gem_model, row, 4)
                try:
                    quantity_int = int(quantity)
                    total_value_dec = Decimal(total_value)
                    weight_dec = Decimal(weight)
                    value_per_item = (total_value_dec / quantity_int).quantize(Decimal('0.01')) if quantity_int else Decimal('0')
                    weight_per_item = (weight_dec / quantity_int).quantize(Decimal('0.0001')) if quantity_int else Decimal('0')
                except (InvalidOperation, ZeroDivisionError):
                    value_per_item = Decimal('0')
                    weight_per_item = Decimal('0')
                for _ in range(quantity_int):
                    row_items = [
                        QtGui.QStandardItem(name),
                        QtGui.QStandardItem('Gems'),
                        QtGui.QStandardItem(str(value_per_item)),
                        QtGui.QStandardItem(str(weight_per_item)),
                        QtGui.QStandardItem(bought_from_shop)
                    ]
                    self.sell_model.appendRow(row_items)
        
        elif category == 'Art Objects':
            for row in range(self.art_model.rowCount()):
                name = get_item_text(self.art_model, row, 0)
                value = get_item_text(self.art_model, row, 1)
                weight = get_item_text(self.art_model, row, 2)
                bought_from_shop = get_item_text(self.art_model, row, 3)
                row_items = [
                    QtGui.QStandardItem(name),
                    QtGui.QStandardItem('Art Objects'),
                    QtGui.QStandardItem(value),
                    QtGui.QStandardItem(weight),
                    QtGui.QStandardItem(bought_from_shop)
                ]
                self.sell_model.appendRow(row_items)
        
        elif category == 'Magic Items':
            for row in range(self.magic_model.rowCount()):
                name = get_item_text(self.magic_model, row, 0)
                value = get_item_text(self.magic_model, row, 3)
                weight = get_item_text(self.magic_model, row, 4)
                bought_from_shop = get_item_text(self.magic_model, row, 5)
                row_items = [
                    QtGui.QStandardItem(name),
                    QtGui.QStandardItem('Magic Items'),
                    QtGui.QStandardItem(value),
                    QtGui.QStandardItem(weight),
                    QtGui.QStandardItem(bought_from_shop)
                ]
                self.sell_model.appendRow(row_items)
        
        logging.info(f"Sell table updated for category: {category}")
        
    def sell_inventory_item(self):
        selected = self.sell_table.selectionModel().selectedRows()
        if not selected:
            QtWidgets.QMessageBox.warning(self, "Warning", "Please select item(s) to sell.")
            return

        total_sell_price = Decimal('0')
        items_to_remove = []

        for index in selected:
            name = self.sell_model.item(index.row(), 0).text()
            category = self.sell_model.item(index.row(), 1).text()
            value = Decimal(self.sell_model.item(index.row(), 2).text())
            weight = Decimal(self.sell_model.item(index.row(), 3).text())
            bought_from_shop = self.sell_model.item(index.row(), 4).text() == 'Yes'

            if category in ['Gems', 'Art Objects']:
                sell_price = value
            elif bought_from_shop:
                shop_rate = Decimal(self.shop_rate_slider.value()) / Decimal('100')
                sell_price = (value * shop_rate).quantize(Decimal('0.01'))
            else:
                QtWidgets.QMessageBox.warning(
                    self,
                    "Warning",
                    f"You cannot sell '{name}' because it was not bought from the shop."
                )
                continue

            total_sell_price += sell_price
            items_to_remove.append((category, name, bought_from_shop))

        if total_sell_price == 0:
            return

        reply = QtWidgets.QMessageBox.question(
            self,
            "Confirm Sale",
            f"Do you want to sell the selected items for a total of {total_sell_price} gp?",
            QtWidgets.QMessageBox.Yes | QtWidgets.QMessageBox.No,
            QtWidgets.QMessageBox.No
        )
        if reply == QtWidgets.QMessageBox.No:
            return

        self.add_currency(total_sell_price)

        for category, name, bought_from_shop in items_to_remove:
            self.remove_item_from_inventory_by_name(category, name, bought_from_shop)
            self.update_sell_table()

        self.update_total_wealth_and_weight()
        QtWidgets.QMessageBox.information(
            self,
            "Success",
            f"You have sold the selected items for {total_sell_price} gp."
        )

        action = {
            'action_type': 'sell_items',
            'data': {
                'items': items_to_remove,
                'total_sell_price': str(total_sell_price)
            }
        }
        
    def remove_item_from_inventory(self, model, name, is_gem=False):
        for row in range(model.rowCount()):
            if model.item(row, 0).text() == name:
                if is_gem:
                    quantity = int(model.item(row, 1).text())
                    if quantity > 1:
                        model.setItem(row, 1, QtGui.QStandardItem(str(quantity - 1)))
                        current_total = Decimal(model.item(row, 2).text())
                        model.setItem(row, 2, QtGui.QStandardItem(str(current_total - (current_total / Decimal(quantity)))))
                    else:
                        model.removeRow(row)
                else:
                    model.removeRow(row)
                break
    
    def add_currency(self, amount_gp):
        total_currency_in_gp = self.get_total_currency_in_gp()
        remaining = amount_gp
        currency_order = [Currency.PP, Currency.GP, Currency.EP, Currency.SP]
        for currency in currency_order:
            currency_value = self.get_currency_value_in_gp(currency)
            amount_in_currency = (remaining // currency_value).to_integral_value(rounding=ROUND_DOWN)
            if amount_in_currency > 0:
                self.currency_vars[currency.value] += amount_in_currency
                self.currency_inputs[currency.value].setValue(int(self.currency_vars[currency.value]))
                remaining -= amount_in_currency * currency_value
        if remaining > 0:
            cp_amount = (remaining / Decimal('0.01')).to_integral_value(rounding=ROUND_DOWN)
            self.currency_vars['cp'] += cp_amount
            self.currency_inputs['cp'].setValue(int(self.currency_vars['cp']))
        self.currency_holdings_label.setText(self.get_currency_holdings_text())
    
    def add_gem_item(self):
        gem_type = self.gem_type_combo.currentText()
        quantity = self.gem_quantity_input.value()
        if not gem_type:
            QtWidgets.QMessageBox.warning(self, "Warning", "Please select a gem type.")
            return
        weight_per_item = Decimal('0.01')
        total_weight_to_add = weight_per_item * Decimal(quantity)
        new_total_weight = self.total_weight + total_weight_to_add
        if self.carrying_capacity > 0 and new_total_weight > self.carrying_capacity:
            QtWidgets.QMessageBox.warning(self, "Warning", "Cannot add gems. Carrying capacity exceeded.")
            return    
        match = re.match(r'(.+)\s+\((\d+)\s+GP\)', gem_type)
        if match:
            gem_name, gem_value = match.groups()
            gem_value = Decimal(gem_value)
            total_value = gem_value * quantity
            for _ in range(quantity):
                self.gem_model.appendRow([
                    QtGui.QStandardItem(gem_name),
                    QtGui.QStandardItem("1"),
                    QtGui.QStandardItem(str(gem_value)),
                    QtGui.QStandardItem("0.01"),
                    QtGui.QStandardItem('No')  
                ])
            self.gem_quantity_input.setValue(1)
            self.update_total_wealth_and_weight()
        else:
            QtWidgets.QMessageBox.warning(self, "Warning", "Invalid gem type format.")
            return
              
    def add_art_item(self):
        name = self.art_name_input.text()
        value = self.art_value_input.value()
        weight = self.art_weight_input.value()
        description = self.art_desc_input.text()  # Retrieve description
        if not name:
            QtWidgets.QMessageBox.warning(self, "Warning", "Please enter an art object name.")
            return
        if value <= 0:
            QtWidgets.QMessageBox.warning(self, "Warning", "Value must be greater than zero.")
            return
        if weight < 0:
            QtWidgets.QMessageBox.warning(self, "Warning", "Weight cannot be negative.")
            return

        new_total_weight = self.total_weight + Decimal(weight)
        if self.carrying_capacity > 0 and new_total_weight > self.carrying_capacity:
            QtWidgets.QMessageBox.warning(self, "Warning", "Cannot add art object. Carrying capacity exceeded.")
            return

        self.art_model.appendRow([
            QtGui.QStandardItem(name),
            QtGui.QStandardItem(str(value)),
            QtGui.QStandardItem(str(weight)),
            QtGui.QStandardItem(description),  # Description
            QtGui.QStandardItem('No')          # Bought from Shop
        ])
        self.art_name_input.clear()
        self.art_value_input.setValue(0)
        self.art_weight_input.setValue(0)
        self.art_desc_input.clear()
        self.update_total_wealth_and_weight()
          
    def add_magic_item(self):
        name = self.magic_name_input.text().strip()
        rarity = self.magic_rarity_combo.currentText()
        requires_attunement = self.magic_attunement_checkbox.isChecked()
        value = self.magic_value_input.value()
        weight = self.magic_weight_input.value()
        description = self.magic_desc_input.text().strip()  # Retrieve description

        if not name:
            QtWidgets.QMessageBox.warning(self, "Warning", "Please enter a magic item name.")
            return
        if value <= 0:
            QtWidgets.QMessageBox.warning(self, "Warning", "Value must be greater than zero.")
            return
        if weight < 0:
            QtWidgets.QMessageBox.warning(self, "Warning", "Weight cannot be negative.")
            return

        new_total_weight = self.total_weight + Decimal(weight)
        if self.carrying_capacity > 0 and new_total_weight > self.carrying_capacity:
            QtWidgets.QMessageBox.warning(self, "Warning", "Cannot add magic item. Carrying capacity exceeded.")
            return

        # Fetch description if not provided
        if not description:
            description = self.fetch_description_from_api(name, 'magic items')

        self.magic_model.appendRow([
            QtGui.QStandardItem(name),
            QtGui.QStandardItem(rarity),
            QtGui.QStandardItem("Yes" if requires_attunement else "No"),
            QtGui.QStandardItem(str(value)),
            QtGui.QStandardItem(str(weight)),
            QtGui.QStandardItem(description),  # Description column
            QtGui.QStandardItem('No')  # Bought from Shop column
        ])

        # Clear input fields
        self.magic_name_input.clear()
        self.magic_rarity_combo.setCurrentIndex(0)
        self.magic_attunement_checkbox.setChecked(False)
        self.magic_value_input.setValue(0)
        self.magic_weight_input.setValue(0)
        self.magic_desc_input.clear()

        # Update total weight and wealth
        self.update_total_wealth_and_weight()
                
    def distribute_loot(self):
        num_members = self.member_count_input.value()
        if num_members <= 0:
            QtWidgets.QMessageBox.warning(self, "Warning", "Number of members must be at least 1.")
            return

        member_names = [input.text().strip() if input.text().strip() else f"Member {i + 1}" for i, input in enumerate(self.member_inputs)]
        distributions = {name: {'Coins': {}, 'Items': [], 'Total Value': Decimal('0')} for name in member_names}

        distribution_method = self.distribution_method_combo.currentText()

        total_coins = {coin: Decimal(self.party_loot['Coins'].get(coin, 0)) for coin in self.currency_vars}

        if distribution_method == "Random Extra":
            self.distribute_coins_random_extra(distributions, total_coins, member_names, num_members)
        elif distribution_method == "Split into Smaller Denominations":
            self.distribute_coins_split_denominations(distributions, total_coins, member_names, num_members)
        else:
            QtWidgets.QMessageBox.warning(self, "Warning", "Unknown distribution method selected.")
            return

        self.distribute_items(distributions, member_names, num_members)

        self.display_distribution_results(distributions, member_names)

        self.party_loot = {
            'Coins': {},
            'Gems': [],
            'Art Objects': [],
            'Magic Items': []
        }

        action = {
            'action_type': 'distribute_loot',
            'data': {
                'method': distribution_method,
                'distributions': distributions
            }
        }

        QtWidgets.QMessageBox.information(self, "Success", "Loot has been successfully distributed to the party members.")    

    def distribute_coins_random_extra(self, distributions, total_coins, member_names, num_members):
        for coin, amount in total_coins.items():
            if amount == 0:
                continue
            base_amount = amount // num_members
            remainder = amount % num_members
            for name in member_names:
                distributions[name]['Coins'][coin] = distributions[name]['Coins'].get(coin, 0) + base_amount
                value_in_gp = base_amount * self.get_currency_value_in_gp(Currency(coin))
                distributions[name]['Total Value'] += value_in_gp

            if remainder > 0:
                recipients = random.choices(member_names, k=int(remainder))
                for name in recipients:
                    distributions[name]['Coins'][coin] += 1
                    value_in_gp = self.get_currency_value_in_gp(Currency(coin))
                    distributions[name]['Total Value'] += value_in_gp

    def distribute_coins_split_denominations(self, distributions, total_coins, member_names, num_members):
        denominations = [
            (Currency.PP, Decimal('10')),  
            (Currency.GP, Decimal('1')),   
            (Currency.EP, Decimal('0.5')),
            (Currency.SP, Decimal('0.1')),
            (Currency.CP, Decimal('0.01')) 
        ]

        total_gp = Decimal('0')
        for coin, amount in total_coins.items():
            total_gp += amount * self.get_currency_value_in_gp(Currency(coin))

        base_gp = (total_gp / Decimal(num_members)).quantize(Decimal('0.1'), rounding=ROUND_DOWN)
        remainder_gp = total_gp - (base_gp * Decimal(num_members))

        for name in member_names:
            remaining_gp = base_gp
            for currency, rate in denominations:
                amount = int(remaining_gp // rate)
                if amount > 0:
                    distributions[name]['Coins'][currency.value] = distributions[name]['Coins'].get(currency.value, 0) + amount
                    distributions[name]['Total Value'] += Decimal(amount) * self.get_currency_value_in_gp(currency)
                    remaining_gp -= Decimal(amount) * rate
            if remaining_gp >= Decimal('0.01'):
                cp_amount = int((remaining_gp / Decimal('0.01')).to_integral_value(rounding=ROUND_DOWN))
                distributions[name]['Coins']['cp'] = distributions[name]['Coins'].get('cp', 0) + cp_amount
                distributions[name]['Total Value'] += Decimal(cp_amount) * self.get_currency_value_in_gp(Currency('cp'))

        if remainder_gp >= Decimal('0.01'):
            cp_remainder = int((remainder_gp / Decimal('0.01')).to_integral_value(rounding=ROUND_DOWN))
            recipients = random.choices(member_names, k=cp_remainder)
            for name in recipients:
                distributions[name]['Coins']['cp'] = distributions[name]['Coins'].get('cp', 0) + 1
                distributions[name]['Total Value'] += Decimal('0.01') 

    def distribute_items(self, distributions, member_names, num_members):
        items = []
        for gem in self.party_loot['Gems']:
            items.append({'Name': gem['Name'], 'Value': Decimal(gem['Value'])})
        for art in self.party_loot['Art Objects']:
            items.append({'Name': art['Name'], 'Value': Decimal(art['Value'])})
        for mi in self.party_loot['Magic Items']:
            if isinstance(mi, str):
                item_name = mi
                value = Decimal('0')
                for row in range(self.magic_model.rowCount()):
                    if self.magic_model.item(row, 0).text() == item_name:
                        value = Decimal(self.magic_model.item(row, 3).text())
                        break
            else:
                item_name = mi.get('Name', 'Unknown Item')
                value = mi.get('Value', Decimal('0'))
            items.append({'Name': item_name, 'Value': Decimal(value)})

        random.shuffle(items)

        for item in items:
            name = min(distributions, key=lambda x: distributions[x]['Total Value'])
            distributions[name]['Items'].append(item['Name'])
            distributions[name]['Total Value'] += item['Value']
            
    def display_distribution_results(self, distributions, member_names):
        self.distribution_results.clear()
        self.distribution_results.append("=== Distribution Results ===")
        for name in member_names:
            self.distribution_results.append(f"\n{name}:")
            coins = distributions[name]['Coins']
            if any(coins.values()):
                self.distribution_results.append("Coins:")
                for coin in coins:
                    amount = coins[coin]
                    if amount > 0:
                        self.distribution_results.append(f"- {coin.upper()}: {amount}")
            items = distributions[name]['Items']
            if items:
                self.distribution_results.append("Items:")
                for item in items:
                    self.distribution_results.append(f"- {item}")
            total_value = distributions[name]['Total Value']
            if total_value == int(total_value):
                total_value_str = f"{int(total_value)}"
            else:
                total_value_str = f"{total_value.quantize(Decimal('0.1'))}"
            self.distribution_results.append(f"Total Value: {total_value_str} gp")        
           
    def update_total_wealth_and_weight(self):
        total_wealth = Decimal('0')
        total_weight = Decimal('0')
        
        for row in range(self.weapons_model.rowCount()):
            value = Decimal(self.weapons_model.item(row, 1).text())
            weight = Decimal(self.weapons_model.item(row, 2).text())
            total_wealth += value
            total_weight += weight

        for row in range(self.armor_model.rowCount()):
            value = Decimal(self.armor_model.item(row, 1).text())
            weight = Decimal(self.armor_model.item(row, 2).text())
            total_wealth += value
            total_weight += weight

        for currency in Currency:
            amount = self.currency_vars[currency.value]
            gp_value = amount * self.get_currency_value_in_gp(currency)
            total_wealth += gp_value
            coin_weight = amount / 50
            total_weight += coin_weight

        for row in range(self.misc_model.rowCount()):
            value = Decimal(self.misc_model.item(row, 1).text())
            weight = Decimal(self.misc_model.item(row, 2).text())
            total_wealth += value
            total_weight += weight

        for row in range(self.gem_model.rowCount()):
            total_value = Decimal(self.gem_model.item(row, 2).text())
            weight = Decimal(self.gem_model.item(row, 3).text())
            total_wealth += total_value
            total_weight += weight

        for row in range(self.art_model.rowCount()):
            value = Decimal(self.art_model.item(row, 1).text())
            weight = Decimal(self.art_model.item(row, 2).text())
            total_wealth += value
            total_weight += weight

        for row in range(self.magic_model.rowCount()):
            value = Decimal(self.magic_model.item(row, 3).text())
            weight = Decimal(self.magic_model.item(row, 4).text())
            total_wealth += value
            total_weight += weight

        total_wealth = total_wealth.quantize(Decimal('0.1')) if total_wealth % 1 else total_wealth.quantize(Decimal('1'))
        total_weight = total_weight.quantize(Decimal('0.1')) if total_weight % 1 else total_weight.quantize(Decimal('1'))

        total_wealth_str = f"{total_wealth}"
        total_weight_str = f"{total_weight}"

        self.total_wealth_label.setText(f"Total Wealth: {total_wealth_str} gp")
        self.total_weight_label.setText(f"Total Weight: {total_weight_str} lbs")
        self.total_weight = total_weight
  
    def remove_misc_item(self):
        selected = self.misc_table.selectionModel().selectedRows()
        for index in sorted(selected, reverse=True):
            row_data = {
                'name': self.misc_model.item(index.row(), 0).text(),
                'value': float(self.misc_model.item(index.row(), 1).text()),
                'weight': float(self.misc_model.item(index.row(), 2).text())
            }
            self.misc_model.removeRow(index.row())

    def remove_gem_item(self):
        selected = self.gem_table.selectionModel().selectedRows()
        for index in sorted(selected, reverse=True):
            row_data = {
                'type': self.gem_model.item(index.row(), 0).text(),
                'quantity': int(self.gem_model.item(index.row(), 1).text()),
                'total_value': float(self.gem_model.item(index.row(), 2).text()),
                'weight': float(self.gem_model.item(index.row(), 3).text())
            }
            self.gem_model.removeRow(index.row())

    def remove_art_item(self):
        selected = self.art_table.selectionModel().selectedRows()
        for index in sorted(selected, reverse=True):
            row_data = {
                'name': self.art_model.item(index.row(), 0).text(),
                'value': float(self.art_model.item(index.row(), 1).text()),
                'weight': float(self.art_model.item(index.row(), 2).text())
            }

            self.art_model.removeRow(index.row())

    def remove_magic_item(self):
        selected = self.magic_table.selectionModel().selectedRows()
        for index in sorted(selected, reverse=True):
            row_data = {
                'name': self.magic_model.item(index.row(), 0).text(),
                'rarity': self.magic_model.item(index.row(), 1).text(),
                'attunement': self.magic_model.item(index.row(), 2).text(),
                'value': float(self.magic_model.item(index.row(), 3).text()),
                'weight': float(self.magic_model.item(index.row(), 4).text())
            }

            self.magic_model.removeRow(index.row())
            
    def save_profile(self):
        options = QtWidgets.QFileDialog.Options()
        default_directory = self.default_save_location.text() or ""
        filename, _ = QtWidgets.QFileDialog.getSaveFileName(
            self, "Save Profile", default_directory, "JSON Files (*.json)", options=options
        )
        if filename:
            data = {
                'currency_vars': {k: str(v) for k, v in self.currency_vars.items()},
                'misc_items': [],
                'gems': [],
                'arts': [],
                'magic_items': [],
                'weapons': [],
                'armor': []
            }

            # Helper function to safely get text from model items
            def get_item_text(model, row, column):
                item = model.item(row, column)
                if item is None:
                    logging.warning(f"Missing item at row {row}, column {column} in {model.objectName()}")
                    return ''
                return item.text()

            # Save Miscellaneous Items with Description
            for row in range(self.misc_model.rowCount()):
                item = {
                    'Name': get_item_text(self.misc_model, row, 0),
                    'Value': get_item_text(self.misc_model, row, 1),
                    'Weight': get_item_text(self.misc_model, row, 2),
                    'BoughtFromShop': get_item_text(self.misc_model, row, 3),
                    'Description': get_item_text(self.misc_model, row, 4)  # Description
                }
                data['misc_items'].append(item)

            # Save Gems
            for row in range(self.gem_model.rowCount()):
                gem = {
                    'Type': get_item_text(self.gem_model, row, 0),
                    'Quantity': get_item_text(self.gem_model, row, 1),
                    'Total Value': get_item_text(self.gem_model, row, 2),
                    'Weight': get_item_text(self.gem_model, row, 3),
                    'BoughtFromShop': get_item_text(self.gem_model, row, 4)
                }
                data['gems'].append(gem)

            # Save Art Objects
            for row in range(self.art_model.rowCount()):
                art = {
                    'Name': get_item_text(self.art_model, row, 0),
                    'Value': get_item_text(self.art_model, row, 1),
                    'Weight': get_item_text(self.art_model, row, 2),
                    'Description': get_item_text(self.art_model, row, 3),
                    'BoughtFromShop': get_item_text(self.art_model, row, 4)
                }
                data['arts'].append(art)

            # Save Magic Items
            for row in range(self.magic_model.rowCount()):
                magic_item = {
                    'Name': get_item_text(self.magic_model, row, 0),
                    'Rarity': get_item_text(self.magic_model, row, 1),
                    'Attunement': get_item_text(self.magic_model, row, 2),
                    'Value': get_item_text(self.magic_model, row, 3),
                    'Weight': get_item_text(self.magic_model, row, 4),
                    'Description': get_item_text(self.magic_model, row, 5),
                    'BoughtFromShop': get_item_text(self.magic_model, row, 6)
                }
                data['magic_items'].append(magic_item)

            # Save Weapons
            for row in range(self.weapons_model.rowCount()):
                weapon = {
                    'Name': get_item_text(self.weapons_model, row, 0),
                    'Value': get_item_text(self.weapons_model, row, 1),
                    'Weight': get_item_text(self.weapons_model, row, 2),
                    'BoughtFromShop': get_item_text(self.weapons_model, row, 3),
                    'Description': get_item_text(self.weapons_model, row, 4)
                }
                data['weapons'].append(weapon)

            # Save Armor
            for row in range(self.armor_model.rowCount()):
                armor = {
                    'Name': get_item_text(self.armor_model, row, 0),
                    'Value': get_item_text(self.armor_model, row, 1),
                    'Weight': get_item_text(self.armor_model, row, 2),
                    'BoughtFromShop': get_item_text(self.armor_model, row, 3),
                    'Description': get_item_text(self.armor_model, row, 4)
                }
                data['armor'].append(armor)

            # Save to JSON file
            try:
                with open(filename, 'w') as f:
                    json.dump(data, f, indent=4)
                QtWidgets.QMessageBox.information(self, "Success", "Profile saved successfully.")
            except Exception as e:
                QtWidgets.QMessageBox.critical(self, "Error", f"Failed to save profile: {e}")

    def load_profile(self):
        options = QtWidgets.QFileDialog.Options()
        default_directory = self.default_save_location.text() or ""
        filename, _ = QtWidgets.QFileDialog.getOpenFileName(self, "Load Profile", default_directory, "JSON Files (*.json)", options=options)
        if filename:
            try:
                with open(filename, 'r') as f:
                    data = json.load(f)
            except Exception as e:
                QtWidgets.QMessageBox.critical(self, "Error", f"Failed to load profile: {e}")
                return

            # Load Currency
            for k, v in data.get('currency_vars', {}).items():
                if k in self.currency_vars:
                    self.currency_vars[k] = Decimal(v)
                    self.currency_inputs[k].setValue(int(Decimal(v)))
                else:
                    QtWidgets.QMessageBox.warning(self, "Warning", f"Unknown currency type: {k}")

            # Load Miscellaneous Items with Description
            self.misc_model.setRowCount(0)
            for item in data.get('misc_items', []):
                row = [
                    QtGui.QStandardItem(item['Name']),
                    QtGui.QStandardItem(item['Value']),
                    QtGui.QStandardItem(item['Weight']),
                    QtGui.QStandardItem(item.get('BoughtFromShop', 'No')),
                    QtGui.QStandardItem(item.get('Description', ''))  # Description
                ]
                self.misc_model.appendRow(row)

            # Load Gems
            self.gem_model.setRowCount(0)
            for gem in data.get('gems', []):
                row = [
                    QtGui.QStandardItem(gem['Type']),
                    QtGui.QStandardItem(gem['Quantity']),
                    QtGui.QStandardItem(gem['Total Value']),
                    QtGui.QStandardItem(gem['Weight']),
                    QtGui.QStandardItem(gem.get('BoughtFromShop', 'No'))
                ]
                self.gem_model.appendRow(row)

            # Load Art Objects
            self.art_model.setRowCount(0)
            for art in data.get('arts', []):
                row = [
                    QtGui.QStandardItem(art['Name']),
                    QtGui.QStandardItem(art['Value']),
                    QtGui.QStandardItem(art['Weight']),
                    QtGui.QStandardItem(art.get('Description', '')),
                    QtGui.QStandardItem(art.get('BoughtFromShop', 'No'))
                ]
                self.art_model.appendRow(row)

            # Load Magic Items
            self.magic_model.setRowCount(0)
            for magic_item in data.get('magic_items', []):
                row = [
                    QtGui.QStandardItem(magic_item['Name']),
                    QtGui.QStandardItem(magic_item['Rarity']),
                    QtGui.QStandardItem(magic_item['Attunement']),
                    QtGui.QStandardItem(magic_item['Value']),
                    QtGui.QStandardItem(magic_item['Weight']),
                    QtGui.QStandardItem(magic_item.get('Description', '')),
                    QtGui.QStandardItem(magic_item.get('BoughtFromShop', 'No'))
                ]
                self.magic_model.appendRow(row)

            # Load Weapons
            self.weapons_model.setRowCount(0)
            for weapon in data.get('weapons', []):
                row = [
                    QtGui.QStandardItem(weapon['Name']),
                    QtGui.QStandardItem(weapon['Value']),
                    QtGui.QStandardItem(weapon['Weight']),
                    QtGui.QStandardItem(weapon.get('BoughtFromShop', 'No')),
                    QtGui.QStandardItem(weapon.get('Description', ''))
                ]
                self.weapons_model.appendRow(row) 

            # Load Armor
            self.armor_model.setRowCount(0)
            for armor in data.get('armor', []):
                row = [
                    QtGui.QStandardItem(armor['Name']),
                    QtGui.QStandardItem(armor['Value']),
                    QtGui.QStandardItem(armor['Weight']),
                    QtGui.QStandardItem(armor.get('BoughtFromShop', 'No')),
                    QtGui.QStandardItem(armor.get('Description', ''))
                ]
                self.armor_model.appendRow(row) 

            self.update_total_wealth_and_weight()
            QtWidgets.QMessageBox.information(self, "Success", "Profile loaded successfully.")
            
    def convert_currency(self, currency):
        amount = self.converter_inputs[currency].value()
        results = []
        for target_currency in Currency:
            if target_currency.value != currency:
                rate = self.get_conversion_rate(currency, target_currency.value)
                if rate:
                    converted_amount = amount * rate
                    if converted_amount == int(converted_amount):
                        converted_amount_str = f"{int(converted_amount)}"
                    else:
                        converted_amount_str = f"{converted_amount:.2f}"
                    results.append(f"{converted_amount_str} {target_currency.name}")
        self.converter_results[currency].setText('\n'.join(results))
        for other_currency in Currency:
            if other_currency.value != currency:
                self.converter_inputs[other_currency.value].blockSignals(True)
                self.converter_inputs[other_currency.value].setValue(0)
                self.converter_results[other_currency.value].setText('')
                self.converter_inputs[other_currency.value].blockSignals(False)

    def get_conversion_rate(self, from_currency, to_currency):
        rate = self.conversion_rates.get(from_currency, {}).get(to_currency, None)
        if rate is None or rate == 0:
            inverse_rate = self.conversion_rates.get(to_currency, {}).get(from_currency, None)
            if inverse_rate and inverse_rate != 0:
                rate = 1 / inverse_rate
            else:
                rate = None  
        return rate
            
    def show_about_dialog(self):
        QtWidgets.QMessageBox.about(self, "About D&D Wealth Manager",
            "D&D Wealth Manager\nVersion 1.0\n\nDeveloped to help manage your Dungeons & Dragons wealth and inventory \nMade By Jaz Dashti \nInstagram: q8_g33k.")
            
def show_main_window(window, splash):
    """Show the main window and close the splash screen."""
    window.show()
    splash.close()

def main():
    if hasattr(QtCore.Qt, 'AA_EnableHighDpiScaling'):
        QtWidgets.QApplication.setAttribute(QtCore.Qt.AA_EnableHighDpiScaling, True)
    if hasattr(QtCore.Qt, 'AA_UseHighDpiPixmaps'):
        QtWidgets.QApplication.setAttribute(QtCore.Qt.AA_UseHighDpiPixmaps, True)

    app = QtWidgets.QApplication(sys.argv)
    
    # Set the application icon
    icon_path = resource_path('icon.ico')
    app_icon = QtGui.QIcon(icon_path)
    app.setWindowIcon(app_icon)
    
    # Create the splash screen pixmap
    splash_pix = QPixmap(resource_path('icon.png'))
    
    # Resize the splash screen image if desired
    splash_pix = splash_pix.scaled(
        SPLASH_IMAGE_SIZE[0], 
        SPLASH_IMAGE_SIZE[1], 
        Qt.KeepAspectRatio, 
        Qt.SmoothTransformation
    )
    
    # Initialize the splash screen with the pixmap and set window flags
    splash = CustomSplashScreen(splash_pix)
    splash.setWindowFlags(Qt.FramelessWindowHint | Qt.SplashScreen)
    
    # Show the splash screen
    splash.show()
    
    # Process events to ensure the splash screen is displayed immediately
    app.processEvents()
    
    # Initialize the main window
    window = DnDWealthManager()
    
    if SPLASH_DISPLAY_TIME > 0:
        # Set a timer to close the splash and show the main window after SPLASH_DISPLAY_TIME milliseconds
        QTimer.singleShot(SPLASH_DISPLAY_TIME, lambda: show_main_window(window, splash))
    else:
        # Auto close when the main window is ready
        show_main_window(window, splash)
      
 # Start the application's event loop
    sys.exit(app.exec())

class CustomSplashScreen(QSplashScreen):
    def __init__(self, pixmap):
        super().__init__(pixmap)
        self.message = "Thanks to all the Dungeon Masters Out There\nFor All The Work And Effort!"
        self.font = QFont()
        self.font.setPointSize(SPLASH_FONT_SIZE)
        self.font.setBold(True)  # Make the font bold
        self.text_color = QColor(SPLASH_TEXT_COLOR)
        self.outline_color = QColor(SPLASH_OUTLINE_COLOR)
        self.glow_color = QColor(SPLASH_GLOW_COLOR)

    def drawContents(self, painter):
        painter.save()
        painter.setRenderHint(QPainter.Antialiasing)
        painter.setFont(self.font)
        
        # Draw outline
        pen = QtGui.QPen(self.outline_color)
        pen.setWidth(3)
        painter.setPen(pen)
        painter.drawText(self.rect().adjusted(1, 1, -1, -1), Qt.AlignBottom | Qt.AlignCenter, self.message)
        
        # Draw main text
        painter.setPen(self.text_color)
        painter.drawText(self.rect(), Qt.AlignBottom | Qt.AlignCenter, self.message)

        # Optional: Draw glow effect
        glow_pen = QtGui.QPen(self.glow_color)
        glow_pen.setWidth(8)
        painter.setPen(glow_pen)
        painter.drawText(self.rect().adjusted(-2, -2, 2, 2), Qt.AlignBottom | Qt.AlignCenter, self.message)
        
        painter.restore()

if __name__ == "__main__":
    main()        
    
