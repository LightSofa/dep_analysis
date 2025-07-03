# -*- coding: utf-8 -*-

"""
Mod Organizer 2 Nexus Mods Dependency Analyzer Plugin

This plugin integrates a comprehensive dependency analysis tool into Mod Organizer 2.
It scrapes Nexus Mods to build dependency graphs, identifies missing requirements,
and generates a topologically sorted load order recommendation for the left pane.

Features:
- Full integration as an MO2 tool plugin.
- Background processing to keep the UI responsive.
- User-configurable settings via the MO2 settings menu.
- Isolated data storage in a dedicated sub-folder under plugins/data.
- Bundled library support by dynamically adding a 'libs' folder to sys.path.
- Two main analysis modes:
  1. Single Mod Dependency Tree: Analyzes a specific mod's requirements.
  2. Full Profile Analysis & Sort: Creates a comprehensive load order report.
- One-click access to cache clearing and rule configuration.
- Automatic detection of required Python libraries.

Author: Gemini AI
Version: 2.2.0 (MO2 Plugin with Bundled Libs Support)
"""

from __future__ import annotations
import os
import json
import time
import re
import logging
import configparser
import heapq
import textwrap
import webbrowser
import subprocess
import sys
import site
from collections import defaultdict, deque
from datetime import datetime, timedelta
from pathlib import Path
from typing import List, Dict, Set, Any, Optional, Tuple


site.addsitedir(os.path.join(os.path.dirname(__file__), "lib"))
import bs4
import playwright.sync_api
BS4_MODULE = bs4
PLAYWRIGHT_MODULE = playwright
DEPENDENCIES_MET = True

import mobase
from PyQt6.QtWidgets import (
    QDialog, QVBoxLayout, QHBoxLayout, QPushButton, QLabel, QLineEdit,
    QDialogButtonBox, QMessageBox, QGroupBox, QPlainTextEdit
)
from PyQt6.QtCore import (
    QObject, QThread, pyqtSignal, Qt
)
from PyQt6.QtGui import QIcon, QTextCursor

# --- 基础导入 ---
# 将依赖库的导入推迟到 init 方法中，在 sys.path 被修改后进行
# try:
#     import mobase
#     from PyQt6.QtWidgets import (
#         QDialog, QVBoxLayout, QHBoxLayout, QPushButton, QLabel, QLineEdit,
#         QDialogButtonBox, QMessageBox, QGroupBox, QPlainTextEdit
#     )
#     from PyQt6.QtCore import (
#         QObject, QThread, pyqtSignal, Qt
#     )
#     from PyQt6.QtGui import QIcon, QTextCursor
# except ImportError:
#     print("Mobase or PyQt6 not found. This script must be run within Mod Organizer 2.")


#     class QObject:
#         pass


#     class QDialog:
#         pass


#     class mobase:
#         class IPluginTool: pass

# --- 全局依赖状态 ---
# 默认值为 False，将在 init 方法中动态检查并更新
# DEPENDENCIES_MET = False
# BS4_MODULE = None
# PLAYWRIGHT_MODULE = None

log = logging.getLogger(__name__)


# =============================================================================
# 1. 配置管理 (Settings)
# =============================================================================
class PluginSettings:
    """
    集中管理所有配置和从MO2动态获取的路径。
    """

    def __init__(self, organizer: mobase.IOrganizer, plugin_name: str):
        self._organizer = organizer
        self._plugin_name = plugin_name

        # 创建插件专属的子目录
        base_data_path = Path(organizer.pluginDataPath())
        self.BASE_DIR = base_data_path / 'dep_analysis'
        os.makedirs(self.BASE_DIR, exist_ok=True)

        self.RULES_PATH = self.BASE_DIR / 'rules.ini'
        self.COOKIES_PATH = self.BASE_DIR / 'cookies.json'
        self.CACHE_FILE_PATH = self.BASE_DIR / 'nexus_cache.json'

        # 从 MO2 的设置系统中读取值
        self.CACHE_EXPIRATION_DAYS: int = int(str(self._organizer.pluginSetting(self._plugin_name, "cache_expiration_days")))
        self.REQUEST_TIMEOUT: int = int(str(self._organizer.pluginSetting(self._plugin_name, "request_timeout")))
        self.AUTO_OPEN_REPORT: bool = bool(self._organizer.pluginSetting(self._plugin_name, "auto_open_report"))

        self.GAME_NAME = self._organizer.managedGame().gameNexusName()
        if not self.GAME_NAME:
            log.warning("无法获取当前游戏的Nexus名称，将使用 'skyrimspecialedition' 作为备用。")
            self.GAME_NAME = 'skyrimspecialedition'

        self.NEXUS_BASE_URL = 'https://www.nexusmods.com'
        self.CATEGORY_PRIORITIES = {
            "VR": 10, "Modders Resources": 10, "Utilities": 10, "Bug Fixes": 11, "User Interface": 15,
            "Gameplay": 20, "Immersion": 21, "Combat": 25, "Stealth": 26, "Skills and Leveling": 30,
            "Magic - Gameplay": 35, "Races, Classes, and Birthsigns": 36, "Guilds/Factions": 40,
            "Quests and Adventures": 50, "Locations - New": 51, "Dungeons": 52, "Creatures and Mounts": 55,
            "NPC": 58, "Followers & Companions": 59, "Weapons": 60, "Armour": 61, "Clothing and Accessories": 62,
            "Items and Objects - Player": 65, "Models and Textures": 70, "Visuals and Graphics": 71,
            "Environmental": 72, "Animation": 75, "Body, Face, and Hair": 78, "Audio": 80,
            "Presets - ENB and ReShade": 85, "Overhauls": 90, "Miscellaneous": 95, "Patches": 99, "Default": 50
        }


# =============================================================================
# 2. 核心分析逻辑 (ModAnalyzer)
# =============================================================================
class ModAnalyzer:
    """
    核心分析类，所有功能逻辑的实现。
    """

    def __init__(self, organizer: mobase.IOrganizer, settings: PluginSettings, log_emitter: Any):
        self.organizer = organizer
        self.settings = settings
        self.log_emitter = log_emitter

        self.cache_data = self._load_cache()
        self.ignore_ids: Set[str] = set()
        self.replacement_map: Dict[str, str] = {}

        self.folder_to_id: Dict[str, str] = {}
        self.id_to_folders: Dict[str, List[str]] = defaultdict(list)
        self.installed_ids: Set[str] = set()

        self.playwright: Optional[PLAYWRIGHT_MODULE.sync_api.Playwright] = None
        self.browser: Optional[PLAYWRIGHT_MODULE.sync_api.Browser] = None
        self.page: Optional[PLAYWRIGHT_MODULE.sync_api.Page] = None

        self._load_rules()
        self._parse_installed_mods()

    def log(self, message: str, level: str = "info"):
        log_entry = f"[{level.upper()}] {message}"
        self.log_emitter.emit(log_entry)
        if level == "info":
            log.info(message)
        elif level == "warning":
            log.warning(message)
        elif level == "error":
            log.error(message)
        elif level == "critical":
            log.critical(message)

    def _save_playwright_cookies_to_json(self, cookies: List[Dict]):
        """
        [新函数] 将Playwright格式的Cookies保存为JSON文件，以便快速加载。
        """
        try:
            with open(self.settings.COOKIES_PATH, 'w', encoding='utf-8') as f:
                json.dump(cookies, f, indent=4)
            self.log(f"已成功将转换后的Cookies缓存到: {self.settings.COOKIES_PATH.name}")
        except IOError as e:
            self.log(f"保存Cookies JSON文件时出错: {e}", "error")

    def _load_mo2_cookies_and_convert(self, dat_path: Path) -> Optional[List[Dict]]:
        """
        [新函数] 读取MO2的nexus_cookies.dat文件，并将其转换为Playwright格式。
        """
        self.log(f"正在尝试从 '{dat_path.name}' 读取和转换Cookies...")
        if not dat_path.exists():
            self.log(f"'{dat_path.name}' 文件不存在。", "warning")
            return None

        playwright_cookies = []
        try:
            import struct
            from http.cookies import SimpleCookie
            with open(dat_path, 'rb') as f:
                # 1. 读取 quint32 (4字节, big-endian) 的cookie数量
                count_data = f.read(4)
                if len(count_data) < 4:
                    self.log("Cookies文件格式无效：无法读取数量。", "error")
                    return None
                cookie_count = struct.unpack('>I', count_data)[0]
                self.log(f"在.dat文件中发现 {cookie_count} 个Cookies。")
                self.log("注意: MO2默认读取的Cookies只包含API Cookies，无法使用较为高级的爬取功能")

                # 2. 循环读取每个cookie
                for _ in range(cookie_count):
                    # 2a. 读取 QByteArray 的 quint32 (4字节) 长度前缀
                    size_data = f.read(4)
                    if len(size_data) < 4:
                        break  # 文件提前结束
                    byte_array_size = struct.unpack('>I', size_data)[0]

                    # 2b. 读取原始cookie数据
                    raw_cookie_bytes = f.read(byte_array_size)

                    # 3. 解析原始cookie字符串
                    # QNetworkCookie::toRawForm() 产生的是HTTP头格式的字符串
                    # 使用 http.cookies.SimpleCookie 可以完美解析
                    cookie = SimpleCookie()
                    # 使用 latin-1 解码以避免Unicode错误，因为HTTP头是ASCII兼容的
                    cookie.load(raw_cookie_bytes.decode('latin-1'))

                    for name, morsel in cookie.items():
                        # 4. 转换为Playwright格式的字典
                        pw_cookie = {
                            'name': morsel.key,
                            'value': morsel.value,
                            'domain': morsel['domain'],
                            'path': morsel['path'],
                            'secure': bool(morsel['secure']),
                            'httpOnly': bool(morsel['httponly']),
                            'sameSite': morsel['samesite'] if morsel['samesite'] else "None",  # 提供默认值
                        }

                        # 处理过期时间
                        if morsel['expires']:
                            try:
                                # 解析 "Wdy, DD-Mon-YYYY HH:MM:SS GMT" 格式
                                expires_dt = datetime.strptime(morsel['expires'], "%a, %d-%b-%Y %H:%M:%S %Z")
                                # 转换为Unix时间戳（以秒为单位）
                                pw_cookie['expires'] = expires_dt.timestamp()
                            except ValueError:
                                # 如果格式不同，则忽略过期时间
                                pw_cookie['expires'] = -1
                        else:
                            pw_cookie['expires'] = -1

                        playwright_cookies.append(pw_cookie)

            self.log(f"成功转换 {len(playwright_cookies)} 个Cookies。")
            return playwright_cookies

        except Exception as e:
            self.log(f"读取或转换 '{dat_path.name}' 时发生错误: {e}", "error")
            return None

    def _load_cookies_from_json(self) -> list | None:
        """尝试从插件自己的JSON缓存加载Cookies。"""
        if not self.settings.COOKIES_PATH.exists():
            return None
        
        try:
            with open(self.settings.COOKIES_PATH, 'r', encoding='utf-8') as f:
                cookies = json.load(f)
            self.log(f"成功从缓存 '{self.settings.COOKIES_PATH.name}' 加载Cookies。")
            return cookies
        except (json.JSONDecodeError, IOError):
            self.log("缓存的cookies.json文件无效或损坏。", "warning")
            return None

    def _load_cookies_from_mo2_dat(self) -> list | None:
        """尝试从MO2的.dat文件加载、转换并缓存Cookies。"""
        self.log("尝试从MO2的.dat文件转换Cookies...")
        mo2_base_path = Path(self.organizer.basePath())
        mo2_cookies_dat_path = mo2_base_path / "webcache" / "nexus_cookies.dat"

        if not mo2_cookies_dat_path.exists():
            self.log("未找到MO2的 'nexus_cookies.dat' 文件。", "info")
            return None

        cookies = self._load_mo2_cookies_and_convert(mo2_cookies_dat_path)

        if cookies:  # 如果转换成功，保存为JSON格式以供下次直接使用
            self.log("成功从.dat文件转换Cookies，并保存为JSON缓存。")
            self._save_playwright_cookies_to_json(cookies)
            return cookies
        else:
            self.log("从.dat文件转换Cookies失败。", "warning")
            return None

    def _get_cookies(self) -> list | None:
        """
        按优先级获取Cookies。
        策略: 优先从JSON缓存加载，失败则尝试从MO2 .dat文件转换。
        """

        return self._load_cookies_from_json() or self._load_cookies_from_mo2_dat() or None

    def _launch_browser_with_cookies(self, cookies: list) -> bool:
        """使用给定的Cookies启动并配置Playwright浏览器。"""
        try:
            self.log("正在启动Playwright...")
            self.playwright = PLAYWRIGHT_MODULE.sync_api.sync_playwright().start()
            self.log("正在以无头模式启动浏览器...")
            self.browser = self.playwright.chromium.launch(headless=True)
            context = self.browser.new_context(
                user_agent='Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36'
            )
            context.add_cookies(cookies)
            self.page = context.new_page()
            self.log("浏览器启动并登录成功。")
            return True
        # 捕获所有可能的Playwright错误和通用异常
        except (PLAYWRIGHT_MODULE.sync_api.Error, Exception) as e:
            error_name = "Playwright" if isinstance(e, PLAYWRIGHT_MODULE.sync_api.Error) else "未知"
            self.log(f"初始化浏览器时发生{error_name}错误: {e}", "critical")
            if hasattr(self, 'playwright') and self.playwright:
                self.playwright.stop()
            return False

    def _initialize_browser(self) -> bool:
        """
        初始化Playwright浏览器并处理登录。
        高层逻辑: 获取Cookies -> 启动浏览器。
        """
        cookies = self._get_cookies()
        if cookies:
            return self._launch_browser_with_cookies(cookies)
        else:
            self.log(
                    f"请确保您的Cookies文件有效。该文件应位于:\n{self.settings.COOKIES_PATH}\n\n"
                    "如果文件不存在或已过期，您需要手动获取。请参考相关教程，使用浏览器开发者工具登录Nexus Mods后导出cookies并保存到上述路径。",
                    "error"
            )
            return False

    def close(self):
        self.log("正在关闭分析器...")
        self._save_cache()
        if self.browser:
            self.browser.close()
        if self.playwright:
            self.playwright.stop()
        self.log("分析器已安全关闭。")

    def _load_cache(self) -> Dict[str, Any]:
        if not self.settings.CACHE_FILE_PATH.exists(): return {}
        try:
            with open(self.settings.CACHE_FILE_PATH, 'r', encoding='utf-8') as f:
                self.log(f"成功加载缓存: {self.settings.CACHE_FILE_PATH.name}")
                return json.load(f)
        except (json.JSONDecodeError, IOError) as e:
            self.log(f"加载缓存文件失败: {e}，将使用空缓存。", "error");
            return {}

    def _save_cache(self):
        try:
            with open(self.settings.CACHE_FILE_PATH, 'w', encoding='utf-8') as f:
                json.dump(self.cache_data, f, indent=4, ensure_ascii=False)
                self.log(f"缓存已成功保存到: {self.settings.CACHE_FILE_PATH.name}")
        except IOError as e:
            self.log(f"保存缓存时出错: {e}", "error")

    def clear_cache(self):
        self.cache_data = {}
        if self.settings.CACHE_FILE_PATH.exists():
            try:
                os.remove(self.settings.CACHE_FILE_PATH)
                self.log(f"缓存文件 '{self.settings.CACHE_FILE_PATH.name}' 已被删除。")
            except OSError as e:
                self.log(f"删除缓存文件时出错: {e}", "error")

    def _load_rules(self):
        if not self.settings.RULES_PATH.exists():
            self.log(f"规则文件 '{self.settings.RULES_PATH.name}' 未找到，将自动创建模板。", "warning")
            self._create_default_rules_file()
            return
        self.log(f"正在从以下位置加载规则: {self.settings.RULES_PATH.name}")
        config = configparser.ConfigParser(allow_no_value=True)
        try:
            config.read(self.settings.RULES_PATH, encoding='utf-8')
            if 'Ignore' in config: self.ignore_ids = {key for key in config['Ignore']}
            if 'Replace' in config: self.replacement_map = {key: value for key, value in config['Replace'].items()}
            self.log(f"加载了 {len(self.ignore_ids)} 条 [Ignore] 和 {len(self.replacement_map)} 条 [Replace] 规则。")
        except configparser.Error as e:
            self.log(f"解析规则文件时出错: {e}", "error")

    def _create_default_rules_file(self):
        template_content = textwrap.dedent(f"""
        # 这是模组规则的配置文件。
        # 您可以在MO2插件的数据目录中找到此文件：
        # {self.settings.BASE_DIR}

        [Ignore]
        # 在此区域下的模组ID将被视为“已满足”，不会被报告为缺失。
        # 示例：
        # 12345

        [Replace]
        # 在此区域下，您可以定义替代关系。
        # 格式为: 被替代的模组ID = 用来替代的模组ID
        # 示例：一个旧的兼容补丁被一个整合版MOD取代
        # 44444 = 55555
        """)
        try:
            self.settings.RULES_PATH.write_text(template_content.strip(), encoding='utf-8')
            self.log(f"已成功创建规则文件模板: {self.settings.RULES_PATH}")
        except IOError:
            self.log("创建规则文件模板失败！", "error")

    def _parse_installed_mods(self):
        self.log("--- 正在使用 MO2 API 验证已启用模组并提取ID... ---")
        mod_list = self.organizer.modList()
        enabled_mods = mod_list.allModsByProfilePriority()

        for mod_name in enabled_mods:
            mod = mod_list.getMod(mod_name)
            if mod and not mod.isSeparator() and mod.nexusId() > 0:
                mod_id = str(mod.nexusId())
                self.folder_to_id[mod_name] = mod_id
                self.id_to_folders[mod_id].append(mod_name)
            else:
                self.log(f"跳过模组 '{mod_name}'，因为它是一个分隔符或缺少有效的Nexus ID。", "info")

        self.installed_ids = set(self.folder_to_id.values())
        self.log(f"已加载 {len(self.installed_ids)} 个唯一的已安装模组ID。")

    def _is_cache_entry_valid(self, entry: Dict[str, Any]) -> bool:
        if 'timestamp' not in entry: return False
        try:
            cache_time = datetime.fromisoformat(entry['timestamp'])
            return datetime.now() - cache_time < timedelta(days=self.settings.CACHE_EXPIRATION_DAYS)
        except ValueError:
            return False

    @staticmethod
    def _extract_mod_id_from_url(url: str) -> Optional[str]:

        if match := re.search(r'/mods/(\d+)', url): return match.group(1)
        return None

    def get_mod_data(self, mod_id: str) -> Dict[str, Any]:
        if mod_id in self.cache_data and self._is_cache_entry_valid(self.cache_data[mod_id]):
            return self.cache_data[mod_id]

        self.log(f"[在线抓取] {mod_id}")
        if not self.page: raise ConnectionError("Playwright 页面未初始化。")

        url = f"{self.settings.NEXUS_BASE_URL}/{self.settings.GAME_NAME}/mods/{mod_id}"
        try:
            self.page.goto(url, wait_until='domcontentloaded', timeout=self.settings.REQUEST_TIMEOUT)
            self.page.wait_for_selector('#pagetitle > h1', timeout=15000)
            soup = BS4_MODULE.BeautifulSoup(self.page.content(), 'html.parser')

            title_element = soup.select_one('#pagetitle > h1')
            mod_name = title_element.get_text(strip=True) if title_element else "未知模组名称"

            category_items = soup.select("ul#breadcrumb li a")
            category = category_items[-1].get_text(strip=True) if len(category_items) > 1 else "Default"

            def scrape_dep_section(header_text: str) -> List[Dict[str, str]]:
                dependencies = []
                header = soup.find('h3', string=lambda t: bool(t) and header_text.lower() in t.lower().strip())
                if header and (table := header.find_next_sibling('table', class_='desc-table')):
                    for row in table.select('tbody tr'):
                        if (name_cell := row.find('td', class_='table-require-name')) and (link := name_cell.find('a')):
                            dep_url = link['href'] if link['href'].startswith(
                                'http') else self.settings.NEXUS_BASE_URL + link['href']
                            notes = (notes_cell.get_text(strip=True) if (
                                notes_cell := row.find('td', class_='table-require-notes')) else "")
                            dependencies.append({'name': link.get_text(strip=True), 'url': dep_url, 'notes': notes})
                return dependencies

            new_entry = {
                "name": mod_name, "category": category, "timestamp": datetime.now().isoformat(),
                "dependencies": {'requires': scrape_dep_section('Nexus requirements'),
                                 'required_by': scrape_dep_section('Mods requiring this file')}
            }
            self.cache_data[mod_id] = new_entry
            self.log(f"[已抓取] {mod_name} ({mod_id})")
            return new_entry
        except Exception as e:
            self.log(f"[抓取失败] {mod_id}: {type(e).__name__}", "error")
            return {"name": f"抓取失败: ID {mod_id}", "error": str(e), "category": "Default", "dependencies": {}}

    def _get_effective_id(self, required_id: str) -> str:
        return self.replacement_map.get(required_id, required_id)

    def _is_dependency_satisfied(self, required_id: str) -> bool:
        return self._get_effective_id(required_id) in self.installed_ids

    def analyze_single_mod_dependencies(self, initial_mod_id: str) -> str:
        self.log(f"--- 开始分析单个模组的缺失依赖 (ID: {initial_mod_id}) ---")
        dependency_tree = self._build_dependency_tree(initial_mod_id, set())
        output_path = self.settings.BASE_DIR / f"dependency_tree_{initial_mod_id}.html"
        self._generate_tree_html_report(dependency_tree, output_path)
        self.log(f"--- 依赖树分析完成。报告已生成: {output_path.resolve()} ---", "info")
        return str(output_path.resolve())

    def _build_dependency_tree(self, mod_id: str, visited_ids: Set[str]) -> Dict[str, Any]:
        node: Dict[str, Any] = {"id": mod_id, "name": "加载中...", "children": []}
        if mod_id in visited_ids:
            node.update({"name": "检测到循环依赖", "status": "cycle"});
            return node

        visited_ids.add(mod_id)
        mod_data = self.get_mod_data(mod_id)
        node['name'] = mod_data.get("name", f"ID: {mod_id}")

        effective_id = self._get_effective_id(mod_id)
        node['replacement_info'] = None
        if mod_id != effective_id:
            replacer_data = self.get_mod_data(effective_id)
            node['replacement_info'] = {"name": replacer_data.get('name', f'ID {effective_id}'), "id": effective_id}

        status = "missing"
        if mod_id in self.ignore_ids:
            status = "ignored"
        elif effective_id in self.installed_ids:
            status = "satisfied"
        node['status'] = status

        if status in ('ignored', 'cycle') or "dependencies" not in mod_data:
            return node

        for req in mod_data.get("dependencies", {}).get("requires", []):
            if req_id := self._extract_mod_id_from_url(req['url']):
                child_node = self._build_dependency_tree(req_id, visited_ids.copy())
                child_node['notes'] = req.get('notes', '')
                node["children"].append(child_node)
        return node

    def _generate_tree_html_report(self, tree_data: Dict[str, Any], output_path: Path):
        self.log(f"正在为依赖树生成HTML报告 -> {output_path}")

        def render_node(node: Dict[str, Any]) -> str:
            status_map = {"satisfied": ("satisfied", "✔"), "missing": ("missing", "❌"), "ignored": ("ignored", "➖"),
                          "cycle": ("cycle", "LOOP")}
            status_class, status_icon = status_map.get(node.get("status", "missing"), ("missing", "❌"))
            original_mod_name = node['name']
            original_mod_id = node['id']
            original_nexus_url = f"{self.settings.NEXUS_BASE_URL}/{self.settings.GAME_NAME}/mods/{original_mod_id}"
            if r_info := node.get('replacement_info'):
                replacer_name = r_info['name']
                replacer_id = r_info['id']
                replacer_nexus_url = f"{self.settings.NEXUS_BASE_URL}/{self.settings.GAME_NAME}/mods/{replacer_id}"
                main_text = f"<a href='{replacer_nexus_url}' target='_blank'>{replacer_name}</a> (ID: {replacer_id})"
                sub_text = f" <span class='replacement-info'>(作为 <a href='{original_nexus_url}'>{original_mod_name}</a> 的替代)</span>"
            else:
                main_text = f"<a href='{original_nexus_url}' target='_blank'>{original_mod_name}</a> (ID: {original_mod_id})"
                sub_text = ""
            notes_html = f" <span class='notes'>({node.get('notes', '')})</span>" if node.get('notes') else ""
            html = f"<li class='{status_class}'><span class='icon'>{status_icon}</span> {main_text}{sub_text}{notes_html}"
            if node["children"]:
                html += "<ul>" + "".join([render_node(child) for child in node["children"]]) + "</ul>"
            return html + "</li>"

        html_content = f"""
        <!DOCTYPE html><html lang="zh-CN"><head><meta charset="UTF-8"><title>模组缺失依赖树报告</title><style>{textwrap.dedent("""
            body{font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; padding:20px; line-height: 1.6;} h1{text-align:center;border-bottom:2px solid #3498db;padding-bottom:10px} ul{list-style-type:none;padding-left:25px;border-left:1px dashed #ccc} li{margin:10px 0} a{text-decoration:none;color:#2980b9} a:hover{text-decoration:underline} .icon{display:inline-block;width:24px;text-align:center;margin-right:8px;font-size:1.2em} .notes{font-style:italic;color:#7f8c8d;font-size:0.9em} .replacement-info, .replacement-info a{font-style:italic;color:#3498db;font-size:0.9em; font-weight: bold;} .satisfied{color:#27ae60} .missing{color:#c0392b} .ignored{color:#7f8c8d} .cycle{color:#f39c12}
        """)}</style></head><body>
        <h1>模组缺失依赖树报告 (起始模组: {tree_data['name']})</h1><ul>{render_node(tree_data)}</ul><hr>
        <p>图例: <span class="satisfied">✔ 已满足</span> | <span class="missing">❌ 缺失</span> | <span class="ignored">➖ 已忽略</span> | <span class="cycle">LOOP 循环依赖</span></p>
        </body></html>"""
        output_path.write_text(textwrap.dedent(html_content).strip(), encoding='utf-8')

    def generate_sorted_load_order(self) -> str:
        self.log("--- 开始对MO2模组进行终极分类拓扑排序 ---")
        if not self.folder_to_id:
            self.log("未找到任何带有有效ID的已启用模组，无法生成排序。", "error");
            return ""
        full_graph, reverse_graph, all_nodes = self._build_full_dependency_network()
        missing_mods_report = self._identify_missing_dependencies(all_nodes, reverse_graph)
        sorted_order, cyclic_nodes = self._perform_topological_sort(full_graph)
        output_path = self.settings.BASE_DIR / "suggested_load_order.html"
        self._generate_sort_html_report(sorted_order, cyclic_nodes, missing_mods_report, full_graph, output_path)
        self.log(f"--- 排序分析完成。报告已生成: {output_path.resolve()} ---", "info")
        return str(output_path.resolve())

    def _build_full_dependency_network(self) -> Tuple[defaultdict, defaultdict, set]:
        self.log("--- 正在构建完整依赖网络... ---")
        graph, reverse_graph = defaultdict(list), defaultdict(list)
        nodes_to_process = deque(self.installed_ids)
        processed_nodes = set()
        while nodes_to_process:
            current_id = nodes_to_process.popleft()
            if current_id in processed_nodes: continue
            processed_nodes.add(current_id)
            mod_data = self.get_mod_data(current_id)
            if "dependencies" in mod_data:
                for req in mod_data.get("dependencies", {}).get("requires", []):
                    if req_id := self._extract_mod_id_from_url(req['url']):
                        notes = req.get('notes', '')
                        graph[current_id].append({'id': req_id, 'notes': notes})
                        reverse_graph[req_id].append({'id': current_id, 'notes': notes})
                        if req_id not in processed_nodes: nodes_to_process.append(req_id)
        return graph, reverse_graph, processed_nodes

    def _identify_missing_dependencies(self, all_nodes: Set[str], reverse_graph: defaultdict) -> Dict[str, Dict]:
        unmet_dependencies = {nid for nid in all_nodes if
                              not self._is_dependency_satisfied(nid) and nid not in self.ignore_ids}
        if not unmet_dependencies: return {}
        self.log(f"检测到 {len(unmet_dependencies)} 个未满足的前置需求。", "warning")
        missing_report = {}
        for unmet_id in sorted(list(unmet_dependencies)):
            req_by_installed, req_by_missing = [], set()
            for req_info in reverse_graph.get(unmet_id, []):
                req_by_id = req_info['id']
                notes = req_info['notes']
                if req_by_id in self.installed_ids:
                    for folder_name in self.id_to_folders.get(req_by_id, []):
                        req_by_installed.append((folder_name, notes))
                elif self._get_effective_id(req_by_id) in unmet_dependencies:
                    req_by_missing.add((self.get_mod_data(req_by_id).get("name", f"ID {req_by_id}"), req_by_id))
            effective_id = self._get_effective_id(unmet_id)
            report_entry = {
                "name": self.get_mod_data(unmet_id).get("name", f"ID {unmet_id}"),
                "required_by_installed": sorted(req_by_installed, key=lambda x: x[0]),
                "required_by_missing": sorted(list(req_by_missing)), "effective_id": effective_id
            }
            if unmet_id != effective_id:
                report_entry['effective_name'] = self.get_mod_data(effective_id).get('name', f'ID {effective_id}')
            missing_report[unmet_id] = report_entry
        return missing_report

    def _perform_topological_sort(self, full_graph: defaultdict) -> Tuple[List[str], List[str]]:
        self.log("--- 正在执行带权重的全局拓扑排序... ---")
        graph, in_degree = defaultdict(list), {f: 0 for f in self.folder_to_id}
        for dep_folder, dep_id in self.folder_to_id.items():
            for req_info in full_graph.get(dep_id, []):
                req_id = req_info['id']
                if not self._is_dependency_satisfied(req_id): continue
                actual_provider_id = self._get_effective_id(req_id)
                for provider_folder in self.id_to_folders.get(actual_provider_id, []):
                    if provider_folder in in_degree:
                        graph[provider_folder].append(dep_folder)
                        in_degree[dep_folder] += 1
        ready_queue = []
        for folder, degree in in_degree.items():
            if degree == 0:
                mod_id = self.folder_to_id[folder]
                priority = self.settings.CATEGORY_PRIORITIES.get(self.get_mod_data(mod_id).get("category", "Default"),
                                                                 50)
                heapq.heappush(ready_queue, (priority, folder))
        sorted_order = []
        while ready_queue:
            _, u_folder = heapq.heappop(ready_queue)
            sorted_order.append(u_folder)
            for v_folder in graph.get(u_folder, []):
                in_degree[v_folder] -= 1
                if in_degree[v_folder] == 0:
                    v_prio = self.settings.CATEGORY_PRIORITIES.get(
                        self.get_mod_data(self.folder_to_id[v_folder]).get("category", "Default"), 50)
                    heapq.heappush(ready_queue, (v_prio, v_folder))
        cyclic_nodes = [f for f, d in in_degree.items() if d > 0]
        if cyclic_nodes:
            self.log(f"检测到循环依赖！涉及的模组: {', '.join(cyclic_nodes)}", "error")
        return sorted_order, cyclic_nodes

    def _generate_sort_html_report(self, sorted_order, cyclic_nodes, missing_report, full_graph, output_path):
        self.log(f"正在生成终极排序HTML报告 -> {output_path}")
        missing_html = ""
        if missing_report:
            items = []
            for unmet_id, data in missing_report.items():
                effective_id, effective_name = data['effective_id'], data.get('effective_name', data['name'])
                req_url = f"{self.settings.NEXUS_BASE_URL}/{self.settings.GAME_NAME}/mods/{effective_id}"
                title_html = f"<a href='{req_url}' target='_blank'>{effective_name}</a> (ID: {effective_id})"
                if unmet_id != effective_id:
                    original_url = f"{self.settings.NEXUS_BASE_URL}/{self.settings.GAME_NAME}/mods/{unmet_id}"
                    title_html = f"{title_html} <span class='replacement-info'>(作为 <a href='{original_url}'>{data['name']}</a> 的替代)</span>"
                details_parts = []
                if data['required_by_installed']:
                    installed_requirers = []
                    for folder_name, notes in data['required_by_installed']:
                        note_html = f" <span class='notes'>({notes})</span>" if notes else ""
                        installed_requirers.append(f"<strong>{folder_name}</strong>{note_html}")
                    details_parts.append(
                        f"<em>被以下 <strong class='dep-satisfied'>已安装</strong> 模组需要:</em> {', '.join(installed_requirers)}")
                if data['required_by_missing']:
                    missing_links = [
                        f"<a href='{self.settings.NEXUS_BASE_URL}/{self.settings.GAME_NAME}/mods/{req_id}' target='_blank'>{name}</a>"
                        for name, req_id in data['required_by_missing']]
                    details_parts.append(
                        f"<em>被以下 <strong class='dep-missing'>未安装</strong> 模组需要:</em> {', '.join(missing_links)}")
                items.append(f"<li>{title_html}<div class='details'>{'<br>'.join(details_parts)}</div></li>")
            missing_html = f"<div class='warning-box'><h2>注意：检测到 {len(missing_report)} 个未满足的前置需求！</h2><p>您需要安装以下模组，或在`{self.settings.RULES_PATH.name}`中将其设为忽略/替代。</p><ul>{''.join(items)}</ul></div>"

        cyclic_html = ""
        if cyclic_nodes:
            items = [f"<li>{mod} (ID: {self.folder_to_id.get(mod, 'N/A')})</li>" for mod in cyclic_nodes]
            cyclic_html = f"<div class='error-box'><h2>检测到循环依赖！</h2><p>无法完成排序。请检查以下模组之间的依赖关系：</p><ul>{''.join(items)}</ul></div>"
        body_content = ""
        if not cyclic_nodes:
            rows, last_priority = [], -1
            priority_to_category = {v: k for k, v in self.settings.CATEGORY_PRIORITIES.items()}
            for i, folder_name in enumerate(sorted_order):
                mod_id = self.folder_to_id.get(folder_name)
                mod_data = self.get_mod_data(mod_id)
                priority = self.settings.CATEGORY_PRIORITIES.get(mod_data.get("category", "Default"), 50)
                if priority != last_priority:
                    cat_name = next((name for p, name in sorted(priority_to_category.items()) if p == priority),
                                    "未知分类")
                    rows.append(
                        f"<tr class='category-header'><td colspan='4'>--- {priority:02d}. {cat_name} ---</td></tr>")
                    last_priority = priority
                nexus_url = f"{self.settings.NEXUS_BASE_URL}/{self.settings.GAME_NAME}/mods/{mod_id}" if mod_id else "#"
                dep_parts = []
                if mod_id and mod_id in full_graph:
                    for req_info in full_graph.get(mod_id, []):
                        req_id, notes = req_info['id'], req_info['notes']
                        note_html = f" <span class='notes'>({notes})</span>" if notes else ""
                        if req_id in self.ignore_ids: continue
                        effective_id = self._get_effective_id(req_id)
                        if effective_id in self.installed_ids:
                            provider_folders = ", ".join(self.id_to_folders.get(effective_id, ['?']))
                            replace_note = f" (替代 <span class='dep-original'>{self.get_mod_data(req_id).get('name', f'ID {req_id}')}</span>)" if req_id != effective_id else ""
                            dep_parts.append(
                                f"<span class='dep-satisfied'>{provider_folders}{replace_note}{note_html}</span>")
                        else:
                            req_name, eff_name = self.get_mod_data(req_id).get("name"), self.get_mod_data(
                                effective_id).get("name")
                            req_url = f"{self.settings.NEXUS_BASE_URL}/{self.settings.GAME_NAME}/mods/{effective_id}"
                            replace_note = f" (替代 {req_name})" if req_id != effective_id else ""
                            dep_parts.append(
                                f"<span class='dep-missing'><a href='{req_url}' target='_blank'>{eff_name}</a>{replace_note}{note_html}</span>")
                deps_html = ", ".join(dep_parts) or "<span class='no-deps'>无</span>"
                rows.append(
                    f"<tr><td>{i + 1}</td><td><strong>{folder_name}</strong><br><span class='nexus-name'>{mod_data.get('name', 'N/A')}</span></td><td><a href='{nexus_url}' target='_blank'>{mod_id or 'N/A'}</a></td><td>{deps_html}</td></tr>")
            body_content = f"<h2>MO2左侧面板建议顺序</h2><p>共排序 {len(sorted_order)} 个模组。</p><table><thead><tr><th>#</th><th>模组文件夹</th><th>Nexus ID</th><th>直接前置依赖</th></tr></thead><tbody>{''.join(rows)}</tbody></table>"

        html_style = textwrap.dedent("""
            body{font-family:-apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;margin:20px;background-color:#f8f9fa; line-height: 1.6;} h1,h2{color:#343a40;border-bottom:2px solid #007bff;padding-bottom:10px} table{width:100%;border-collapse:collapse;margin-top:20px;box-shadow:0 2px 5px rgba(0,0,0,0.1)} th,td{padding:12px 15px;text-align:left;border-bottom:1px solid #dee2e6; vertical-align: top;} th{background-color:#007bff;color:white} tr:nth-child(even){background-color:#f2f2f2} tr:hover{background-color:#e9ecef} a{color:#0056b3;text-decoration:none} a:hover{text-decoration:underline} .nexus-name,.details{font-size:0.9em;color:#6c757d} .details{margin-top: 5px; padding-left: 10px; border-left: 2px solid #ddd;} .notes{font-style:italic;color:#5a6268;font-size:0.9em; margin-left: 4px;} .no-deps{color:#28a745;font-style:italic} .dep-satisfied, .dep-satisfied strong{color: #1e6b20;} .dep-original{color: #555; text-decoration: line-through;} .dep-missing, .dep-missing a, .dep-missing strong{color:#c0392b !important; font-weight: bold;} .replacement-info, .replacement-info a{font-style:italic;color:#3498db;font-size:0.9em; font-weight: bold;} .error-box,.warning-box{padding:1rem 1.5rem;margin: 20px 0;border-radius:5px} .error-box{background-color:#f8d7da;color:#721c24;border:1px solid #f5c6cb} .warning-box{background-color:#fff3cd;color:#856404;border:1px solid #ffeeba} .warning-box h2,.error-box h2{border:none;margin-top:0} .warning-box li{margin:10px 0} .category-header td{background-color:#e9ecef;font-weight:bold;color:#495057; text-align: center;}
            """)
        html = f"<!DOCTYPE html><html lang='zh-CN'><head><meta charset='UTF-8'><title>MO2模组智能排序报告</title><style>{html_style}</style></head><body><h1>MO2模组智能排序报告</h1>{missing_html}{cyclic_html}{body_content}</body></html>"
        output_path.write_text(textwrap.dedent(html).strip(), encoding='utf-8')


# =============================================================================
# 3. 后台工作线程 (Worker)
# =============================================================================
class Worker(QObject):
    progress = pyqtSignal(str)
    analysis_finished = pyqtSignal(str)
    error = pyqtSignal(str)

    def __init__(self, organizer: mobase.IOrganizer, plugin_name: str):
        super().__init__()
        self.organizer = organizer
        self.plugin_name = plugin_name
        self.settings = PluginSettings(organizer, plugin_name)
        self.analyzer: ModAnalyzer = None # type: ignore

    def _run_analysis(self, analysis_func):
        try:
            self.analyzer = ModAnalyzer(self.organizer, self.settings, self.progress)
            if not self.analyzer._initialize_browser():
                self.error.emit(
                    f"浏览器初始化失败！请检查日志获取更多信息。"
                )
                if self.analyzer: self.analyzer.close()
                return
            result_path = analysis_func()
            if self.analyzer: self.analyzer.close()
            if result_path:
                self.analysis_finished.emit(result_path)
            else:
                if analysis_func.__name__ != 'clear_cache':
                    self.error.emit("分析未能生成报告。请检查日志获取更多信息。")
        except Exception as e:
            log.exception("分析过程中发生未捕获的错误。")
            self.error.emit(f"发生严重错误: {e}\n\n请检查MO2日志获取详细信息。")
            if self.analyzer: self.analyzer.close()

    def run_single_mod_analysis(self, mod_id: str):
        self._run_analysis(lambda: self.analyzer.analyze_single_mod_dependencies(mod_id))

    def run_full_profile_analysis(self):
        self._run_analysis(lambda: self.analyzer.generate_sorted_load_order())

    def clear_cache(self):
        try:
            settings = PluginSettings(self.organizer, self.plugin_name)
            cache_file = settings.CACHE_FILE_PATH
            if cache_file.exists():
                os.remove(cache_file)
                self.progress.emit(f"[SUCCESS] 缓存文件 '{cache_file.name}' 已成功清理。")
            else:
                self.progress.emit("[INFO] 缓存文件不存在，无需清理。")
        except Exception as e:
            self.error.emit(f"清理缓存时出错: {e}")


# =============================================================================
# 4. 插件UI界面 (AnalyzerDialog)
# =============================================================================
class AnalyzerDialog(QDialog):
    start_single_analysis_signal = pyqtSignal(str)
    start_full_analysis_signal = pyqtSignal()
    start_clear_cache_signal = pyqtSignal()

    def __init__(self, organizer: mobase.IOrganizer, plugin_name: str, parent=None):
        super().__init__(parent)
        self.organizer = organizer
        self.plugin_name = plugin_name
        self.settings = PluginSettings(organizer, plugin_name)
        self.worker: Optional[Worker] = None
        self.thread: Optional[QThread] = None
        self._init_ui()
        self._setup_worker()

    def _init_ui(self):
        self.setWindowTitle("Nexus Mods 依赖分析器")
        self.setMinimumSize(600, 450)
        layout = QVBoxLayout(self)
        single_mod_group = QGroupBox("依赖树分析 (单个模组)")
        single_mod_layout = QHBoxLayout()
        single_mod_layout.addWidget(QLabel("Nexus Mod ID:"))
        self.mod_id_input = QLineEdit()
        self.mod_id_input.setPlaceholderText("例如: 3863")
        single_mod_layout.addWidget(self.mod_id_input)
        self.analyze_single_btn = QPushButton("开始分析")
        single_mod_layout.addWidget(self.analyze_single_btn)
        single_mod_group.setLayout(single_mod_layout)
        layout.addWidget(single_mod_group)
        full_sort_group = QGroupBox("MO2 智能排序 (整个配置)")
        full_sort_layout = QVBoxLayout()
        full_sort_layout.addWidget(QLabel("此功能将分析您所有已启用的模组，并生成一份详细的左侧面板排序报告。"))
        self.analyze_full_btn = QPushButton("生成完整排序报告")
        full_sort_layout.addWidget(self.analyze_full_btn)
        full_sort_group.setLayout(full_sort_layout)
        layout.addWidget(full_sort_group)
        log_group = QGroupBox("状态与日志")
        log_layout = QVBoxLayout()
        self.log_output = QPlainTextEdit()
        self.log_output.setReadOnly(True)
        self.log_output.setLineWrapMode(QPlainTextEdit.LineWrapMode.NoWrap)
        log_layout.addWidget(self.log_output)
        log_group.setLayout(log_layout)
        layout.addWidget(log_group, 1)
        bottom_layout = QHBoxLayout()
        self.clear_cache_btn = QPushButton("清理缓存")
        bottom_layout.addWidget(self.clear_cache_btn)
        self.open_rules_btn = QPushButton("打开规则文件")
        bottom_layout.addWidget(self.open_rules_btn)
        bottom_layout.addStretch()
        self.close_btn = QPushButton("关闭")
        bottom_layout.addWidget(self.close_btn)
        layout.addLayout(bottom_layout)
        self.analyze_single_btn.clicked.connect(self.trigger_single_mod_analysis)
        self.analyze_full_btn.clicked.connect(self.trigger_full_profile_analysis)
        self.clear_cache_btn.clicked.connect(self.trigger_clear_cache)
        self.open_rules_btn.clicked.connect(self.open_rules_file)
        self.close_btn.clicked.connect(self.close)

    def _setup_worker(self):
        self.thread = QThread()
        self.worker = Worker(self.organizer, self.plugin_name)
        self.worker.moveToThread(self.thread)
        self.worker.progress.connect(self.log_message)
        self.worker.analysis_finished.connect(self.on_analysis_finished)
        self.worker.error.connect(self.on_error)
        self.start_single_analysis_signal.connect(self.worker.run_single_mod_analysis)
        self.start_full_analysis_signal.connect(self.worker.run_full_profile_analysis)
        self.start_clear_cache_signal.connect(self.worker.clear_cache)
        self.thread.start()

    def _set_ui_enabled(self, enabled: bool):
        self.analyze_single_btn.setEnabled(enabled)
        self.analyze_full_btn.setEnabled(enabled)
        self.clear_cache_btn.setEnabled(enabled)
        self.mod_id_input.setEnabled(enabled)

    def log_message(self, message: str):
        self.log_output.appendPlainText(f"[{datetime.now().strftime('%H:%M:%S')}] {message}")
        self.log_output.moveCursor(QTextCursor.MoveOperation.End)

    def trigger_single_mod_analysis(self):
        mod_id = self.mod_id_input.text().strip()
        if not mod_id.isdigit():
            QMessageBox.warning(self, "输入无效", "请输入一个纯数字的 Nexus Mod ID。")
            return
        self._set_ui_enabled(False)
        self.log_output.clear()
        self.log_message(f"--- 开始分析单个模组 (ID: {mod_id}) ---")
        self.start_single_analysis_signal.emit(mod_id)

    def trigger_full_profile_analysis(self):
        self._set_ui_enabled(False)
        self.log_output.clear()
        self.log_message("--- 开始完整配置文件分析与排序 ---")
        self.start_full_analysis_signal.emit()

    def trigger_clear_cache(self):
        reply = QMessageBox.question(self, "确认清理",
                                     "您确定要删除所有已缓存的 Nexus Mods 数据吗？\n下次分析将会重新从网站抓取所有数据，速度会变慢。",
                                     QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                                     QMessageBox.StandardButton.No)
        if reply == QMessageBox.StandardButton.Yes:
            self.log_message("--- 正在清理缓存... ---")
            self.start_clear_cache_signal.emit()

    def on_analysis_finished(self, report_path: str):
        self._set_ui_enabled(True)
        self.log_message(f"[SUCCESS] 分析完成！报告已保存至: {report_path}")
        if self.settings.AUTO_OPEN_REPORT:
            webbrowser.open(f'file:///{report_path}')
        else:
            reply = QMessageBox.information(self, "分析完成",
                                            f"报告已成功生成。\n\n路径: {report_path}\n\n是否立即在浏览器中打开？",
                                            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                                            QMessageBox.StandardButton.Yes)
            if reply == QMessageBox.StandardButton.Yes:
                webbrowser.open(f'file:///{report_path}')

    def on_error(self, message: str):
        self._set_ui_enabled(True)
        self.log_message(f"[ERROR] {message}")
        QMessageBox.critical(self, "发生错误", message)

    def open_rules_file(self):
        rules_path = self.settings.RULES_PATH
        if not rules_path.exists():
            try:
                temp_analyzer = ModAnalyzer(self.organizer, self.settings, self.log_message)
                temp_analyzer._create_default_rules_file()
                self.log_message(f"规则文件已创建于: {rules_path}")
            except Exception as e:
                self.on_error(f"创建规则文件失败: {e}")
                return
        self.log_message(f"正在打开规则文件: {rules_path}")
        os.startfile(rules_path)

    def closeEvent(self, event):
        self.log_message("正在关闭窗口和后台线程...")
        if self.thread and self.thread.isRunning():
            self.thread.quit()
            self.thread.wait(3000)
        super().closeEvent(event)


# =============================================================================
# 5. MO2插件主类
# =============================================================================
class ModDepAnalyzerPlugin(mobase.IPluginTool):

    def __init__(self):
        super().__init__()
        self._organizer: mobase.IOrganizer = None # type: ignore
        self._window: Optional[AnalyzerDialog] = None

    def init(self, organizer: mobase.IOrganizer) -> bool:
        self._organizer = organizer

        # 在路径添加后，进行依赖检查
        # global DEPENDENCIES_MET, BS4_MODULE, PLAYWRIGHT_MODULE
        # try:
        #     # 将导入的模块存储在全局变量中，以供其他部分使用
        #     import bs4
        #     print("bs4 ok")
        #     print(sys.path, site.getsitepackages())
        #     import playwright.sync_api
        #     BS4_MODULE = bs4
        #     PLAYWRIGHT_MODULE = playwright
        #     DEPENDENCIES_MET = True
        # except ImportError as e:
        #     DEPENDENCIES_MET = False
        #     log.warning(f"{self.name()} 依赖库不齐全，报错如下：{e}。请将 bs4 和 playwright 库重新安装")

        return True

    def name(self) -> str:
        return "Nexus Mods Dependency Analyzer"

    def author(self) -> str:
        return "Gemini AI"

    def description(self) -> str:
        return "一个分析 Nexus Mods 依赖关系并为 MO2 生成排序建议的工具。"

    def version(self) -> mobase.VersionInfo:
        return mobase.VersionInfo(2, 2, 0, mobase.ReleaseType.FINAL)

    def isActive(self) -> bool:
        return DEPENDENCIES_MET

    def displayName(self) -> str:
        return "Nexus Mods 依赖分析器"

    def tooltip(self) -> str:
        return "启动依赖分析工具"

    def icon(self) -> QIcon:
        return QIcon(":/MO/gui/icons/search-list")

    def settings(self) -> List[mobase.PluginSetting]:
        """定义此插件的设置。"""
        return [
            mobase.PluginSetting(
                "cache_expiration_days",
                "缓存文件的有效期（天）。减少此值会更频繁地从Nexus获取新数据，但会降低分析速度。",
                180
            ),
            mobase.PluginSetting(
                "request_timeout",
                "网络请求的超时时间（毫秒）。如果您的网络状况不佳，可以尝试增加此值。",
                45000
            ),
            mobase.PluginSetting(
                "auto_open_report",
                "分析完成后是否自动在浏览器中打开HTML报告文件。",
                True
            )
        ]

    def display(self):
        if not DEPENDENCIES_MET:
            libs_path = Path(self._organizer.pluginDataPath()) / self.name() / 'libs'
            msg = (
                f"此插件的依赖库缺失！\n\n"
                f"请将 'bs4' (Beautiful Soup) 和 'playwright' 库文件夹复制到以下目录：\n\n"
                f"{libs_path}\n\n"
                f"您可以通在其他Python环境中使用 `pip install beautifulsoup4 playwright` 安装它们，"
                f"然后从该环境的 `site-packages` 目录中找到对应的文件夹进行复制。\n\n"
                f"完成后请重启 MO2。"
            )
            QMessageBox.critical(None, "缺少依赖项", msg)
            return

        if self._window is None or not self._window.isVisible():
            self._window = AnalyzerDialog(self._organizer, self.name())

        self._window.show()
        self._window.raise_()
        self._window.activateWindow()


