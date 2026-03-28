import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import webbrowser
import zipfile
import ctypes
from html import unescape
from dataclasses import dataclass
from pathlib import Path
from queue import Empty, Queue
from tempfile import TemporaryDirectory
from urllib.error import HTTPError, URLError
from urllib.parse import urlparse
from urllib.request import Request, urlopen

import tkinter as tk
from tkinter import filedialog, messagebox, ttk


APP_DIR = Path(sys.executable).resolve().parent if getattr(sys, "frozen", False) else Path(__file__).resolve().parent
RESOURCE_DIR = Path(getattr(sys, "_MEIPASS", APP_DIR))
BASE_DIR = APP_DIR
USER_DATA_DIR = Path(os.environ.get("LOCALAPPDATA") or os.environ.get("APPDATA") or APP_DIR) / "EH Patcher"
CONFIG_PATH = USER_DATA_DIR / "patches.json"
if not CONFIG_PATH.exists():
    CONFIG_PATH = APP_DIR / "patches.json"
if not CONFIG_PATH.exists():
    CONFIG_PATH = RESOURCE_DIR / "patches.json"
TRANSLATIONS_PATH = APP_DIR / "translations.json"
if not TRANSLATIONS_PATH.exists():
    TRANSLATIONS_PATH = RESOURCE_DIR / "translations.json"
SETTINGS_PATH = USER_DATA_DIR / "settings.json"
PATCH_STATE_PATH = USER_DATA_DIR / "patch_state.json"
PATCH_DATA_DIR = USER_DATA_DIR / ".patcher-data"
PATCH_BACKUPS_DIR = PATCH_DATA_DIR / "backups"
PATCH_DOWNLOAD_CACHE_DIR = PATCH_DATA_DIR / "downloads"
ICON_PATH = RESOURCE_DIR / "icon.png"
APP_ICON_PATH = RESOURCE_DIR / "icon-app.png"
ICON_ICO_PATH = RESOURCE_DIR / "icon.ico"
WINDOW_TITLE = "Ebonhold HD Patcher"
APP_VERSION = "1.0.0"
BUG_REPORTS_URL = "https://github.com/SypherRed/eh-patcher/issues"
DEFAULT_SEARCH_TARGET_NAME = "ebonhold"
DOWNLOAD_TIMEOUT_SECONDS = 20
DOWNLOAD_CHUNK_SIZE = 1024 * 512
GITHUB_API_TIMEOUT_SECONDS = 20
DEFAULT_LANGUAGE = "en"
LANGUAGES = [("English", "en"), ("Deutsch", "de"), ("Espanol", "es"), ("Italiano", "it")]
GROUP_TOGGLE_GUTTER = 28
PATCH_BASE_INDENT = 56
PATCH_CHILD_INDENT = 24
IMAGE_FILE_LARGE_ADDRESS_AWARE = 0x20
SEARCH_STATUS_INTERVAL = 150


@dataclass
class PatchSource:
    label: str
    url: str


@dataclass
class PatchDefinition:
    id: str
    name: dict[str, str]
    description: dict[str, str]
    patch_type: str
    target_subdirectories: list[str]
    expected_files: list[str]
    requires: str | None
    selects: list[str]
    target_executable: str | None
    sources: list[PatchSource]


@dataclass
class PatchGroup:
    id: str
    name: dict[str, str]
    description: dict[str, str]
    items: list[PatchDefinition]


class PatcherApp:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.lang = DEFAULT_LANGUAGE
        self.translations = self.read_json(TRANSLATIONS_PATH, default={})
        self.settings = self.read_json(SETTINGS_PATH, default={})
        self.patch_state = self.read_json(PATCH_STATE_PATH, default={"installs": []})
        self.queue: Queue = Queue()
        self.install_tool_path = self.find_extractor()
        self.is_busy = False
        self.updating_group_state = False
        self.status_refresh_job: str | None = None
        self.current_version = APP_VERSION
        self.update_repo = ""
        self.update_asset_name = ""

        self.groups, self.standalone_patches = self.load_config()
        self.group_vars: dict[str, tk.BooleanVar] = {}
        self.group_children: dict[str, list[tuple[PatchDefinition, tk.BooleanVar]]] = {}
        self.group_expanded: dict[str, tk.BooleanVar] = {}
        self.group_item_frames: dict[str, ttk.Frame] = {}
        self.group_toggle_buttons: dict[str, ttk.Button] = {}
        self.group_checkbuttons: dict[str, ttk.Checkbutton] = {}
        self.group_description_labels: dict[str, tuple[PatchGroup, ttk.Label]] = {}
        self.patch_vars: list[tuple[PatchDefinition, tk.BooleanVar]] = []
        self.patch_var_map: dict[str, tk.BooleanVar] = {}
        self.patch_group_map: dict[str, str | None] = {}
        self.patch_requires: dict[str, str | None] = {}
        self.patch_selects: dict[str, list[str]] = {}
        self.patch_dependents: dict[str, list[str]] = {}
        self.patch_buttons: dict[str, ttk.Checkbutton] = {}
        self.patch_detail_labels: dict[str, tuple[PatchDefinition, ttk.Label]] = {}
        self.patch_active_ids: set[str] = set()

        self.target_path_var = tk.StringVar(value=self.settings.get("last_target_path", ""))
        self.target_path_var.trace_add("write", self.on_target_path_changed)
        self.status_var = tk.StringVar(value=self.tr("ready"))
        self.progress_var = tk.DoubleVar(value=0.0)
        self.lang_var = tk.StringVar(value="English")
        self.widgets: dict[str, object] = {}

        self.root.title(WINDOW_TITLE)
        self.root.geometry("980x700")
        self.root.minsize(900, 580)
        self.window_icon = None
        self.configure_window_icon()

        self.build_ui()
        self.root.after(150, self.process_queue)
        self.root.after(250, self.start_initial_search)
        self.root.after(300, self.refresh_patch_statuses)

    def read_json(self, path: Path, default: dict) -> dict:
        if not path.exists():
            return default
        try:
            return json.loads(path.read_text(encoding="utf-8-sig"))
        except json.JSONDecodeError:
            return default

    def write_json(self, path: Path, payload: dict) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")

    def tr(self, key: str, **kwargs: object) -> str:
        language_map = self.translations.get(self.lang) or self.translations.get(DEFAULT_LANGUAGE, {})
        template = language_map.get(key)
        if template is None:
            template = key
        return str(template).format(**kwargs)

    def configure_window_icon(self) -> None:
        try:
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("Ebonhold.HDPatcher")
        except Exception:
            pass

        if ICON_ICO_PATH.exists():
            try:
                self.root.iconbitmap(default=str(ICON_ICO_PATH))
            except tk.TclError:
                pass

        icon_png_path = APP_ICON_PATH if APP_ICON_PATH.exists() else ICON_PATH
        if not icon_png_path.exists():
            return
        try:
            self.window_icon = tk.PhotoImage(file=str(icon_png_path))
            self.root.iconphoto(True, self.window_icon)
        except tk.TclError:
            self.window_icon = None

    def load_config(self) -> tuple[list[PatchGroup], list[PatchDefinition]]:
        if not CONFIG_PATH.exists():
            raise FileNotFoundError(self.tr("cfg_missing", name=CONFIG_PATH.name))
        raw = json.loads(CONFIG_PATH.read_text(encoding="utf-8-sig"))
        update_config = raw.get("app_update", {})
        self.current_version = str(update_config.get("current_version", APP_VERSION)).strip() or APP_VERSION
        self.update_repo = str(update_config.get("github_repo", "")).strip()
        self.update_asset_name = str(update_config.get("asset_name", "")).strip()
        groups: list[PatchGroup] = []
        standalone: list[PatchDefinition] = []
        for entry in raw.get("patches", []):
            if "items" in entry:
                items = [self.parse_patch(item) for item in entry.get("items", [])]
                if not items:
                    raise ValueError(self.tr("cfg_group_empty", name=self.config_label(entry)))
                groups.append(PatchGroup(entry["id"], self.parse_localized_text(entry.get("name", entry["id"])), self.parse_localized_text(entry.get("description", "")), items))
            else:
                standalone.append(self.parse_patch(entry))
        if not groups and not standalone:
            raise ValueError(self.tr("cfg_patches"))
        return groups, standalone

    def parse_patch(self, patch: dict) -> PatchDefinition:
        patch_type = str(patch.get("patch_type", "archive")).strip().lower() or "archive"
        target_executable = self.normalize_relative_path(patch.get("target_executable", ""))
        sources = [PatchSource(src.get("label", f"Mirror {index + 1}"), src["url"]) for index, src in enumerate(patch.get("sources", []))]
        if patch_type in {"large_address_aware", "laa"}:
            if not target_executable:
                raise ValueError(self.tr("cfg_exe", name=self.config_label(patch)))
        elif not sources:
            raise ValueError(self.tr("cfg_src", name=self.config_label(patch)))
        return PatchDefinition(
            id=patch["id"],
            name=self.parse_localized_text(patch.get("name", patch["id"])),
            description=self.parse_localized_text(patch.get("description", "")),
            patch_type=patch_type,
            target_subdirectories=self.normalize_target_subdirectories(patch),
            expected_files=self.normalize_expected_files(patch),
            requires=patch.get("requires"),
            selects=self.normalize_patch_links(patch.get("selects")),
            target_executable=target_executable,
            sources=sources,
        )

    def config_label(self, payload: dict) -> str:
        return self.localize_text(self.parse_localized_text(payload.get("name", payload.get("id", "?"))), fallback=payload.get("id", "?"))

    def parse_localized_text(self, value: object) -> dict[str, str]:
        if isinstance(value, dict):
            parsed = {str(key): str(text) for key, text in value.items() if str(text).strip()}
            if parsed:
                return parsed
        text = str(value).strip()
        return {DEFAULT_LANGUAGE: text} if text else {}

    def localize_text(self, values: dict[str, str], fallback: str = "") -> str:
        return values.get(self.lang) or values.get(DEFAULT_LANGUAGE) or next(iter(values.values()), fallback)

    def normalize_relative_path(self, value: object) -> str:
        return str(value).replace("/", "\\").strip("\\ ").strip()

    def normalize_target_subdirectories(self, patch: dict) -> list[str]:
        values = patch.get("target_subdirectories")
        if values is None:
            values = [patch.get("target_subdirectory", patch.get("subdirectory", ""))]
        cleaned = []
        for value in values:
            text = self.normalize_relative_path(value)
            if text:
                cleaned.append(text)
        return cleaned or [""]

    def normalize_expected_files(self, patch: dict) -> list[str]:
        values = patch.get("expected_files", [])
        cleaned = []
        for value in values:
            text = self.normalize_relative_path(value)
            if text:
                cleaned.append(text)
        return cleaned

    def normalize_patch_links(self, value: object) -> list[str]:
        if value is None:
            return []
        values = value if isinstance(value, list) else [value]
        cleaned = []
        for entry in values:
            text = str(entry).strip()
            if text:
                cleaned.append(text)
        return cleaned

    def build_ui(self) -> None:
        frame = ttk.Frame(self.root, padding=18)
        frame.pack(fill="both", expand=True)
        frame.columnconfigure(0, weight=1)
        frame.rowconfigure(2, weight=1)

        header = ttk.Frame(frame)
        header.grid(row=0, column=0, sticky="ew")
        header.columnconfigure(0, weight=1)
        ttk.Label(header, text=WINDOW_TITLE, font=("Segoe UI", 18, "bold")).grid(row=0, column=0, sticky="w")
        self.widgets["version_label"] = ttk.Label(header, foreground="#6a6a6a")
        self.widgets["version_label"].grid(row=1, column=0, sticky="w", pady=(2, 0))
        self.widgets["update_btn"] = ttk.Button(header, command=self.start_update_check)
        self.widgets["update_btn"].grid(row=0, column=1, sticky="e", padx=(0, 12))
        self.widgets["info_btn"] = ttk.Button(header, command=self.open_info_window, width=8)
        self.widgets["info_btn"].grid(row=0, column=2, sticky="e", padx=(0, 12))
        self.widgets["lang_label"] = ttk.Label(header, text=self.tr("lang"))
        self.widgets["lang_label"].grid(row=0, column=3, sticky="e", padx=(0, 8))
        combo = ttk.Combobox(header, state="readonly", values=[label for label, _ in LANGUAGES], textvariable=self.lang_var, width=12)
        combo.grid(row=0, column=4, sticky="e")
        combo.bind("<<ComboboxSelected>>", self.on_language_changed)

        path_box = ttk.LabelFrame(frame, text=self.tr("target"))
        path_box.grid(row=1, column=0, sticky="ew", pady=(16, 12))
        path_box.columnconfigure(0, weight=1)
        self.widgets["path_box"] = path_box
        ttk.Entry(path_box, textvariable=self.target_path_var).grid(row=0, column=0, sticky="ew", padx=(12, 8), pady=12)
        self.widgets["choose_btn"] = ttk.Button(path_box, text=self.tr("choose"), command=self.choose_target_path)
        self.widgets["choose_btn"].grid(row=0, column=1, padx=4, pady=12)
        self.widgets["search_btn"] = ttk.Button(path_box, text=self.tr("search"), command=self.start_manual_search)
        self.widgets["search_btn"].grid(row=0, column=2, padx=(4, 12), pady=12)
        self.widgets["note"] = ttk.Label(path_box, text=self.tr("note"), foreground="#555555")
        self.widgets["note"].grid(row=1, column=0, columnspan=3, sticky="w", padx=12, pady=(0, 12))

        patch_box = ttk.LabelFrame(frame, text=self.tr("patches"))
        patch_box.grid(row=2, column=0, sticky="nsew", pady=(0, 12))
        patch_box.columnconfigure(0, weight=1)
        patch_box.rowconfigure(1, weight=1)
        self.widgets["patch_box"] = patch_box
        self.widgets["patch_hint"] = ttk.Label(patch_box, text=self.tr("patch_hint"), foreground="#555555", wraplength=860, justify="left")
        self.widgets["patch_hint"].grid(row=0, column=0, sticky="w", padx=12, pady=(10, 6))
        canvas = tk.Canvas(patch_box, highlightthickness=0)
        scrollbar = ttk.Scrollbar(patch_box, orient="vertical", command=canvas.yview)
        scrollbar.grid(row=1, column=1, sticky="ns")
        inner = ttk.Frame(canvas, padding=12)
        inner.bind("<Configure>", lambda _e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=inner, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.grid(row=1, column=0, sticky="nsew")

        for index, group in enumerate(self.groups):
            self.build_group_section(inner, group)
            if index < len(self.groups) - 1 or self.standalone_patches:
                ttk.Separator(inner, orient="horizontal").pack(fill="x", pady=8)
        if self.standalone_patches:
            for patch in self.standalone_patches:
                self.build_patch_row(inner, patch, indent=0)

        controls = ttk.Frame(frame)
        controls.grid(row=3, column=0, sticky="ew")
        controls.columnconfigure(0, weight=1)
        self.widgets["extractor"] = ttk.Label(controls, foreground="#555555")
        self.widgets["extractor"].grid(row=0, column=0, sticky="w")
        actions = ttk.Frame(controls)
        actions.grid(row=0, column=1, sticky="e")
        self.widgets["apply_btn"] = ttk.Button(actions, command=self.start_patch_install)
        self.widgets["apply_btn"].pack(side="left", padx=(0, 8))
        self.widgets["uninstall_btn"] = ttk.Button(actions, command=self.start_uninstall_selected)
        self.widgets["uninstall_btn"].pack(side="left")

        ttk.Progressbar(frame, variable=self.progress_var, maximum=100).grid(row=4, column=0, sticky="ew", pady=(12, 4))
        ttk.Label(frame, textvariable=self.status_var).grid(row=5, column=0, sticky="w")
        self.refresh_language()
    def build_group_section(self, parent: ttk.Frame, group: PatchGroup) -> None:
        wrapper = ttk.Frame(parent, padding=(0, 6, 0, 10))
        wrapper.pack(fill="x", expand=True)
        self.group_vars[group.id] = tk.BooleanVar(value=False)
        self.group_children[group.id] = []
        self.group_expanded[group.id] = tk.BooleanVar(value=True)

        header = ttk.Frame(wrapper)
        header.pack(fill="x", expand=True)
        header.columnconfigure(1, weight=1)
        gutter = ttk.Frame(header, width=GROUP_TOGGLE_GUTTER)
        gutter.grid(row=0, column=0, sticky="w")
        gutter.grid_propagate(False)
        toggle = ttk.Button(gutter, text=self.group_toggle_text(group.id), width=2, command=lambda gid=group.id: self.toggle_group_visibility(gid))
        toggle.grid(row=0, column=0, sticky="w")
        self.group_toggle_buttons[group.id] = toggle
        group_check = ttk.Checkbutton(header, text=self.group_name(group), variable=self.group_vars[group.id], command=lambda gid=group.id: self.on_group_toggled(gid))
        group_check.grid(row=0, column=1, sticky="w")
        self.group_checkbuttons[group.id] = group_check

        if group.description:
            description_label = ttk.Label(wrapper, text=self.group_description(group), foreground="#555555", wraplength=820, justify="left")
            description_label.pack(anchor="w", padx=(GROUP_TOGGLE_GUTTER, 0), pady=(2, 6))
            self.group_description_labels[group.id] = (group, description_label)

        items_frame = ttk.Frame(wrapper)
        items_frame.pack(fill="x", expand=True)
        self.group_item_frames[group.id] = items_frame
        for patch in group.items:
            self.build_patch_row(items_frame, patch, indent=self.patch_indent(patch), group_id=group.id)

    def build_patch_row(self, parent: ttk.Frame, patch: PatchDefinition, indent: int, group_id: str | None = None) -> None:
        var = tk.BooleanVar(value=False)
        self.patch_vars.append((patch, var))
        self.patch_var_map[patch.id] = var
        self.patch_group_map[patch.id] = group_id
        self.patch_requires[patch.id] = patch.requires
        self.patch_selects[patch.id] = patch.selects
        if patch.requires:
            self.patch_dependents.setdefault(patch.requires, []).append(patch.id)
        if group_id:
            self.group_children[group_id].append((patch, var))

        row = ttk.Frame(parent, padding=(0, 4))
        row.pack(fill="x", expand=True)

        if patch.requires:
            branch = tk.Frame(row, width=2, bg="#b7c0c8")
            branch.pack(side="left", fill="y", padx=(indent, 10))
        else:
            spacer = ttk.Frame(row, width=indent)
            spacer.pack(side="left")

        content = ttk.Frame(row)
        content.pack(side="left", fill="x", expand=True)

        button = ttk.Checkbutton(content, variable=var, text=self.patch_button_label(patch), command=lambda pid=patch.id: self.on_patch_toggled(pid))
        button.pack(anchor="w")
        self.patch_buttons[patch.id] = button
        label = ttk.Label(content, foreground="#555555", wraplength=760, justify="left")
        label.pack(anchor="w", padx=(24, 0), pady=(2, 0))
        self.patch_detail_labels[patch.id] = (patch, label)

    def on_group_toggled(self, group_id: str) -> None:
        if self.updating_group_state:
            return
        value = self.group_vars[group_id].get()
        self.updating_group_state = True
        for _, child_var in self.group_children[group_id]:
            child_var.set(value)
        self.updating_group_state = False

    def on_patch_toggled(self, patch_id: str) -> None:
        if self.updating_group_state:
            return
        var = self.patch_var_map[patch_id]
        if var.get():
            self.select_required_chain(patch_id)
            self.select_selected_chain(patch_id)
        else:
            self.deselect_dependents(patch_id)

        group_id = self.patch_group_map.get(patch_id)
        if not group_id:
            return
        self.updating_group_state = True
        self.group_vars[group_id].set(all(var.get() for _, var in self.group_children[group_id]))
        self.updating_group_state = False

    def select_required_chain(self, patch_id: str) -> None:
        self.updating_group_state = True
        current = patch_id
        while current:
            self.patch_var_map[current].set(True)
            group_id = self.patch_group_map.get(current)
            if group_id:
                self.group_vars[group_id].set(all(var.get() for _, var in self.group_children[group_id]))
            current = self.patch_requires.get(current)
        self.updating_group_state = False

    def select_selected_chain(self, patch_id: str) -> None:
        self.updating_group_state = True
        pending = list(self.patch_selects.get(patch_id, []))
        seen: set[str] = set()
        while pending:
            selected_id = pending.pop()
            if selected_id in seen or selected_id not in self.patch_var_map:
                continue
            seen.add(selected_id)
            self.patch_var_map[selected_id].set(True)
            current = self.patch_requires.get(selected_id)
            while current:
                if current in self.patch_var_map:
                    self.patch_var_map[current].set(True)
                    group_id = self.patch_group_map.get(current)
                    if group_id:
                        self.group_vars[group_id].set(all(var.get() for _, var in self.group_children[group_id]))
                current = self.patch_requires.get(current)
            group_id = self.patch_group_map.get(selected_id)
            if group_id:
                self.group_vars[group_id].set(all(var.get() for _, var in self.group_children[group_id]))
            pending.extend(self.patch_selects.get(selected_id, []))
        for group_id in self.group_children:
            self.group_vars[group_id].set(all(var.get() for _, var in self.group_children[group_id]))
        self.updating_group_state = False

    def deselect_dependents(self, patch_id: str) -> None:
        self.updating_group_state = True
        pending = list(self.patch_dependents.get(patch_id, []))
        while pending:
            dependent_id = pending.pop()
            self.patch_var_map[dependent_id].set(False)
            pending.extend(self.patch_dependents.get(dependent_id, []))
            group_id = self.patch_group_map.get(dependent_id)
            if group_id:
                self.group_vars[group_id].set(all(var.get() for _, var in self.group_children[group_id]))
        group_id = self.patch_group_map.get(patch_id)
        if group_id:
            self.group_vars[group_id].set(all(var.get() for _, var in self.group_children[group_id]))
        self.updating_group_state = False

    def group_toggle_text(self, group_id: str) -> str:
        return "-" if self.group_expanded[group_id].get() else "+"

    def patch_indent(self, patch: PatchDefinition) -> int:
        depth = 0
        current = patch.requires
        while current:
            depth += 1
            current = self.patch_requires.get(current)
        return PATCH_BASE_INDENT + (depth * PATCH_CHILD_INDENT)

    def patch_name(self, patch: PatchDefinition) -> str:
        return self.localize_text(patch.name, fallback=patch.id)

    def patch_description(self, patch: PatchDefinition) -> str:
        return self.localize_text(patch.description, fallback="")

    def group_name(self, group: PatchGroup) -> str:
        return self.localize_text(group.name, fallback=group.id)

    def group_description(self, group: PatchGroup) -> str:
        return self.localize_text(group.description, fallback="")

    def patch_button_label(self, patch: PatchDefinition) -> str:
        patch_name = self.patch_name(patch)
        return f"+ {patch_name}" if patch.requires else patch_name

    def toggle_group_visibility(self, group_id: str) -> None:
        expanded = not self.group_expanded[group_id].get()
        self.group_expanded[group_id].set(expanded)
        frame = self.group_item_frames[group_id]
        if expanded:
            frame.pack(fill="x", expand=True)
        else:
            frame.pack_forget()
        self.group_toggle_buttons[group_id].configure(text=self.group_toggle_text(group_id))

    def on_language_changed(self, _event: object) -> None:
        mapping = {label: code for label, code in LANGUAGES}
        self.lang = mapping.get(self.lang_var.get(), DEFAULT_LANGUAGE)
        self.refresh_language()
        self.refresh_patch_statuses()

    def refresh_language(self) -> None:
        if not self.is_busy:
            self.status_var.set(self.tr("ready"))
        self.widgets["version_label"].configure(text=self.tr("version_label", version=self.current_version))
        self.widgets["update_btn"].configure(text=self.tr("check_updates"))
        self.widgets["info_btn"].configure(text=self.tr("info_button"))
        self.widgets["lang_label"].configure(text=self.tr("lang"))
        self.widgets["path_box"].configure(text=self.tr("target"))
        self.widgets["choose_btn"].configure(text=self.tr("choose"))
        self.widgets["search_btn"].configure(text=self.tr("search"))
        self.widgets["note"].configure(text=self.tr("note"))
        self.widgets["patch_box"].configure(text=self.tr("patches"))
        self.widgets["patch_hint"].configure(text=self.tr("patch_hint"))
        self.widgets["apply_btn"].configure(text=self.tr("apply"))
        self.widgets["uninstall_btn"].configure(text=self.tr("uninstall"))
        extractor_state = self.tr("zip_builtin")
        if self.install_tool_path:
            extractor_state = self.tr("extractor_with_external", name=Path(self.install_tool_path).name)
        self.widgets["extractor"].configure(text=extractor_state)
        for group_id, checkbutton in self.group_checkbuttons.items():
            group = next((candidate for candidate in self.groups if candidate.id == group_id), None)
            if group:
                checkbutton.configure(text=self.group_name(group))
        for group_id, (group, label) in self.group_description_labels.items():
            description = self.group_description(group)
            if description:
                label.configure(text=description)
        self.refresh_patch_statuses()

    def open_info_window(self) -> None:
        window = tk.Toplevel(self.root)
        window.title(self.tr("info_title"))
        window.transient(self.root)
        window.resizable(False, False)
        try:
            if self.window_icon is not None:
                window.iconphoto(True, self.window_icon)
            elif ICON_ICO_PATH.exists():
                window.iconbitmap(default=str(ICON_ICO_PATH))
        except tk.TclError:
            pass

        frame = ttk.Frame(window, padding=12)
        frame.pack(fill="both", expand=True)

        ttk.Label(frame, text=self.tr("info_title"), font=("Segoe UI", 11, "bold")).pack(anchor="w")
        ttk.Label(frame, text=self.tr("info_version", version=self.current_version), foreground="#6a6a6a").pack(anchor="w", pady=(1, 1))
        ttk.Label(frame, text=self.tr("info_author"), foreground="#6a6a6a").pack(anchor="w", pady=(0, 8))
        ttk.Label(frame, text=self.tr("info_sources"), wraplength=320, justify="left").pack(anchor="w")
        ttk.Label(frame, text=self.tr("info_bugs"), wraplength=320, justify="left").pack(anchor="w", pady=(8, 4))
        ttk.Button(frame, text=self.tr("info_open_issues"), command=lambda: webbrowser.open(BUG_REPORTS_URL)).pack(anchor="w")
        ttk.Button(frame, text=self.tr("close"), command=window.destroy).pack(anchor="e", pady=(10, 0))

    def on_target_path_changed(self, *_args) -> None:
        if self.status_refresh_job:
            self.root.after_cancel(self.status_refresh_job)
        self.status_refresh_job = self.root.after(150, self.refresh_patch_statuses)

    def refresh_patch_statuses(self) -> None:
        self.status_refresh_job = None
        target_root = self.current_target_root()
        self.patch_active_ids = set()
        for patch, _ in self.patch_vars:
            active = bool(target_root and self.is_patch_active_for_target(patch.id, target_root))
            if active:
                self.patch_active_ids.add(patch.id)
            self.patch_buttons[patch.id].configure(text=self.patch_display_name(patch, active))
            self.patch_detail_labels[patch.id][1].configure(text=self.patch_detail_text(patch, active))

    def patch_display_name(self, patch: PatchDefinition, active: bool) -> str:
        base_name = self.patch_button_label(patch)
        return f"{base_name} \u2713" if active else base_name

    def patch_detail_text(self, patch: PatchDefinition, active: bool) -> str:
        return self.patch_description(patch) or self.tr("nodesc")

    def choose_target_path(self) -> None:
        path = filedialog.askdirectory(title=self.tr("choose_title"))
        if path:
            self.set_target_path(path)

    def set_target_path(self, path: str) -> None:
        self.target_path_var.set(path)
        self.settings["last_target_path"] = path
        self.write_json(SETTINGS_PATH, self.settings)

    def current_target_root(self) -> Path | None:
        raw = self.target_path_var.get().strip()
        if not raw:
            return None
        path = Path(raw)
        return path if path.exists() else None

    def start_initial_search(self) -> None:
        saved = self.target_path_var.get().strip()
        if saved and Path(saved).exists():
            return
        self.start_search(show_dialogs=False)

    def start_manual_search(self) -> None:
        self.start_search(show_dialogs=True)

    def start_search(self, show_dialogs: bool) -> None:
        if self.is_busy:
            return
        self.is_busy = True
        self.progress_var.set(0)
        self.status_var.set(self.tr("searching"))
        threading.Thread(target=self.search_target_path_worker, args=(show_dialogs,), daemon=True).start()

    def start_update_check(self) -> None:
        if self.is_busy:
            return
        if not self.update_repo:
            messagebox.showwarning(self.tr("updates_t"), self.tr("updates_not_configured"))
            return
        self.is_busy = True
        self.progress_var.set(0)
        self.status_var.set(self.tr("updates_checking"))
        threading.Thread(target=self.check_for_updates_worker, daemon=True).start()

    def start_patch_install(self) -> None:
        if self.is_busy:
            return
        target_root = self.current_target_root()
        if not target_root:
            messagebox.showwarning(self.tr("no_target_t"), self.tr("no_target"))
            return
        selected = [patch for patch, var in self.patch_vars if var.get()]
        if not selected:
            messagebox.showwarning(self.tr("no_sel_t"), self.tr("no_sel"))
            return
        install_candidates = [patch for patch in selected if patch.id not in self.patch_active_ids]
        if install_candidates:
            mandatory_laa = [
                patch for patch, _ in self.patch_vars
                if patch.patch_type in {"large_address_aware", "laa"} and patch.id not in self.patch_active_ids
            ]
            seen_ids = {patch.id for patch in install_candidates}
            for patch in mandatory_laa:
                if patch.id not in seen_ids:
                    install_candidates.append(patch)
                    seen_ids.add(patch.id)
        if not install_candidates:
            messagebox.showinfo(self.tr("already_installed_t"), self.tr("already_installed_m"))
            return
        self.is_busy = True
        self.progress_var.set(0)
        self.status_var.set(self.tr("installing"))
        threading.Thread(target=self.patch_install_worker, args=(install_candidates, target_root), daemon=True).start()

    def start_uninstall_selected(self) -> None:
        if self.is_busy:
            return
        target_root = self.current_target_root()
        if not target_root:
            messagebox.showwarning(self.tr("no_target_t"), self.tr("no_target"))
            return
        selected = [patch for patch, var in self.patch_vars if var.get() and patch.id in self.patch_active_ids]
        if not selected:
            messagebox.showwarning(self.tr("no_active_sel_t"), self.tr("no_active_sel"))
            return
        self.is_busy = True
        self.progress_var.set(0)
        self.status_var.set(self.tr("uninstalling"))
        threading.Thread(target=self.uninstall_patches_worker, args=(selected, target_root), daemon=True).start()
    def search_target_path_worker(self, show_dialogs: bool) -> None:
        matches = []
        for root in self.get_search_roots():
            if matches:
                break
            self.queue.put(("status", self.tr("search_in", root=root)))
            matches.extend(self.scan_for_target(root))
        self.queue.put(("search_finished", {"matches": matches, "show_dialogs": show_dialogs}))

    def patch_install_worker(self, selected: list[PatchDefinition], target_root: Path) -> None:
        try:
            with TemporaryDirectory(prefix="eh-patcher-") as temp_dir:
                temp_root = Path(temp_dir)
                total = len(selected)
                for index, patch in enumerate(selected, start=1):
                    patch_start = ((index - 1) / total) * 100
                    patch_end = (index / total) * 100
                    patch_label = self.patch_name(patch)
                    self.queue.put(("progress", patch_start))
                    if patch.patch_type in {"large_address_aware", "laa"}:
                        self.queue.put(("status", self.tr("apply_status", i=index, n=total, name=patch_label)))
                        record = self.apply_large_address_aware_patch(patch, target_root)
                        self.queue.put(("progress", patch_end))
                    else:
                        self.queue.put(("status", self.tr("check", i=index, n=total, name=patch_label)))
                        self.set_patch_stage_progress(patch_start, patch_end, 0.08)
                        source = self.pick_working_source(patch)
                        if source is None:
                            raise RuntimeError(self.tr("no_source", name=patch_label))

                        archive_name = self.filename_from_url(source.url, patch.id)
                        archive_path = self.cached_download_path(source.url, archive_name)
                        stage_dir = temp_root / f"{patch.id}-stage"
                        stage_dir.mkdir(parents=True, exist_ok=True)
                        used_cached_archive = archive_path.exists() and archive_path.is_file()
                        if used_cached_archive:
                            self.queue.put(("status", self.tr("using_cached_patch", i=index, n=total, name=patch_label)))
                            self.set_patch_stage_progress(patch_start, patch_end, 0.78)
                        else:
                            self.queue.put(("status", self.tr("download", i=index, n=total, name=patch_label)))
                            self.download_file(
                                source.url,
                                archive_path,
                                progress_callback=lambda fraction, ps=patch_start, pe=patch_end: self.set_patch_stage_progress(ps, pe, 0.08 + (fraction * 0.70)),
                                status_callback=lambda downloaded, total_size, i=index, n=total, name=patch_label: self.queue.put((
                                    "status",
                                    f"{self.tr('download', i=i, n=n, name=name)} ({self.format_size(downloaded)} / {self.format_size(total_size)})",
                                )) if total_size else None,
                            )
                        self.queue.put(("status", self.tr("extract_archive", i=index, n=total, name=patch_label)))
                        self.set_patch_stage_progress(patch_start, patch_end, 0.82)
                        try:
                            self.extract_archive_to_directory(archive_path, stage_dir)
                        except Exception:
                            if not used_cached_archive:
                                raise
                            if stage_dir.exists():
                                shutil.rmtree(stage_dir, ignore_errors=True)
                            stage_dir.mkdir(parents=True, exist_ok=True)
                            try:
                                archive_path.unlink()
                            except OSError:
                                pass
                            self.queue.put(("status", self.tr("download", i=index, n=total, name=patch_label)))
                            self.download_file(
                                source.url,
                                archive_path,
                                progress_callback=lambda fraction, ps=patch_start, pe=patch_end: self.set_patch_stage_progress(ps, pe, 0.08 + (fraction * 0.70)),
                                status_callback=lambda downloaded, total_size, i=index, n=total, name=patch_label: self.queue.put((
                                    "status",
                                    f"{self.tr('download', i=i, n=n, name=name)} ({self.format_size(downloaded)} / {self.format_size(total_size)})",
                                )) if total_size else None,
                            )
                            self.queue.put(("status", self.tr("extract_archive", i=index, n=total, name=patch_label)))
                            self.extract_archive_to_directory(archive_path, stage_dir)
                        self.queue.put(("status", self.tr("apply_status", i=index, n=total, name=patch_label)))
                        self.set_patch_stage_progress(patch_start, patch_end, 0.92)
                        record = self.apply_staged_patch(patch, stage_dir, target_root)
                        self.queue.put(("progress", patch_end))
                    self.upsert_install_record(record)

                self.queue.put(("progress", 100))
                self.queue.put(("done", self.tr("done")))
        except Exception as exc:
            self.queue.put(("error", str(exc)))

    def check_for_updates_worker(self) -> None:
        try:
            release = self.fetch_latest_release()
            self.queue.put(("update_check_result", release))
        except Exception as exc:
            self.queue.put(("update_error", str(exc)))

    def download_update_worker(self, release: dict) -> None:
        try:
            asset = self.pick_update_asset(release)
            if not asset:
                self.queue.put(("update_no_asset", release))
                return
            download_url = asset["browser_download_url"]
            update_dir = Path(os.environ.get("TEMP", str(BASE_DIR))) / "eh-patcher-updates"
            update_dir.mkdir(parents=True, exist_ok=True)
            destination = update_dir / asset["name"]
            self.download_file(
                download_url,
                destination,
                progress_callback=lambda fraction: self.queue.put(("progress", fraction * 100)),
                status_callback=lambda downloaded, total_size: self.queue.put((
                    "status",
                    f"{self.tr('updates_downloading')} ({self.format_size(downloaded)} / {self.format_size(total_size)})",
                )) if total_size else None,
            )
            self.queue.put(("update_ready", {"release": release, "path": str(destination)}))
        except Exception as exc:
            self.queue.put(("update_error", str(exc)))

    def uninstall_patches_worker(self, selected: list[PatchDefinition], target_root: Path) -> None:
        try:
            total = len(selected)
            for index, patch in enumerate(selected, start=1):
                self.queue.put(("progress", ((index - 1) / total) * 100))
                self.queue.put(("status", self.tr("uninstall_status", i=index, n=total, name=self.patch_name(patch))))
                self.uninstall_patch_record(patch.id, target_root)
            self.queue.put(("progress", 100))
            self.queue.put(("done", self.tr("uninstall_done")))
        except Exception as exc:
            self.queue.put(("error", str(exc)))

    def process_queue(self) -> None:
        try:
            while True:
                kind, payload = self.queue.get_nowait()
                if kind == "status":
                    self.status_var.set(payload)
                elif kind == "progress":
                    self.progress_var.set(payload)
                elif kind == "search_finished":
                    self.is_busy = False
                    matches = payload["matches"]
                    show_dialogs = payload["show_dialogs"]
                    if not matches:
                        self.status_var.set(self.tr("none"))
                        if show_dialogs:
                            messagebox.showinfo(self.tr("none_t"), self.tr("none_m"))
                    elif len(matches) == 1:
                        self.set_target_path(str(matches[0]))
                        self.status_var.set(self.tr("found", path=matches[0]))
                    else:
                        self.set_target_path(str(matches[0]))
                        self.status_var.set(self.tr("multi", path=matches[0]))
                        if show_dialogs:
                            messagebox.showinfo(self.tr("multi_t"), self.tr("multi_m", matches="\n".join(str(x) for x in matches[:10])))
                elif kind == "done":
                    self.is_busy = False
                    self.status_var.set(payload)
                    self.refresh_patch_statuses()
                    messagebox.showinfo(self.tr("done_t"), payload)
                elif kind == "update_check_result":
                    release = payload
                    latest_version = self.normalize_version_text(release.get("tag_name", ""))
                    if not self.is_newer_version(latest_version, self.current_version):
                        self.is_busy = False
                        self.progress_var.set(0)
                        self.status_var.set(self.tr("ready"))
                        messagebox.showinfo(self.tr("updates_t"), self.tr("updates_current", version=self.current_version))
                    else:
                        message = self.tr("updates_available", current=self.current_version, latest=latest_version)
                        if messagebox.askyesno(self.tr("updates_t"), message):
                            self.progress_var.set(0)
                            self.status_var.set(self.tr("updates_downloading"))
                            threading.Thread(target=self.download_update_worker, args=(release,), daemon=True).start()
                        else:
                            self.is_busy = False
                            self.progress_var.set(0)
                            self.status_var.set(self.tr("ready"))
                elif kind == "update_no_asset":
                    self.is_busy = False
                    self.progress_var.set(0)
                    self.status_var.set(self.tr("ready"))
                    release = payload
                    messagebox.showerror(
                        self.tr("updates_t"),
                        self.tr("updates_asset_missing", asset=self.update_asset_name or Path(sys.executable).name, release=release.get("tag_name", "?")),
                    )
                elif kind == "update_ready":
                    download_path = Path(payload["path"])
                    if self.apply_downloaded_update(download_path):
                        return
                    self.is_busy = False
                    self.progress_var.set(0)
                    self.status_var.set(self.tr("ready"))
                    messagebox.showerror(self.tr("updates_t"), self.tr("updates_auto_only"))
                elif kind == "update_error":
                    self.is_busy = False
                    self.progress_var.set(0)
                    self.status_var.set(self.tr("ready"))
                    messagebox.showerror(self.tr("updates_t"), payload)
                elif kind == "error":
                    self.is_busy = False
                    self.status_var.set(self.tr("err"))
                    self.refresh_patch_statuses()
                    messagebox.showerror(self.tr("err_t"), payload)
        except Empty:
            pass
        self.root.after(150, self.process_queue)

    def get_search_roots(self) -> list[Path]:
        return self.list_available_drives()

    def list_available_drives(self) -> list[Path]:
        return [Path(f"{letter}:\\") for letter in "ABCDEFGHIJKLMNOPQRSTUVWXYZ" if Path(f"{letter}:\\").exists()]

    def scan_for_target(self, root: Path) -> list[Path]:
        matches = []
        visited = 0
        for current_root, dirnames, _ in os.walk(root, topdown=True):
            dirnames[:] = [name for name in dirnames if not self.should_skip_directory(name)]
            current_path = Path(current_root)
            visited += 1
            if visited == 1 or visited % SEARCH_STATUS_INTERVAL == 0:
                self.queue.put(("status", self.tr("search_at", root=root, current=current_path)))
            if current_path.name.lower() == DEFAULT_SEARCH_TARGET_NAME:
                matches.append(current_path)
                if len(matches) >= 5:
                    break
        return matches

    def should_skip_directory(self, directory_name: str) -> bool:
        return directory_name.lower() in {"$recycle.bin", "system volume information", "windows", "appdata", "programdata", "temp", "tmp", ".git", "__pycache__"}

    def pick_working_source(self, patch: PatchDefinition) -> PatchSource | None:
        for source in patch.sources:
            self.queue.put(("status", self.tr("check_source", name=self.patch_name(patch))))
            try:
                resolved_url = self.resolve_download_url(source.url)
            except Exception:
                continue
            if self.check_url_available(resolved_url):
                return PatchSource(source.label, resolved_url)
        return None

    def resolve_download_url(self, url: str) -> str:
        parsed = urlparse(url)
        hostname = (parsed.hostname or "").lower()
        if hostname.endswith("mediafire.com") and "/file/" in parsed.path:
            return self.resolve_mediafire_download_url(url)
        return url

    def resolve_mediafire_download_url(self, url: str) -> str:
        with urlopen(Request(url, headers={"User-Agent": "eh-patcher/1.0"}), timeout=DOWNLOAD_TIMEOUT_SECONDS) as response:
            content_type = response.headers.get("Content-Type", "")
            if "text/html" not in content_type.lower():
                return response.geturl() or url
            html = response.read().decode("utf-8", errors="replace")

        patterns = [
            r'href="(https://download[^"]+)"',
            r'id="downloadButton"[^>]*href="([^"]+)"',
            r'aria-label="Download file"[^>]*href="([^"]+)"',
        ]
        for pattern in patterns:
            match = re.search(pattern, html, flags=re.IGNORECASE)
            if match:
                return unescape(match.group(1))
        raise RuntimeError(f"Could not resolve MediaFire download link from {url}")

    def check_url_available(self, url: str) -> bool:
        try:
            with urlopen(Request(url, method="HEAD", headers={"User-Agent": "eh-patcher/1.0"}), timeout=DOWNLOAD_TIMEOUT_SECONDS) as response:
                return 200 <= response.status < 400
        except HTTPError as exc:
            if exc.code in {403, 405} and self.check_url_available_with_range(url):
                return True
            if exc.code in {403, 405}:
                return self.check_url_available_with_get(url)
            return False
        except URLError:
            return False

    def check_url_available_with_range(self, url: str) -> bool:
        try:
            with urlopen(Request(url, headers={"Range": "bytes=0-0", "User-Agent": "eh-patcher/1.0"}), timeout=DOWNLOAD_TIMEOUT_SECONDS) as response:
                return 200 <= response.status < 400
        except Exception:
            return False

    def check_url_available_with_get(self, url: str) -> bool:
        try:
            with urlopen(Request(url, headers={"User-Agent": "eh-patcher/1.0"}), timeout=DOWNLOAD_TIMEOUT_SECONDS) as response:
                return 200 <= response.status < 400
        except Exception:
            return False

    def set_patch_stage_progress(self, patch_start: float, patch_end: float, stage_fraction: float) -> None:
        bounded_fraction = max(0.0, min(1.0, stage_fraction))
        self.queue.put(("progress", patch_start + ((patch_end - patch_start) * bounded_fraction)))

    def format_size(self, size_bytes: int) -> str:
        value = float(size_bytes)
        units = ["B", "KB", "MB", "GB", "TB"]
        for unit in units:
            if value < 1024 or unit == units[-1]:
                if unit == "B":
                    return f"{int(value)} {unit}"
                return f"{value:.1f} {unit}"
            value /= 1024
        return f"{size_bytes} B"

    def cached_download_path(self, url: str, filename: str) -> Path:
        digest = hashlib.sha256(url.encode("utf-8")).hexdigest()[:16]
        PATCH_DOWNLOAD_CACHE_DIR.mkdir(parents=True, exist_ok=True)
        return PATCH_DOWNLOAD_CACHE_DIR / f"{digest}-{filename}"

    def normalize_version_text(self, value: str) -> str:
        normalized = value.strip()
        if normalized.lower().startswith("v"):
            normalized = normalized[1:]
        return normalized

    def version_key(self, value: str) -> tuple:
        normalized = self.normalize_version_text(value)
        parts: list[object] = []
        for piece in normalized.replace("-", ".").split("."):
            if piece.isdigit():
                parts.append(int(piece))
            elif piece:
                parts.append(piece.lower())
        return tuple(parts)

    def is_newer_version(self, candidate: str, current: str) -> bool:
        return self.version_key(candidate) > self.version_key(current)

    def fetch_latest_release(self) -> dict:
        api_url = f"https://api.github.com/repos/{self.update_repo}/releases/latest"
        with urlopen(Request(api_url, headers={"User-Agent": "eh-patcher/1.0"}), timeout=GITHUB_API_TIMEOUT_SECONDS) as response:
            return json.loads(response.read().decode("utf-8"))

    def pick_update_asset(self, release: dict) -> dict | None:
        assets = release.get("assets", [])
        if not assets:
            return None
        if self.update_asset_name:
            return next((asset for asset in assets if asset.get("name", "").lower() == self.update_asset_name.lower()), None)
        current_name = Path(sys.executable).name.lower()
        if getattr(sys, "frozen", False):
            exact = next((asset for asset in assets if asset.get("name", "").lower() == current_name), None)
            if exact:
                return exact
        return next((asset for asset in assets if asset.get("name", "").lower().endswith(".exe")), None)

    def apply_downloaded_update(self, download_path: Path) -> bool:
        if not getattr(sys, "frozen", False):
            return False
        current_executable = Path(sys.executable)
        script_path = download_path.with_suffix(".cmd")
        script_lines = [
            "@echo off",
            "setlocal",
            f'set "NEW_FILE={download_path}"',
            f'set "TARGET_FILE={current_executable}"',
            ":retry",
            'copy /Y "%NEW_FILE%" "%TARGET_FILE%" >nul',
            "if errorlevel 1 (",
            "  timeout /t 2 /nobreak >nul",
            "  goto retry",
            ")",
            'del "%NEW_FILE%" >nul 2>&1',
            'start "" "%TARGET_FILE%"',
            'del "%~f0" >nul 2>&1',
        ]
        script_path.write_text("\r\n".join(script_lines) + "\r\n", encoding="utf-8")
        creationflags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
        subprocess.Popen(["cmd", "/c", str(script_path)], creationflags=creationflags)
        self.root.destroy()
        os._exit(0)

    def download_file(self, url: str, destination: Path, progress_callback=None, status_callback=None) -> None:
        with urlopen(Request(url, headers={"User-Agent": "eh-patcher/1.0"}), timeout=DOWNLOAD_TIMEOUT_SECONDS) as response:
            total = response.headers.get("Content-Length")
            total_size = int(total) if total and total.isdigit() else None
            downloaded = 0
            with destination.open("wb") as out:
                while True:
                    chunk = response.read(DOWNLOAD_CHUNK_SIZE)
                    if not chunk:
                        break
                    out.write(chunk)
                    downloaded += len(chunk)
                    if total_size and progress_callback:
                        progress_callback(downloaded / total_size)
                    if total_size and status_callback:
                        status_callback(downloaded, total_size)
            if progress_callback:
                progress_callback(1.0)

    def extract_archive_to_directory(self, archive_path: Path, destination: Path) -> None:
        suffix = archive_path.suffix.lower()
        if suffix == ".zip":
            with zipfile.ZipFile(archive_path, "r") as archive:
                archive.extractall(destination)
            return
        if suffix == ".rar":
            if not self.install_tool_path:
                raise RuntimeError(self.tr("rar_requires_tool"))
            result = subprocess.run(self.build_extractor_command(archive_path, destination), check=False, capture_output=True, text=True)
            if result.returncode != 0:
                details = result.stderr.strip() or result.stdout.strip() or self.tr("unknown")
                raise RuntimeError(self.tr("extract_fail", details=details))
            return
        self.stage_single_file(archive_path, destination)

    def stage_single_file(self, source_file: Path, destination: Path) -> None:
        destination.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source_file, destination / source_file.name)
        return

    def apply_large_address_aware_patch(self, patch: PatchDefinition, target_root: Path) -> dict:
        if not patch.target_executable:
            raise RuntimeError(self.tr("cfg_exe", name=self.patch_name(patch)))
        executable_path = target_root / Path(patch.target_executable)
        if not executable_path.exists():
            raise RuntimeError(self.tr("exe_missing", name=self.patch_name(patch), path=patch.target_executable))
        if not executable_path.is_file():
            raise RuntimeError(self.tr("exe_invalid", path=patch.target_executable))

        old_record = self.find_install_record(patch.id, target_root)
        old_backups = {entry["relative_path"]: entry.get("backup_path") for entry in old_record.get("files", [])} if old_record else {}
        install_id = self.make_install_id(patch.id)
        backup_root = PATCH_BACKUPS_DIR / install_id
        relative_to_root = str(executable_path.relative_to(target_root)).replace("/", "\\")
        backup_path = old_backups.get(relative_to_root)
        if not backup_path:
            backup_file = backup_root / relative_to_root
            backup_file.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(executable_path, backup_file)
            backup_path = str(backup_file.relative_to(PATCH_DATA_DIR)).replace("/", "\\")

        self.set_large_address_aware(executable_path)
        return {
            "patch_id": patch.id,
            "target_root": str(target_root),
            "install_id": install_id,
            "patch_type": "large_address_aware",
            "files": [{
                "relative_path": relative_to_root,
                "backup_path": backup_path,
                "sha256": self.hash_file(executable_path),
            }],
        }

    def apply_staged_patch(self, patch: PatchDefinition, stage_dir: Path, target_root: Path) -> dict:
        old_record = self.find_install_record(patch.id, target_root)
        old_backups = {entry["relative_path"]: entry.get("backup_path") for entry in old_record.get("files", [])} if old_record else {}
        install_id = self.make_install_id(patch.id)
        backup_root = PATCH_BACKUPS_DIR / install_id
        staged_files = [path for path in stage_dir.rglob("*") if path.is_file()]
        if not staged_files:
            raise RuntimeError(self.tr("empty_archive", name=self.patch_name(patch)))

        records = []
        for target_subdirectory in patch.target_subdirectories:
            target_base = target_root / target_subdirectory if target_subdirectory else target_root
            for source_file in staged_files:
                relative_inside = source_file.relative_to(stage_dir)
                destination = target_base / relative_inside
                destination.parent.mkdir(parents=True, exist_ok=True)
                relative_to_root = str(destination.relative_to(target_root)).replace("/", "\\")
                backup_path = old_backups.get(relative_to_root)
                if destination.exists() and not backup_path:
                    backup_file = backup_root / relative_to_root
                    backup_file.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(destination, backup_file)
                    backup_path = str(backup_file.relative_to(PATCH_DATA_DIR)).replace("/", "\\")
                shutil.copy2(source_file, destination)
                records.append({"relative_path": relative_to_root, "backup_path": backup_path, "sha256": self.hash_file(destination)})

        return {"patch_id": patch.id, "target_root": str(target_root), "install_id": install_id, "patch_type": patch.patch_type, "files": self.deduplicate_records(records)}
    def uninstall_patch_record(self, patch_id: str, target_root: Path) -> None:
        record = self.find_install_record(patch_id, target_root)
        if not record:
            return
        touched_dirs: set[Path] = set()
        for entry in reversed(record.get("files", [])):
            current_file = target_root / Path(entry["relative_path"])
            touched_dirs.add(current_file.parent)
            backup_rel = entry.get("backup_path")
            backup_abs = PATCH_DATA_DIR / Path(backup_rel) if backup_rel else None
            if backup_abs and backup_abs.exists():
                current_file.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(backup_abs, current_file)
                continue
            if current_file.exists() and self.hash_file(current_file) == entry.get("sha256"):
                current_file.unlink()
        for directory in sorted(touched_dirs, key=lambda item: len(item.parts), reverse=True):
            self.prune_empty_directories(directory, target_root)
        self.remove_install_record(patch_id, target_root)
        self.write_json(PATCH_STATE_PATH, self.patch_state)

    def prune_empty_directories(self, directory: Path, stop_at: Path) -> None:
        current = directory
        while current != stop_at and current.exists():
            try:
                current.rmdir()
            except OSError:
                break
            current = current.parent

    def hash_file(self, path: Path) -> str:
        hasher = hashlib.sha256()
        with path.open("rb") as handle:
            while chunk := handle.read(1024 * 1024):
                hasher.update(chunk)
        return hasher.hexdigest()

    def deduplicate_records(self, records: list[dict]) -> list[dict]:
        unique: dict[str, dict] = {}
        for record in records:
            unique[record["relative_path"]] = record
        return list(unique.values())

    def is_large_address_aware(self, path: Path) -> bool:
        with path.open("rb") as handle:
            if handle.read(2) != b"MZ":
                raise RuntimeError(self.tr("exe_not_pe", path=path.name))
            handle.seek(0x3C)
            pe_offset = int.from_bytes(handle.read(4), "little")
            handle.seek(pe_offset)
            if handle.read(4) != b"PE\x00\x00":
                raise RuntimeError(self.tr("exe_not_pe", path=path.name))
            handle.seek(pe_offset + 4 + 18)
            characteristics = int.from_bytes(handle.read(2), "little")
            return bool(characteristics & IMAGE_FILE_LARGE_ADDRESS_AWARE)

    def set_large_address_aware(self, path: Path) -> None:
        with path.open("r+b") as handle:
            if handle.read(2) != b"MZ":
                raise RuntimeError(self.tr("exe_not_pe", path=path.name))
            handle.seek(0x3C)
            pe_offset = int.from_bytes(handle.read(4), "little")
            handle.seek(pe_offset)
            if handle.read(4) != b"PE\x00\x00":
                raise RuntimeError(self.tr("exe_not_pe", path=path.name))
            characteristics_offset = pe_offset + 4 + 18
            handle.seek(characteristics_offset)
            characteristics = int.from_bytes(handle.read(2), "little")
            if characteristics & IMAGE_FILE_LARGE_ADDRESS_AWARE:
                return
            handle.seek(characteristics_offset)
            handle.write((characteristics | IMAGE_FILE_LARGE_ADDRESS_AWARE).to_bytes(2, "little"))

    def make_install_id(self, patch_id: str) -> str:
        return f"{patch_id}-{len(self.patch_state.get('installs', [])) + 1}"

    def normalize_target_root(self, target_root: Path | str) -> str:
        return str(Path(target_root)).lower()

    def find_install_record(self, patch_id: str, target_root: Path) -> dict | None:
        normalized = self.normalize_target_root(target_root)
        for record in self.patch_state.get("installs", []):
            if record.get("patch_id") == patch_id and self.normalize_target_root(record.get("target_root", "")) == normalized:
                return record
        return None

    def remove_install_record(self, patch_id: str, target_root: Path) -> None:
        normalized = self.normalize_target_root(target_root)
        self.patch_state["installs"] = [
            record for record in self.patch_state.get("installs", [])
            if not (record.get("patch_id") == patch_id and self.normalize_target_root(record.get("target_root", "")) == normalized)
        ]

    def upsert_install_record(self, record: dict) -> None:
        self.remove_install_record(record["patch_id"], Path(record["target_root"]))
        self.patch_state.setdefault("installs", []).append(record)
        self.write_json(PATCH_STATE_PATH, self.patch_state)

    def is_patch_active_for_target(self, patch_id: str, target_root: Path) -> bool:
        patch = next((candidate for candidate, _ in self.patch_vars if candidate.id == patch_id), None)
        if patch and patch.patch_type in {"large_address_aware", "laa"} and patch.target_executable:
            executable_path = target_root / Path(patch.target_executable)
            if not executable_path.exists() or not executable_path.is_file():
                return False
            try:
                return self.is_large_address_aware(executable_path)
            except RuntimeError:
                return False
        if patch and patch.expected_files:
            return all((target_root / Path(relative_path)).exists() for relative_path in patch.expected_files)
        record = self.find_install_record(patch_id, target_root)
        if not record:
            return False
        return all((target_root / Path(entry["relative_path"])).exists() for entry in record.get("files", []))

    def build_extractor_command(self, archive_path: Path, destination: Path) -> list[str]:
        tool_name = Path(self.install_tool_path).name.lower()
        if tool_name == "7z.exe":
            return [self.install_tool_path, "x", str(archive_path), f"-o{destination}", "-y"]
        if tool_name == "winrar.exe":
            return [self.install_tool_path, "x", "-ibck", "-o+", str(archive_path), str(destination)]
        return [self.install_tool_path, "x", "-o+", str(archive_path), str(destination)]

    def find_extractor(self) -> str | None:
        tool_roots = [APP_DIR / "tools"]
        if RESOURCE_DIR != APP_DIR:
            tool_roots.append(RESOURCE_DIR / "tools")
        for tool_root in tool_roots:
            for candidate in (tool_root / "7z.exe", tool_root / "WinRAR.exe", tool_root / "unrar.exe", tool_root / "UnRAR.exe"):
                if candidate.exists():
                    return str(candidate)
        for candidate in ("7z.exe", "WinRAR.exe", "unrar.exe"):
            if path := shutil.which(candidate):
                return path
        for candidate in (Path("C:/Program Files/7-Zip/7z.exe"), Path("C:/Program Files/WinRAR/WinRAR.exe"), Path("C:/Program Files (x86)/WinRAR/WinRAR.exe")):
            if candidate.exists():
                return str(candidate)
        return None

    def filename_from_url(self, url: str, fallback_stem: str) -> str:
        name = Path(urlparse(url).path).name
        return name or f"{fallback_stem}.zip"


def main() -> None:
    root = tk.Tk()
    try:
        app = PatcherApp(root)
    except Exception as exc:
        messagebox.showerror("Startup Error", str(exc))
        root.destroy()
        return
    app.root.mainloop()


if __name__ == "__main__":
    main()
