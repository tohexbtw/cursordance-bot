"""
osu!lazer CursorDance Bot v3.1 - WINDOW DETECTION VERSION
Новая система детекта:
- Мониторинг заголовка окна osu! через Win32 API
- Определение начала карты по изменению заголовка
- Минимум ложных запусков благодаря точному анализу
- Поддержка как osu!stable, так и osu!lazer
- Горячие клавиши: Insert (старт), End (стоп), Home (пауза)

Улучшенное движение курсора:
- Физическая система движения (acceleration + friction) как в Auto mode
- Плавные переходы между объектами без рывков
- Естественный танец курсора с уменьшающейся интенсивностью при приближении
- Работает только когда окно osu! активно (требует pywin32)
- Адаптивная скорость в зависимости от расстояния
"""

import time
import math
import threading
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from pynput.mouse import Controller as MouseController
from pynput.keyboard import Key, Listener as KeyboardListener, Controller as KeyboardController
import re
import os
import zipfile
import tempfile
import shutil
import psutil
from dataclasses import dataclass
from typing import List, Tuple, Optional, Dict
import sys
import ctypes
from collections import deque

# Константы osu!
OSU_WIDTH = 512
OSU_HEIGHT = 384
SCREEN_WIDTH = 1920
SCREEN_HEIGHT = 1080
SCALE_X = SCREEN_WIDTH / OSU_WIDTH
SCALE_Y = SCREEN_HEIGHT / OSU_HEIGHT

# Константы тайминга
HIT_WINDOW_50 = 150.0
HIT_WINDOW_100 = 100.0
HIT_WINDOW_300 = 50.0
PERFECT_WINDOW = 30.0

# Windows API для SendInput (работает в osu!lazer)
PUL = ctypes.POINTER(ctypes.c_ulong)

class KeyBdInput(ctypes.Structure):
    _fields_ = [("wVk", ctypes.c_ushort),
                ("wScan", ctypes.c_ushort),
                ("dwFlags", ctypes.c_ulong),
                ("time", ctypes.c_ulong),
                ("dwExtraInfo", PUL)]

class HardwareInput(ctypes.Structure):
    _fields_ = [("uMsg", ctypes.c_ulong),
                ("wParamL", ctypes.c_short),
                ("wParamH", ctypes.c_ushort)]

class MouseInput(ctypes.Structure):
    _fields_ = [("dx", ctypes.c_long),
                ("dy", ctypes.c_long),
                ("mouseData", ctypes.c_ulong),
                ("dwFlags", ctypes.c_ulong),
                ("time", ctypes.c_ulong),
                ("dwExtraInfo", PUL)]

class Input_I(ctypes.Union):
    _fields_ = [("ki", KeyBdInput),
                ("mi", MouseInput),
                ("hi", HardwareInput)]

class Input(ctypes.Structure):
    _fields_ = [("type", ctypes.c_ulong),
                ("ii", Input_I)]

def is_admin():
    """Проверка прав администратора"""
    try:
        return ctypes.windll.shell32.IsUserAnAdmin() != 0
    except:
        return False

def run_as_admin():
    """Перезапуск с правами администратора"""
    try:
        if sys.argv[0].endswith('.py'):
            params = ' '.join([sys.argv[0]] + sys.argv[1:])
            ctypes.windll.shell32.ShellExecuteW(
                None, "runas", sys.executable, params, None, 1
            )
        else:
            params = ' '.join(sys.argv[1:])
            ctypes.windll.shell32.ShellExecuteW(
                None, "runas", sys.executable, params, None, 1
            )
        return True
    except:
        return False

@dataclass
class TimingPoint:
    """Точка тайминга"""
    time: float
    beat_length: float
    meter: int
    sample_set: int
    sample_index: int
    volume: int
    uninherited: bool
    effects: int

@dataclass
class HitObject:
    """Объект карты"""
    x: int
    y: int
    time: float
    type: int
    hit_sound: int
    extras: str = ""
    slider_type: Optional[str] = None
    slider_points: List[Tuple[int, int]] = None
    repeat: int = 1
    pixel_length: float = 0.0
    end_time: Optional[float] = None

class OsuBeatmapParser:
    """Парсер .osu файлов"""
    
    def __init__(self, file_path: str):
        self.file_path = file_path
        self.hit_objects: List[HitObject] = []
        self.timing_points: List[TimingPoint] = []
        self.difficulty = {}
        self.general = {}
        self.metadata = {}
        
    def parse(self) -> bool:
        """Парсинг .osu файла"""
        try:
            for encoding in ['utf-8', 'utf-8-sig', 'cp1251', 'latin1']:
                try:
                    with open(self.file_path, 'r', encoding=encoding) as f:
                        content = f.read()
                    break
                except UnicodeDecodeError:
                    continue
            else:
                return False
            
            self._parse_general(content)
            self._parse_metadata(content)
            self._parse_difficulty(content)
            self._parse_timing_points(content)
            self._parse_hit_objects(content)
            
            self.hit_objects.sort(key=lambda obj: obj.time)
            return True
        except Exception as e:
            print(f"Ошибка парсинга: {e}")
            return False
    
    def _parse_general(self, content: str):
        section = self._get_section(content, "General")
        if section:
            self.general = self._parse_key_value(section)
    
    def _parse_metadata(self, content: str):
        section = self._get_section(content, "Metadata")
        if section:
            self.metadata = self._parse_key_value(section)
    
    def _parse_difficulty(self, content: str):
        section = self._get_section(content, "Difficulty")
        if section:
            self.difficulty = self._parse_key_value(section)
    
    def _parse_timing_points(self, content: str):
        section = self._get_section(content, "TimingPoints")
        if not section:
            return
        
        for line in section.strip().split('\n'):
            line = line.strip()
            if not line or line.startswith('//'):
                continue
            
            parts = line.split(',')
            if len(parts) < 2:
                continue
            
            try:
                self.timing_points.append(TimingPoint(
                    time=float(parts[0]),
                    beat_length=float(parts[1]),
                    meter=int(parts[2]) if len(parts) > 2 else 4,
                    sample_set=int(parts[3]) if len(parts) > 3 else 0,
                    sample_index=int(parts[4]) if len(parts) > 4 else 0,
                    volume=int(parts[5]) if len(parts) > 5 else 50,
                    uninherited=int(parts[6]) == 1 if len(parts) > 6 else True,
                    effects=int(parts[7]) if len(parts) > 7 else 0
                ))
            except:
                continue
    
    def _parse_hit_objects(self, content: str):
        section = self._get_section(content, "HitObjects")
        if not section:
            return
        
        for line in section.strip().split('\n'):
            line = line.strip()
            if not line or line.startswith('//'):
                continue
            
            parts = line.split(',')
            if len(parts) < 4:
                continue
            
            try:
                x = int(parts[0])
                y = int(parts[1])
                time = float(parts[2])
                obj_type = int(parts[3])
                hit_sound = int(parts[4]) if len(parts) > 4 else 0
                
                if obj_type & 1:
                    self.hit_objects.append(HitObject(
                        x=x, y=y, time=time, type=1, hit_sound=hit_sound
                    ))
                
                elif obj_type & 2:
                    if len(parts) > 5:
                        slider_data = parts[5]
                        slider_parts = slider_data.split('|')
                        slider_type = slider_parts[0] if slider_parts else 'L'
                        slider_points = []
                        
                        for i in range(1, len(slider_parts)):
                            point_str = slider_parts[i]
                            if ':' in point_str:
                                px, py = map(int, point_str.split(':'))
                                slider_points.append((px, py))
                        
                        repeat = int(parts[6]) if len(parts) > 6 else 1
                        pixel_length = float(parts[7]) if len(parts) > 7 else 0.0
                        
                        active_timing = None
                        for tp in self.timing_points:
                            if tp.time <= time and tp.uninherited:
                                active_timing = tp
                        
                        slider_multiplier = float(self.difficulty.get('SliderMultiplier', 1.4))
                        if active_timing and active_timing.beat_length > 0:
                            duration = (pixel_length / (100.0 * slider_multiplier)) * active_timing.beat_length * repeat
                            end_time = time + duration
                        else:
                            end_time = time + (pixel_length / 100.0) * 600.0
                        
                        self.hit_objects.append(HitObject(
                            x=x, y=y, time=time, type=2, hit_sound=hit_sound,
                            slider_type=slider_type, slider_points=slider_points,
                            repeat=repeat, pixel_length=pixel_length, end_time=end_time
                        ))
                
                elif obj_type & 8:
                    end_time = float(parts[5]) if len(parts) > 5 else time + 1000
                    self.hit_objects.append(HitObject(
                        x=256, y=192, time=time, type=8, hit_sound=hit_sound, end_time=end_time
                    ))
                        
            except Exception as e:
                print(f"Ошибка парсинга объекта: {e}")
                continue
    
    def _get_section(self, content: str, section_name: str) -> Optional[str]:
        pattern = rf'\[{section_name}\](.*?)(?=\[|\Z)'
        match = re.search(pattern, content, re.DOTALL)
        return match.group(1).strip() if match else None
    
    def _parse_key_value(self, content: str) -> dict:
        result = {}
        for line in content.split('\n'):
            line = line.strip()
            if ':' in line and not line.startswith('//'):
                key, value = line.split(':', 1)
                result[key.strip()] = value.strip()
        return result

class WindowsInputHelper:
    """Помощник для Windows SendInput API"""
    
    VK_Z = 0x5A
    VK_X = 0x58
    
    KEYEVENTF_KEYDOWN = 0x0000
    KEYEVENTF_KEYUP = 0x0002
    INPUT_KEYBOARD = 1
    
    @staticmethod
    def press_key(vk_code):
        """Нажатие клавиши через SendInput"""
        extra = ctypes.c_ulong(0)
        ii_ = Input_I()
        ii_.ki = KeyBdInput(vk_code, 0, WindowsInputHelper.KEYEVENTF_KEYDOWN, 0, ctypes.pointer(extra))
        x = Input(ctypes.c_ulong(WindowsInputHelper.INPUT_KEYBOARD), ii_)
        ctypes.windll.user32.SendInput(1, ctypes.pointer(x), ctypes.sizeof(x))
    
    @staticmethod
    def release_key(vk_code):
        """Отпускание клавиши через SendInput"""
        extra = ctypes.c_ulong(0)
        ii_ = Input_I()
        ii_.ki = KeyBdInput(vk_code, 0, WindowsInputHelper.KEYEVENTF_KEYUP, 0, ctypes.pointer(extra))
        x = Input(ctypes.c_ulong(WindowsInputHelper.INPUT_KEYBOARD), ii_)
        ctypes.windll.user32.SendInput(1, ctypes.pointer(x), ctypes.sizeof(x))

class OsuWindowMonitor:
    """Мониторинг окна osu! через Win32 API"""
    
    def __init__(self, callback):
        self.callback = callback
        self.running = False
        self.thread = None
        self.last_title = ""
        self.last_state = "menu"  # menu, selecting, playing
        self.stable_counter = 0  # Счетчик для устранения ложных срабатываний
        self.required_stable_frames = 3  # Требуемое количество стабильных кадров
        
        # Проверка pywin32
        try:
            import win32gui
            import win32process
            self.has_win32 = True
        except ImportError:
            print("⚠ ОШИБКА: pywin32 не установлен!")
            print("Установите: pip install pywin32 --break-system-packages")
            self.has_win32 = False
    
    def start(self):
        """Запуск мониторинга"""
        if not self.has_win32:
            print("❌ Невозможно запустить мониторинг без pywin32")
            return False
        
        if self.running:
            return True
        
        self.running = True
        self.thread = threading.Thread(target=self._monitor_loop, daemon=True)
        self.thread.start()
        print("✓ Мониторинг окна osu! запущен")
        return True
    
    def stop(self):
        """Остановка мониторинга"""
        self.running = False
        print("✓ Мониторинг окна остановлен")
    
    def _monitor_loop(self):
        """Главный цикл мониторинга"""
        import win32gui
        import win32process
        
        while self.running:
            try:
                # Ищем окно osu!
                osu_hwnd = self._find_osu_window()
                
                if osu_hwnd:
                    # Получаем заголовок окна
                    title = win32gui.GetWindowText(osu_hwnd)
                    
                    if title != self.last_title:
                        # Анализируем изменение состояния
                        new_state = self._analyze_window_title(title)
                        
                        # Проверяем переход в режим игры
                        if new_state == "playing" and self.last_state != "playing":
                            self.stable_counter += 1
                            
                            # Требуем стабильное состояние перед запуском
                            if self.stable_counter >= self.required_stable_frames:
                                beatmap_info = self._extract_beatmap_info(title)
                                print(f"🎵 Обнаружено начало карты: {beatmap_info}")
                                self.callback(beatmap_info)
                                self.stable_counter = 0
                        else:
                            # Сброс счетчика при любом другом изменении
                            if new_state != "playing":
                                self.stable_counter = 0
                        
                        self.last_state = new_state
                        self.last_title = title
                
                time.sleep(0.1)  # Проверяем каждые 100мс
                
            except Exception as e:
                print(f"Ошибка мониторинга окна: {e}")
                time.sleep(1.0)
    
    def _find_osu_window(self):
        """Поиск окна osu!"""
        import win32gui
        
        osu_windows = []
        
        def callback(hwnd, windows):
            if win32gui.IsWindowVisible(hwnd):
                title = win32gui.GetWindowText(hwnd).lower()
                if 'osu!' in title:
                    windows.append(hwnd)
            return True
        
        win32gui.EnumWindows(callback, osu_windows)
        
        return osu_windows[0] if osu_windows else None
    
    def _analyze_window_title(self, title: str) -> str:
        """
        Анализ заголовка окна для определения состояния
        
        Примеры заголовков:
        - osu! - главное меню или выбор
        - osu! - Artist - Title [Difficulty] - игра началась
        - osu! - Edit - Artist - Title [Difficulty] - редактор
        """
        title_lower = title.lower()
        
        # Проверяем признаки редактора (игнорируем)
        if 'edit' in title_lower or 'editor' in title_lower:
            return "editing"
        
        # Проверяем признаки выбора карты
        if title == "osu!" or "song select" in title_lower:
            return "selecting"
        
        # Проверяем признаки игры
        # В osu! во время игры в заголовке появляется: Artist - Title [Difficulty]
        if '[' in title and ']' in title:
            # Дополнительная проверка: должно быть " - " (разделитель артист-название)
            if ' - ' in title:
                # Исключаем случаи с меню
                if 'menu' not in title_lower and 'select' not in title_lower:
                    return "playing"
        
        return "menu"
    
    def _extract_beatmap_info(self, title: str) -> str:
        """Извлечение информации о beatmap из заголовка"""
        # Убираем "osu! - " в начале
        if title.startswith("osu! - "):
            beatmap_name = title[7:]
            return beatmap_name
        return title

class RelaxBot:
    """Улучшенный Relax бот с Discord RPC детектом"""
    
    def __init__(self):
        self.mouse = MouseController()
        self.keyboard = KeyboardController()
        self.running = False
        self.paused = False
        self.thread = None
        
        self.beatmap: Optional[OsuBeatmapParser] = None
        self.hit_objects: List[HitObject] = []
        self.start_time = 0.0
        self.temp_dir: Optional[str] = None
        
        self.offset_ms = 0.0
        self.smooth_factor = 0.4
        self.dance_intensity = 0.5
        self.dance_style = "flow"
        self.accuracy_mode = "perfect"
        
        self.clicked_objects = set()
        self.current_key = 'z'
        self.current_vk = WindowsInputHelper.VK_Z
        self.key_pressed = False
        self.active_slider = None
        self.spinner_rpm = 477.0
        
        self.position_cache = deque(maxlen=10)
        self.last_update = 0.0
        self.target_fps = 120
        
        self.waiting_mode = False
        self.window_monitor = None
        self.osu_window = None
        
        # Улучшенная система движения курсора (как Auto mod)
        self.current_position = [SCREEN_WIDTH // 2, SCREEN_HEIGHT // 2]
        self.target_position = [SCREEN_WIDTH // 2, SCREEN_HEIGHT // 2]
        self.velocity = [0.0, 0.0]
        self.auto_acceleration = 3.5  # Ускорение как в Auto
        self.auto_friction = 0.85  # Трение для плавности
        self.arrival_threshold = 5  # Порог прибытия в пикселях
        
        # Проверка pywin32 для Windows API
        self.has_pywin32 = False
        try:
            import win32gui
            import win32process
            self.has_pywin32 = True
        except ImportError:
            print("⚠ pywin32 не установлен. Используется упрощенный метод детекта.")
            print("Установите: pip install pywin32 --break-system-packages")
        
        self.create_modern_gui()
        
        self.keyboard_listener = KeyboardListener(on_press=self.on_key_press)
        self.keyboard_listener.start()
    
    def create_modern_gui(self):
        """Современный минималистичный GUI с прокруткой"""
        self.root = tk.Tk()
        self.root.title("osu! Relax Bot v3.1 [Window Detection]" + (" [ADMIN]" if is_admin() else ""))
        
        # Определяем высоту экрана для адаптивного размера
        screen_height = self.root.winfo_screenheight()
        max_window_height = int(screen_height * 0.85)  # Максимум 85% высоты экрана
        
        bg_color = "#1e1e1e"
        fg_color = "#ffffff"
        accent_color = "#ff66aa"
        secondary_bg = "#2d2d2d"
        
        self.root.configure(bg=bg_color)
        self.root.resizable(False, False)
        self.root.attributes("-topmost", True)
        
        style = ttk.Style()
        style.theme_use('clam')
        
        # Заголовок (фиксированный)
        header = tk.Frame(self.root, bg=accent_color, height=60)
        header.pack(fill=tk.X)
        header.pack_propagate(False)
        
        title_label = tk.Label(
            header,
            text="🎵 osu! Relax Bot v3.1\n[Window Detection]" + (" [ADMIN]" if is_admin() else ""),
            bg=accent_color,
            fg="#ffffff",
            font=("Segoe UI", 12, "bold"),
            justify=tk.CENTER
        )
        title_label.pack(pady=8)
        
        # Предупреждения (фиксированные)
        warnings_frame = tk.Frame(self.root, bg=bg_color)
        warnings_frame.pack(fill=tk.X)
        
        if not is_admin():
            warn_frame = tk.Frame(warnings_frame, bg="#ff3333")
            warn_frame.pack(fill=tk.X)
            tk.Label(
                warn_frame,
                text="⚠ Требуются права администратора для работы с osu!lazer",
                bg="#ff3333",
                fg="#ffffff",
                font=("Segoe UI", 8),
                wraplength=360
            ).pack(pady=3)
        
        if not self.has_pywin32:
            warn_frame2 = tk.Frame(warnings_frame, bg="#ffaa00")
            warn_frame2.pack(fill=tk.X)
            tk.Label(
                warn_frame2,
                text="⚠ ОБЯЗАТЕЛЬНО установите pywin32: pip install pywin32",
                bg="#ffaa00",
                fg="#000000",
                font=("Segoe UI", 8, "bold"),
                wraplength=360
            ).pack(pady=3)
        
        # Создаем контейнер с прокруткой
        container = tk.Frame(self.root, bg=bg_color)
        container.pack(fill=tk.BOTH, expand=True)
        
        # Canvas для прокрутки
        canvas = tk.Canvas(container, bg=bg_color, highlightthickness=0)
        scrollbar = ttk.Scrollbar(container, orient="vertical", command=canvas.yview)
        
        # Скроллируемый фрейм
        scrollable_frame = tk.Frame(canvas, bg=bg_color)
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas_window = canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        
        # Обновление ширины scrollable_frame при изменении canvas
        def on_canvas_configure(event):
            canvas.itemconfig(canvas_window, width=event.width)
        
        canvas.bind('<Configure>', on_canvas_configure)
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # Прокрутка колесиком мыши
        def on_mousewheel(event):
            canvas.yview_scroll(int(-1*(event.delta/120)), "units")
        
        canvas.bind_all("<MouseWheel>", on_mousewheel)
        
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # Основной контент внутри scrollable_frame
        main_frame = tk.Frame(scrollable_frame, bg=bg_color)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=15, pady=10)
        
        # Статус мониторинга
        monitor_frame = tk.Frame(main_frame, bg="#4a90e2", relief=tk.FLAT, bd=0)
        monitor_frame.pack(fill=tk.X, pady=(0, 10))
        
        tk.Label(
            monitor_frame,
            text="Мониторинг окна:",
            bg="#4a90e2",
            fg="#ffffff",
            font=("Segoe UI", 9, "bold")
        ).pack(anchor=tk.W, padx=10, pady=(5, 0))
        
        self.monitor_status_label = tk.Label(
            monitor_frame,
            text="Не запущен",
            bg="#4a90e2",
            fg="#ffffff",
            font=("Segoe UI", 9),
            wraplength=340,
            justify=tk.LEFT
        )
        self.monitor_status_label.pack(anchor=tk.W, padx=10, pady=(0, 5))
        
        # Статус
        status_frame = tk.Frame(main_frame, bg=secondary_bg, relief=tk.FLAT, bd=0)
        status_frame.pack(fill=tk.X, pady=(0, 10))
        
        tk.Label(
            status_frame,
            text="Статус:",
            bg=secondary_bg,
            fg="#888888",
            font=("Segoe UI", 9)
        ).pack(anchor=tk.W, padx=10, pady=(5, 0))
        
        self.status_label = tk.Label(
            status_frame,
            text="Готов к работе",
            bg=secondary_bg,
            fg="#00ff88",
            font=("Segoe UI", 10, "bold"),
            wraplength=340,
            justify=tk.LEFT
        )
        self.status_label.pack(anchor=tk.W, padx=10, pady=(0, 5))
        
        # Beatmap
        beatmap_frame = tk.Frame(main_frame, bg=secondary_bg)
        beatmap_frame.pack(fill=tk.X, pady=(0, 10))
        
        tk.Label(
            beatmap_frame,
            text="Beatmap:",
            bg=secondary_bg,
            fg="#888888",
            font=("Segoe UI", 9)
        ).pack(anchor=tk.W, padx=10, pady=(5, 0))
        
        self.beatmap_label = tk.Label(
            beatmap_frame,
            text="Не загружен",
            bg=secondary_bg,
            fg="#aaaaaa",
            font=("Segoe UI", 9),
            wraplength=340,
            justify=tk.LEFT
        )
        self.beatmap_label.pack(anchor=tk.W, padx=10, pady=(0, 5))
        
        load_btn = tk.Button(
            main_frame,
            text="📁 Загрузить Beatmap (.osu / .osz)",
            command=self.load_beatmap,
            bg=accent_color,
            fg="#ffffff",
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            cursor="hand2",
            activebackground="#ff88bb"
        )
        load_btn.pack(fill=tk.X, pady=(0, 10))
        
        # Настройки
        settings_frame = tk.LabelFrame(
            main_frame,
            text="⚙ Настройки",
            bg=secondary_bg,
            fg=fg_color,
            font=("Segoe UI", 9, "bold"),
            relief=tk.FLAT
        )
        settings_frame.pack(fill=tk.X, pady=(0, 10))
        
        settings_grid = tk.Frame(settings_frame, bg=secondary_bg)
        settings_grid.pack(padx=10, pady=10)
        
        tk.Label(settings_grid, text="Смещение (мс):", bg=secondary_bg, fg="#aaaaaa", font=("Segoe UI", 9)).grid(row=0, column=0, sticky=tk.W, pady=3)
        self.offset_var = tk.StringVar(value="0")
        offset_entry = tk.Entry(settings_grid, textvariable=self.offset_var, bg="#3a3a3a", fg="#ffffff", width=10, relief=tk.FLAT, font=("Segoe UI", 9))
        offset_entry.grid(row=0, column=1, padx=(10, 0), pady=3)
        
        tk.Label(settings_grid, text="Плавность:", bg=secondary_bg, fg="#aaaaaa", font=("Segoe UI", 9)).grid(row=1, column=0, sticky=tk.W, pady=3)
        self.smooth_var = tk.StringVar(value="0.4")
        smooth_entry = tk.Entry(settings_grid, textvariable=self.smooth_var, bg="#3a3a3a", fg="#ffffff", width=10, relief=tk.FLAT, font=("Segoe UI", 9))
        smooth_entry.grid(row=1, column=1, padx=(10, 0), pady=3)
        
        tk.Label(settings_grid, text="Стиль танца:", bg=secondary_bg, fg="#aaaaaa", font=("Segoe UI", 9)).grid(row=2, column=0, sticky=tk.W, pady=3)
        self.dance_style_var = tk.StringVar(value="flow")
        style_combo = ttk.Combobox(
            settings_grid,
            textvariable=self.dance_style_var,
            values=["flow", "wave", "circular", "sharp"],
            state="readonly",
            width=8,
            font=("Segoe UI", 9)
        )
        style_combo.grid(row=2, column=1, padx=(10, 0), pady=3)
        
        tk.Label(settings_grid, text="Точность:", bg=secondary_bg, fg="#aaaaaa", font=("Segoe UI", 9)).grid(row=3, column=0, sticky=tk.W, pady=3)
        self.accuracy_var = tk.StringVar(value="perfect")
        accuracy_combo = ttk.Combobox(
            settings_grid,
            textvariable=self.accuracy_var,
            values=["perfect", "high", "medium"],
            state="readonly",
            width=8,
            font=("Segoe UI", 9)
        )
        accuracy_combo.grid(row=3, column=1, padx=(10, 0), pady=3)
        
        # Кнопки управления
        control_frame = tk.Frame(main_frame, bg=bg_color)
        control_frame.pack(fill=tk.X, pady=(0, 5))
        
        self.start_btn = tk.Button(
            control_frame,
            text="▶ Автостарт (Окно)",
            command=self.toggle_waiting,
            bg="#00cc66",
            fg="#ffffff",
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            cursor="hand2",
            activebackground="#00dd77"
        )
        self.start_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5))
        
        self.stop_btn = tk.Button(
            control_frame,
            text="⬛ Стоп",
            command=self.stop,
            bg="#cc0000",
            fg="#ffffff",
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT,
            cursor="hand2",
            state=tk.DISABLED,
            activebackground="#dd0000"
        )
        self.stop_btn.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        # Подсказки
        hint_frame = tk.Frame(main_frame, bg=bg_color)
        hint_frame.pack(fill=tk.X, pady=(5, 0))
        
        tk.Label(
            hint_frame,
            text="🔑 Insert: Автостарт | End: Стоп | Home: Пауза",
            bg=bg_color,
            fg="#ffaa00",
            font=("Segoe UI", 9, "bold")
        ).pack()
        
        tk.Label(
            hint_frame,
            text="Мониторинг заголовка окна osu! (требует pywin32)",
            bg=bg_color,
            fg="#4a90e2",
            font=("Segoe UI", 8, "bold")
        ).pack()
        
        # Обновляем geometry после создания всех виджетов
        self.root.update_idletasks()
        
        # Вычисляем необходимую высоту
        required_height = scrollable_frame.winfo_reqheight() + 60 + warnings_frame.winfo_reqheight() + 40
        
        # Ограничиваем высоту окна
        window_height = min(required_height, max_window_height)
        
        # Устанавливаем размер окна
        self.root.geometry(f"380x{window_height}")
        
        # Сохраняем canvas для возможности программной прокрутки
        self.canvas = canvas
    
    def load_beatmap(self):
        """Загрузка beatmap"""
        file_path = filedialog.askopenfilename(
            title="Выберите .osz или .osu файл",
            filetypes=[
                ("osu! files", "*.osz *.osu"),
                ("All files", "*.*")
            ]
        )
        
        if not file_path:
            return
        
        self.cleanup_temp_dir()
        
        try:
            if file_path.lower().endswith('.osz'):
                osu_file = self.extract_osz(file_path)
                if not osu_file:
                    messagebox.showerror("Ошибка", "Не удалось распаковать .osz")
                    return
                file_path = osu_file
            
            self.beatmap = OsuBeatmapParser(file_path)
            if not self.beatmap.parse():
                messagebox.showerror("Ошибка", "Не удалось распарсить beatmap")
                return
            
            self.hit_objects = self.beatmap.hit_objects
            
            title = self.beatmap.metadata.get('Title', 'Unknown')
            artist = self.beatmap.metadata.get('Artist', 'Unknown')
            version = self.beatmap.metadata.get('Version', 'Unknown')
            
            self.beatmap_label.config(
                text=f"{artist} - {title} [{version}]\n{len(self.hit_objects)} объектов",
                fg="#00ff88"
            )
            
            self.status_label.config(
                text=f"Beatmap загружен: {len(self.hit_objects)} объектов",
                fg="#00ff88"
            )
            
        except Exception as e:
            messagebox.showerror("Ошибка", f"Ошибка загрузки: {str(e)}")
            self.cleanup_temp_dir()
    
    def extract_osz(self, path: str) -> Optional[str]:
        """Распаковка .osz"""
        try:
            temp_dir = tempfile.mkdtemp(prefix="osu_relax_")
            self.temp_dir = temp_dir
            
            with zipfile.ZipFile(path, 'r') as zip_ref:
                zip_ref.extractall(temp_dir)
            
            osu_files = [f for f in os.listdir(temp_dir) if f.endswith('.osu')]
            
            if not osu_files:
                return None
            
            if len(osu_files) == 1:
                return os.path.join(temp_dir, osu_files[0])
            
            return self.select_difficulty(temp_dir, osu_files)
            
        except Exception as e:
            print(f"Ошибка распаковки: {e}")
            return None
    
    def select_difficulty(self, temp_dir: str, files: List[str]) -> Optional[str]:
        """Выбор сложности"""
        win = tk.Toplevel(self.root)
        win.title("Выберите сложность")
        win.geometry("400x300")
        win.configure(bg="#1e1e1e")
        win.transient(self.root)
        win.grab_set()
        
        selected = [None]
        
        tk.Label(
            win,
            text="Выберите сложность:",
            bg="#1e1e1e",
            fg="#ffffff",
            font=("Segoe UI", 12, "bold")
        ).pack(pady=10)
        
        listbox = tk.Listbox(
            win,
            bg="#2d2d2d",
            fg="#ffffff",
            font=("Segoe UI", 10),
            selectmode=tk.SINGLE,
            relief=tk.FLAT
        )
        listbox.pack(fill=tk.BOTH, expand=True, padx=20, pady=(0, 10))
        
        for f in files:
            listbox.insert(tk.END, f)
        listbox.select_set(0)
        
        def on_select():
            sel = listbox.curselection()
            if sel:
                selected[0] = os.path.join(temp_dir, files[sel[0]])
            win.destroy()
        
        tk.Button(
            win,
            text="Выбрать",
            command=on_select,
            bg="#00cc66",
            fg="#ffffff",
            font=("Segoe UI", 10, "bold"),
            relief=tk.FLAT
        ).pack(pady=(0, 10))
        
        listbox.bind('<Double-Button-1>', lambda e: on_select())
        
        win.wait_window()
        return selected[0]
    
    def cleanup_temp_dir(self):
        """Очистка временных файлов"""
        if self.temp_dir and os.path.exists(self.temp_dir):
            try:
                shutil.rmtree(self.temp_dir, ignore_errors=True)
            except:
                pass
            self.temp_dir = None
    
    def is_osu_window_active(self) -> bool:
        """Проверка, активно ли окно osu!"""
        if not self.has_pywin32:
            return True  # Если нет pywin32, считаем что окно активно
        
        try:
            import win32gui
            
            # Получаем активное окно
            hwnd = win32gui.GetForegroundWindow()
            if not hwnd:
                return False
            
            # Получаем заголовок окна
            title = win32gui.GetWindowText(hwnd).lower()
            
            # Проверяем, что это osu!
            return 'osu!' in title or 'lazer' in title
            
        except Exception as e:
            print(f"Ошибка проверки окна: {e}")
            return True  # В случае ошибки продолжаем работу
    
    def toggle_waiting(self):
        """Переключение режима ожидания"""
        if self.waiting_mode:
            self.stop()
        else:
            if not self.hit_objects:
                messagebox.showwarning("Предупреждение", "Загрузите beatmap!")
                return
            
            if not self.has_pywin32:
                messagebox.showerror(
                    "Ошибка", 
                    "pywin32 не установлен!\n\n"
                    "Автостарт невозможен без этой библиотеки.\n"
                    "Установите: pip install pywin32 --break-system-packages"
                )
                return
            
            self.waiting_mode = True
            self.start_btn.config(text="⏸ Ожидание...", bg="#4a90e2")
            self.status_label.config(text="Ожидание начала карты...", fg="#4a90e2")
            self.monitor_status_label.config(text="Мониторинг активен - ожидание начала игры", fg="#ffffff")
            
            # Запуск мониторинга окна
            self.window_monitor = OsuWindowMonitor(callback=self.on_beatmap_detected)
            if not self.window_monitor.start():
                self.waiting_mode = False
                self.start_btn.config(text="▶ Автостарт (Окно)", bg="#00cc66")
                self.status_label.config(text="Ошибка запуска мониторинга", fg="#ff3333")
                self.monitor_status_label.config(text="Не запущен", fg="#ffffff")
                messagebox.showerror("Ошибка", "Не удалось запустить мониторинг окна")
    
    def on_beatmap_detected(self, beatmap_name: str):
        """Callback при обнаружении начала карты"""
        if not self.waiting_mode:
            return
        
        print(f"🎵 Начало карты обнаружено: {beatmap_name}")
        self.monitor_status_label.config(text=f"Обнаружена карта: {beatmap_name}", fg="#00ff88")
        
        # Небольшая задержка перед стартом (загрузка карты)
        time.sleep(0.5)
        
        self.waiting_mode = False
        self.start()
    
    def start(self):
        """Старт бота"""
        if self.running:
            return
        
        if not self.hit_objects:
            self.status_label.config(text="Загрузите beatmap!", fg="#ff3333")
            return
        
        try:
            self.offset_ms = float(self.offset_var.get())
            self.smooth_factor = float(self.smooth_var.get())
            self.dance_style = self.dance_style_var.get()
            self.accuracy_mode = self.accuracy_var.get()
        except ValueError:
            messagebox.showerror("Ошибка", "Некорректные значения настроек")
            return
        
        self.running = True
        self.paused = False
        self.waiting_mode = False
        self.clicked_objects.clear()
        self.current_key = 'z'
        self.current_vk = WindowsInputHelper.VK_Z
        self.key_pressed = False
        self.active_slider = None
        self.position_cache.clear()
        
        # Инициализация физики курсора
        current_pos = self.mouse.position
        self.current_position = [float(current_pos[0]), float(current_pos[1])]
        self.target_position = [float(current_pos[0]), float(current_pos[1])]
        self.velocity = [0.0, 0.0]
        
        self.start_time = time.time() * 1000 - (self.offset_ms if self.hit_objects else 0)
        
        self.start_btn.config(text="⏸ Пауза", bg="#ffaa00", state=tk.NORMAL)
        self.stop_btn.config(state=tk.NORMAL)
        self.status_label.config(text="▶ Бот запущен!", fg="#00ff88")
        
        self.thread = threading.Thread(target=self.bot_loop, daemon=True)
        self.thread.start()
        
        print(f"Бот запущен! Объектов: {len(self.hit_objects)}, Offset: {self.offset_ms}ms")
        print(f"Физика курсора: acceleration={self.auto_acceleration}, friction={self.auto_friction}")
    
    def toggle_pause(self):
        """Пауза/Продолжить"""
        if not self.running:
            return
        
        self.paused = not self.paused
        
        if self.paused:
            self.start_btn.config(text="▶ Продолжить", bg="#00cc66")
            self.status_label.config(text="⏸ Пауза", fg="#ffaa00")
            if self.key_pressed:
                WindowsInputHelper.release_key(self.current_vk)
                self.key_pressed = False
        else:
            self.start_btn.config(text="⏸ Пауза", bg="#ffaa00")
            self.status_label.config(text="▶ Бот работает", fg="#00ff88")
    
    def stop(self):
        """Остановка бота"""
        self.running = False
        self.waiting_mode = False
        self.paused = False
        
        if self.key_pressed:
            WindowsInputHelper.release_key(self.current_vk)
            self.key_pressed = False
        
        if self.window_monitor:
            self.window_monitor.stop()
            self.window_monitor = None
        
        self.start_btn.config(text="▶ Автостарт (Окно)", bg="#00cc66", state=tk.NORMAL)
        self.stop_btn.config(state=tk.DISABLED)
        self.status_label.config(text="⬛ Остановлен", fg="#ff3333")
        self.monitor_status_label.config(text="Не запущен", fg="#ffffff")
        
        print("Бот остановлен")
    
    def bot_loop(self):
        """Главный цикл бота"""
        frame_time = 1.0 / self.target_fps
        
        while self.running:
            if self.paused:
                time.sleep(0.05)
                continue
            
            # Проверяем, активно ли окно osu!
            if not self.is_osu_window_active():
                time.sleep(0.1)
                continue
            
            loop_start = time.time()
            current_time = (time.time() * 1000) - self.start_time
            
            # Обработка объектов
            active_objects = []
            for obj in self.hit_objects:
                if obj.time in self.clicked_objects:
                    continue
                
                time_diff = obj.time - current_time
                
                # Собираем активные объекты (в пределах видимости)
                if -200 <= time_diff <= 800:
                    active_objects.append((obj, time_diff))
            
            # Определяем целевую позицию (как в Auto - движемся к ближайшему объекту)
            if active_objects:
                # Сортируем по времени до клика
                active_objects.sort(key=lambda x: abs(x[1]))
                nearest_obj, nearest_diff = active_objects[0]
                
                # Рассчитываем целевую позицию с танцем
                target_x, target_y = self.calculate_target_position(nearest_obj, current_time)
                self.target_position = [target_x, target_y]
            
            # Плавное движение курсора (физика как в Auto)
            self.update_cursor_physics()
            
            # Обработка кликов
            for obj, time_diff in active_objects:
                if obj.type == 1:  # Hit Circle
                    if self.should_click(obj, current_time):
                        self.click_circle(obj)
                        self.clicked_objects.add(obj.time)
                
                elif obj.type == 2:  # Slider
                    if self.should_click(obj, current_time):
                        if not self.active_slider:
                            self.start_slider(obj)
                            self.clicked_objects.add(obj.time)
                    
                    if self.active_slider and self.active_slider.time == obj.time:
                        if current_time >= obj.end_time:
                            self.end_slider()
                        else:
                            slider_pos = self.get_slider_position(obj, current_time)
                            if slider_pos:
                                self.target_position = list(slider_pos)
                
                elif obj.type == 8:  # Spinner
                    if time_diff <= 0 and current_time < obj.end_time:
                        if not self.key_pressed:
                            self.press_key()
                        self.spin_cursor(current_time)
                    elif current_time >= obj.end_time and obj.time not in self.clicked_objects:
                        if self.key_pressed:
                            self.release_key()
                        self.clicked_objects.add(obj.time)
            
            # Ограничение FPS
            elapsed = time.time() - loop_start
            if elapsed < frame_time:
                time.sleep(frame_time - elapsed)
    
    def update_cursor_physics(self):
        """
        Обновление физики курсора (как в Auto mode osu!)
        Использует acceleration и friction для плавного движения
        """
        # Вектор до цели
        dx = self.target_position[0] - self.current_position[0]
        dy = self.target_position[1] - self.current_position[1]
        
        # Расстояние до цели
        distance = math.sqrt(dx*dx + dy*dy)
        
        if distance < self.arrival_threshold:
            # Мы уже на месте
            return
        
        # Нормализованный вектор направления
        if distance > 0:
            dir_x = dx / distance
            dir_y = dy / distance
        else:
            dir_x = 0
            dir_y = 0
        
        # Применяем ускорение (как в Auto)
        acceleration_strength = min(distance / 100.0, 1.0) * self.auto_acceleration
        
        self.velocity[0] += dir_x * acceleration_strength
        self.velocity[1] += dir_y * acceleration_strength
        
        # Применяем трение (для плавности)
        self.velocity[0] *= self.auto_friction
        self.velocity[1] *= self.auto_friction
        
        # Ограничиваем максимальную скорость
        max_speed = 50.0
        speed = math.sqrt(self.velocity[0]**2 + self.velocity[1]**2)
        if speed > max_speed:
            scale = max_speed / speed
            self.velocity[0] *= scale
            self.velocity[1] *= scale
        
        # Обновляем позицию
        self.current_position[0] += self.velocity[0]
        self.current_position[1] += self.velocity[1]
        
        # Плавное торможение при приближении к цели
        if distance < 50:
            decel_factor = distance / 50.0
            self.velocity[0] *= decel_factor
            self.velocity[1] *= decel_factor
        
        # Ограничиваем координаты экрана
        self.current_position[0] = max(0, min(SCREEN_WIDTH, self.current_position[0]))
        self.current_position[1] = max(0, min(SCREEN_HEIGHT, self.current_position[1]))
        
        # Устанавливаем курсор
        self.mouse.position = (int(self.current_position[0]), int(self.current_position[1]))
    
    def calculate_target_position(self, obj: HitObject, current_time: float) -> Tuple[int, int]:
        """Расчет целевой позиции с плавным танцем (как Auto)"""
        base_x = int(obj.x * SCALE_X)
        base_y = int(obj.y * SCALE_Y)
        
        time_until = obj.time - current_time
        
        # Если далеко до объекта - добавляем танец
        if time_until > 150:
            # Плавный танец (менее интенсивный, чем раньше)
            dance_offset = self.calculate_dance_offset(current_time, obj, time_until)
            return (base_x + dance_offset[0], base_y + dance_offset[1])
        elif time_until > 50:
            # Приближаемся - уменьшаем интенсивность танца
            intensity_scale = (time_until - 50) / 100.0  # 0.0 to 1.0
            dance_offset = self.calculate_dance_offset(current_time, obj, time_until)
            return (
                base_x + int(dance_offset[0] * intensity_scale),
                base_y + int(dance_offset[1] * intensity_scale)
            )
        else:
            # Близко к объекту - двигаемся точно к центру
            return (base_x, base_y)
    
    def calculate_dance_offset(self, current_time: float, obj: HitObject, time_until: float) -> Tuple[int, int]:
        """
        Расчет смещения для танца курсора (более плавный, как Auto)
        """
        # Уменьшенная интенсивность для более естественного движения
        base_intensity = 15.0  # Было 30
        intensity = base_intensity * self.dance_intensity
        
        # Плавная волна времени
        t = current_time / 400.0  # Замедленное движение
        
        # Добавляем зависимость от расстояния до клика
        distance_factor = min(time_until / 500.0, 1.0)
        intensity *= distance_factor
        
        if self.dance_style == "flow":
            # Плавные синусоидальные волны (классический Auto)
            offset_x = int(math.sin(t * 1.2) * intensity)
            offset_y = int(math.cos(t * 1.5) * intensity)
        elif self.dance_style == "wave":
            # Волновое движение
            offset_x = int(math.sin(t * 1.5) * intensity)
            offset_y = int(math.sin(t * 1.5 + math.pi/3) * intensity * 0.7)
        elif self.dance_style == "circular":
            # Круговое движение (как в Auto при ожидании)
            radius = intensity * 0.8
            offset_x = int(math.cos(t * 2) * radius)
            offset_y = int(math.sin(t * 2) * radius)
        else:  # sharp
            # Резкие движения (но все еще плавнее старой версии)
            offset_x = int(math.sin(t * 3) * intensity)
            offset_y = int(math.cos(t * 2.5) * intensity)
        
        return (offset_x, offset_y)
    
    def should_click(self, obj: HitObject, current_time: float) -> bool:
        """Определение момента клика"""
        time_diff = obj.time - current_time
        
        if self.accuracy_mode == "perfect":
            return -PERFECT_WINDOW <= time_diff <= PERFECT_WINDOW
        elif self.accuracy_mode == "high":
            return -HIT_WINDOW_300 <= time_diff <= HIT_WINDOW_300
        else:
            return -HIT_WINDOW_100 <= time_diff <= HIT_WINDOW_100
    
    def click_circle(self, obj: HitObject):
        """Клик по кругу"""
        self.press_key()
        threading.Timer(0.05, self.release_key).start()
    
    def start_slider(self, obj: HitObject):
        """Начало слайдера"""
        self.active_slider = obj
        self.press_key()
    
    def end_slider(self):
        """Конец слайдера"""
        self.release_key()
        self.active_slider = None
    
    def get_slider_position(self, obj: HitObject, current_time: float) -> Optional[Tuple[int, int]]:
        """Позиция на слайдере"""
        if not obj.end_time:
            return None
        
        progress = (current_time - obj.time) / (obj.end_time - obj.time)
        progress = max(0.0, min(1.0, progress))
        
        # Упрощенная линейная интерполяция
        if obj.slider_points and len(obj.slider_points) > 0:
            end_point = obj.slider_points[0]
            x = int((obj.x + (end_point[0] - obj.x) * progress) * SCALE_X)
            y = int((obj.y + (end_point[1] - obj.y) * progress) * SCALE_Y)
            return (x, y)
        
        return (int(obj.x * SCALE_X), int(obj.y * SCALE_Y))
    
    def spin_cursor(self, current_time: float):
        """Вращение курсора для спиннера (плавное, как Auto)"""
        center_x, center_y = SCREEN_WIDTH // 2, SCREEN_HEIGHT // 2
        radius = 120  # Немного больше радиус
        
        # Плавное ускорение вращения
        angle = (current_time * self.spinner_rpm / 1000.0) * 2 * math.pi
        
        # Добавляем небольшую вариацию радиуса для естественности
        radius_variation = math.sin(angle * 3) * 5
        actual_radius = radius + radius_variation
        
        target_x = int(center_x + actual_radius * math.cos(angle))
        target_y = int(center_y + actual_radius * math.sin(angle))
        
        # Используем физику для плавного движения
        self.target_position = [target_x, target_y]
        
        # Для спиннера двигаемся быстрее
        self.velocity[0] *= 0.95  # Меньше трение для спиннера
        self.velocity[1] *= 0.95
    
    def press_key(self):
        """Нажатие клавиши"""
        if not self.key_pressed:
            WindowsInputHelper.press_key(self.current_vk)
            self.key_pressed = True
    
    def release_key(self):
        """Отпускание клавиши"""
        if self.key_pressed:
            WindowsInputHelper.release_key(self.current_vk)
            self.key_pressed = False
            self.toggle_key()
    
    def toggle_key(self):
        """Чередование клавиш Z/X"""
        if self.current_key == 'z':
            self.current_key = 'x'
            self.current_vk = WindowsInputHelper.VK_X
        else:
            self.current_key = 'z'
            self.current_vk = WindowsInputHelper.VK_Z
    
    def on_key_press(self, key):
        """Обработка горячих клавиш"""
        try:
            if key == Key.insert:  # Insert - автостарт
                if not self.running and not self.waiting_mode:
                    self.toggle_waiting()
            elif key == Key.end:  # End - стоп
                if self.running or self.waiting_mode:
                    self.stop()
            elif key == Key.home:  # Home - пауза
                if self.running:
                    self.toggle_pause()
        except AttributeError:
            pass
    
    def run(self):
        """Запуск GUI"""
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        self.root.mainloop()
    
    def on_closing(self):
        """Закрытие приложения"""
        self.stop()
        self.cleanup_temp_dir()
        if self.keyboard_listener:
            self.keyboard_listener.stop()
        
        # Отвязываем события прокрутки
        try:
            self.canvas.unbind_all("<MouseWheel>")
        except:
            pass
        
        self.root.destroy()

if __name__ == "__main__":
    print("="*60)
    print("osu! Relax Bot v3.1 - Window Detection")
    print("="*60)
    
    # Проверка pywin32
    try:
        import win32gui
        import win32process
        print("✓ pywin32 установлен")
    except ImportError:
        print("❌ ВНИМАНИЕ: pywin32 не установлен!")
        print("   Автостарт работать не будет!")
        print("   Установите: pip install pywin32 --break-system-packages")
        input("\nНажмите Enter для продолжения...")
    
    if not is_admin():
        print("⚠ ВНИМАНИЕ: Требуются права администратора!")
        print("Попытка перезапуска с правами администратора...")
        if run_as_admin():
            sys.exit(0)
        else:
            print("❌ Не удалось получить права администратора.")
            print("⚠ Запускаем без админ-прав (может не работать с osu!lazer)")
            input("Нажмите Enter для продолжения...")
    
    bot = RelaxBot()
    bot.run()