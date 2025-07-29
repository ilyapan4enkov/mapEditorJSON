import tkinter as tk
from tkinter import ttk, filedialog
import json
import math
from collections import defaultdict
import random
import copy
from PIL import Image, ImageDraw, ImageTk

SCALE = 5

GRID_SIZE = 32
DOOR_BASE_WIDTH = GRID_SIZE * 2  # 64
DOOR_BASE_HEIGHT = 10     # 10
WALL_BASE_WIDTH = GRID_SIZE * 4  # 128
WALL_BASE_HEIGHT = GRID_SIZE     # 32
ENEMY_RADIUS = GRID_SIZE // 2  # базовый радиус для отображения врага
PLAYERSPAWNS_RADIUS = GRID_SIZE // 2  # радиус точки спавна

CANVAS_WIDTH = 1280
CANVAS_HEIGHT = 720
SIDEBAR_WIDTH = 320

class MapEditor(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("2D Map JSON Generator with Rotation")
        self.geometry(f"{CANVAS_WIDTH + SIDEBAR_WIDTH}x{CANVAS_HEIGHT}")

        self.zoom = 1.0
        self.offset_x = 0
        self.offset_y = 0

        self.panning = False
        self.pan_start = (0, 0)

        self.sidebar = ttk.Frame(self, width=SIDEBAR_WIDTH)
        self.sidebar.pack(side="left", fill="y")
        self.sidebar.pack_propagate(False)

        self.object_type = tk.StringVar(value="wall")

        # --- Верхняя часть: тип объекта и параметры ---
        self.top_frame = ttk.Frame(self.sidebar)
        self.top_frame.pack(side="top", fill="x", expand=False, pady=(10, 0))

        ttk.Label(self.top_frame, text="Тип объекта:").pack(pady=5, anchor="w", padx=10)
        self.type_buttons = []
        for t in ["wall", "door", "ivent", "enemy", "playerSpawns"]:
            btn = ttk.Radiobutton(self.top_frame, text=t, variable=self.object_type, value=t, command=self.update_ui_controls)
            btn.pack(anchor="w", padx=20)
            self.type_buttons.append(btn)

        self.param_frame = ttk.Frame(self.top_frame)
        self.param_frame.pack(fill="x", pady=(10, 0))

        self.width_label = ttk.Label(self.param_frame, text="Ширина:")
        self.width_var = tk.IntVar(value=WALL_BASE_WIDTH)
        self.width_entry = ttk.Entry(self.param_frame, textvariable=self.width_var, width=10)

        self.height_label = ttk.Label(self.param_frame, text="Высота:")
        self.height_var = tk.IntVar(value=WALL_BASE_HEIGHT)
        self.height_entry = ttk.Entry(self.param_frame, textvariable=self.height_var, width=10)

        self.scale_label = ttk.Label(self.param_frame, text="Масштаб (двери/ивенты):")
        self.scale_var = tk.DoubleVar(value=1.0)
        self.scale_entry = ttk.Entry(self.param_frame, textvariable=self.scale_var, width=10)

        self.ivent_label = ttk.Label(self.param_frame, text="ID ивент-зоны:")
        self.ivent_id_var = tk.IntVar(value=0)
        self.ivent_id_spinbox = ttk.Spinbox(self.param_frame, from_=0, to=9999, textvariable=self.ivent_id_var, width=10)

        # --- Enemy parameters ---
        self.enemy_label = ttk.Label(self.param_frame, text="ID врага:")
        self.enemy_id_var = tk.IntVar(value=0)
        self.enemy_id_spinbox = ttk.Spinbox(self.param_frame, from_=0, to=9999, textvariable=self.enemy_id_var, width=10)

        self.angle_label = ttk.Label(self.param_frame, text="Угол (градусы):")
        self.angle_var = tk.DoubleVar(value=0.0)
        self.angle_entry = ttk.Entry(self.param_frame, textvariable=self.angle_var, width=10)

        ttk.Separator(self.sidebar).pack(fill="x", pady=10)

        # --- Координаты ---
        self.coord_frame = ttk.Frame(self.sidebar)
        self.coord_frame.pack(side="top", fill="x", pady=(0, 0))
        ttk.Label(self.coord_frame, text="Координаты центра:").pack(pady=(5, 0), anchor="w", padx=10)
        self.coord_label = ttk.Label(self.coord_frame, text="X: — , Y: —")
        self.coord_label.pack(anchor="w", padx=20)
        ttk.Label(self.coord_frame, text="Точка вращения (origin):").pack(pady=(5, 0), anchor="w", padx=10)
        self.origin_label = ttk.Label(self.coord_frame, text="X: — , Y: —")
        self.origin_label.pack(anchor="w", padx=20)

        # --- Количество выбранных объектов ---
        self.selected_count_label = ttk.Label(self.coord_frame, text="Выделено объектов: 0")
        self.selected_count_label.pack(anchor="w", padx=20, pady=(10, 0))

        # --- Кнопки внизу ---
        self.button_frame = ttk.Frame(self.sidebar)
        self.button_frame.pack(side="bottom", fill="x", pady=20)
        self.change_btn = ttk.Button(self.button_frame, text="Изменить", command=self.apply_changes)
        self.change_btn.pack(fill="x", padx=20, pady=(0, 10))
        self.save_btn = ttk.Button(self.button_frame, text="Сохранить JSON", command=self.save_json)
        self.save_btn.pack(fill="x", padx=20)
        self.load_btn = ttk.Button(self.button_frame, text="Загрузить JSON", command=self.load_json)
        self.load_btn.pack(fill="x", padx=20, pady=(0, 10))
        self.gen_btn = ttk.Button(self.button_frame, text="Сгенерировать уровень", command=self.generate_level)
        self.gen_btn.pack(fill="x", padx=20, pady=(0, 10))

        self.objects = {
            "walls": [],
            "doors": [],
            "iventAreas": [],
            "enemies": [],
            "playerSpawns": []
        }
        self.canvas_objects = []

        self.selected = None  # для совместимости, но не используется
        self.selected_objects = []  # список (obj, obj_type)
        self.drag_offset = (0, 0)
        self.drag_offsets_multi = []  # для группового drag
        self.moving_origin = False
        self.drag_angle = 0.0
        self.drag_origin = None
        self.drag_start = None
        self.select_box_start = None
        self.select_box_rect = None
        self.is_group_drag = False
        # (playerSpawn has no rotation)

        self.type_map = {
            "wall": "walls",
            "door": "doors",
            "ivent": "iventAreas",
            "enemy": "enemies",
            "playerSpawns": "playerSpawns"
        }

        self.canvas = tk.Canvas(self, bg="white")
        self.canvas.pack(side="right", fill="both", expand=True)
        self.canvas.bind('<Configure>', self.on_resize)

        self.canvas.bind("<Button-1>", self.on_left_click)
        self.canvas.bind("<B1-Motion>", self.on_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_release)
        self.canvas.bind("<Button-3>", self.on_right_click)
        self.canvas.bind("<MouseWheel>", self.on_mousewheel)

        self.canvas.bind("<Button-2>", self.on_pan_start)
        self.canvas.bind("<B2-Motion>", self.on_pan_move)
        self.canvas.bind("<ButtonRelease-2>", self.on_pan_end)

        self.raster_bg = None
        self.raster_bg_cache = {
            'zoom': None,
            'offset_x': None,
            'offset_y': None,
            'size': (None, None),
            'objects_hash': None
        }

        self.update_ui_controls()
        self.draw_all()

        # Бинды на стрелки для перемещения выделенного объекта
        self.bind_all('<Up>', lambda e: self.on_arrow_key('up', e))
        self.bind_all('<Down>', lambda e: self.on_arrow_key('down', e))
        self.bind_all('<Left>', lambda e: self.on_arrow_key('left', e))
        self.bind_all('<Right>', lambda e: self.on_arrow_key('right', e))
        self.bind_all('<Escape>', lambda e: self.clear_selection())
        self.bind_all('<Control-c>', self.on_ctrl_c)
        self.bind_all('<Control-C>', self.on_ctrl_c)
        self.bind_all('<Control-v>', self.on_ctrl_v)
        self.bind_all('<Control-V>', self.on_ctrl_v)

    def update_ui_controls(self):
        t = self.object_type.get()

        # Очищаем параметры
        for widget in [self.width_label, self.width_entry,
                       self.height_label, self.height_entry,
                       self.scale_label, self.scale_entry,
                       self.ivent_label, self.ivent_id_spinbox,
                       self.enemy_label, self.enemy_id_spinbox,
                       self.angle_label, self.angle_entry]:
            widget.pack_forget()

        # Параметры в param_frame
        if t == "door":
            self.scale_label.pack(anchor="w", padx=10, pady=2)
            self.scale_entry.pack(anchor="w", padx=20, pady=2)
            self.angle_label.pack(anchor="w", padx=10, pady=2)
            self.angle_entry.pack(anchor="w", padx=20, pady=2)
        elif t == "ivent":
            self.width_label.pack(anchor="w", padx=10, pady=2)
            self.width_entry.pack(anchor="w", padx=20, pady=2)
            self.height_label.pack(anchor="w", padx=10, pady=2)
            self.height_entry.pack(anchor="w", padx=20, pady=2)
            self.scale_label.pack(anchor="w", padx=10, pady=2)
            self.scale_entry.pack(anchor="w", padx=20, pady=2)
            self.angle_label.pack(anchor="w", padx=10, pady=2)
            self.angle_entry.pack(anchor="w", padx=20, pady=2)
            self.ivent_label.pack(anchor="w", padx=10, pady=2)
            self.ivent_id_spinbox.pack(anchor="w", padx=20, pady=2)
        elif t == "enemy":
            self.enemy_label.pack(anchor="w", padx=10, pady=2)
            self.enemy_id_spinbox.pack(anchor="w", padx=20, pady=2)
        elif t == "playerSpawns":
            # у спавна нет дополнительных параметров
            pass
        else:
            # wall
            self.width_label.pack(anchor="w", padx=10, pady=2)
            self.width_entry.pack(anchor="w", padx=20, pady=2)
            self.height_label.pack(anchor="w", padx=10, pady=2)
            self.height_entry.pack(anchor="w", padx=20, pady=2)
            self.angle_label.pack(anchor="w", padx=10, pady=2)
            self.angle_entry.pack(anchor="w", padx=20, pady=2)

        self.draw_all()

    def clear_params_inputs(self):
        pass  # Отключаем сброс параметров полностью

    def draw_all(self):
        # Удаляем всё, кроме рамки выделения
        for item in self.canvas.find_all():
            if "select_box" not in self.canvas.gettags(item):
                self.canvas.delete(item)
        self.canvas_objects.clear()
        self.draw_grid()

        w = self.canvas.winfo_width()
        h = self.canvas.winfo_height()
        left = (-self.offset_x) / self.zoom
        top = (-self.offset_y) / self.zoom
        right = left + w / self.zoom
        bottom = top + h / self.zoom

        total_objs = sum(len(self.objects[t]) for t in self.objects)
        simple_mode = total_objs > 500

        # --- РАСТРОВЫЙ СЛОЙ ФОНА ---
        # Хэшируем только стены/двери/ивенты
        bg_hash = hash(str([
            [(o['pos'], o.get('width'), o.get('height'), o.get('scale'), o.get('angle'), o.get('origin')) for o in self.objects['walls']],
            [(o['pos'], o.get('scale'), o.get('angle'), o.get('origin')) for o in self.objects['doors']],
            [(o['pos'], o.get('width'), o.get('height'), o.get('scale'), o.get('angle'), o.get('origin')) for o in self.objects['iventAreas']]
        ]))
        cache = self.raster_bg_cache
        need_redraw = (
            cache['zoom'] != self.zoom or
            cache['offset_x'] != self.offset_x or
            cache['offset_y'] != self.offset_y or
            cache['size'] != (w, h) or
            cache['objects_hash'] != bg_hash
        )
        if need_redraw:
            img = Image.new('RGBA', (w, h), (0,0,0,0))
            draw = ImageDraw.Draw(img)
            # Стены
            for obj in self.objects['walls']:
                scale = obj.get('scale', 1.0)
                angle = obj.get('angle', 0.0)
                origin = obj.get('origin', obj['pos'])
                pos = obj['pos']
                rotated_pos = self.rotate_point(pos[0], pos[1], origin[0], origin[1], angle)
                ww = obj['width'] * scale
                hh = obj['height'] * scale
                # bbox
                x0 = (rotated_pos[0] - ww/2) * self.zoom + self.offset_x
                y0 = (rotated_pos[1] - hh/2) * self.zoom + self.offset_y
                x1 = (rotated_pos[0] + ww/2) * self.zoom + self.offset_x
                y1 = (rotated_pos[1] + hh/2) * self.zoom + self.offset_y
                # Поворот только если angle!=0
                if abs(angle) > 0.01:
                    # Рисуем как многоугольник
                    rad = math.radians(angle)
                    hw, hh2 = ww/2, hh/2
                    corners = [
                        (-hw, -hh2), (hw, -hh2), (hw, hh2), (-hw, hh2)
                    ]
                    pts = []
                    for px, py in corners:
                        xr = rotated_pos[0] + px * math.cos(rad) - py * math.sin(rad)
                        yr = rotated_pos[1] + px * math.sin(rad) + py * math.cos(rad)
                        pts.append((xr * self.zoom + self.offset_x, yr * self.zoom + self.offset_y))
                    draw.polygon(pts, fill=(180,180,180,255))
                else:
                    draw.rectangle([x0, y0, x1, y1], fill=(180,180,180,255))
            # Двери
            for obj in self.objects['doors']:
                scale = obj.get('scale', 1.0)
                angle = obj.get('angle', 0.0)
                origin = obj.get('origin', obj['pos'])
                pos = obj['pos']
                rotated_pos = self.rotate_point(pos[0], pos[1], origin[0], origin[1], angle)
                ww = DOOR_BASE_WIDTH * scale
                hh = DOOR_BASE_HEIGHT * scale
                x0 = (rotated_pos[0] - ww/2) * self.zoom + self.offset_x
                y0 = (rotated_pos[1] - hh/2) * self.zoom + self.offset_y
                x1 = (rotated_pos[0] + ww/2) * self.zoom + self.offset_x
                y1 = (rotated_pos[1] + hh/2) * self.zoom + self.offset_y
                if abs(angle) > 0.01:
                    rad = math.radians(angle)
                    hw, hh2 = ww/2, hh/2
                    corners = [
                        (-hw, -hh2), (hw, -hh2), (hw, hh2), (-hw, hh2)
                    ]
                    pts = []
                    for px, py in corners:
                        xr = rotated_pos[0] + px * math.cos(rad) - py * math.sin(rad)
                        yr = rotated_pos[1] + px * math.sin(rad) + py * math.cos(rad)
                        pts.append((xr * self.zoom + self.offset_x, yr * self.zoom + self.offset_y))
                    draw.polygon(pts, fill=(170,120,70,255))
                else:
                    draw.rectangle([x0, y0, x1, y1], fill=(170,120,70,255))
            # Ивенты
            for obj in self.objects['iventAreas']:
                scale = obj.get('scale', 1.0)
                angle = obj.get('angle', 0.0)
                origin = obj.get('origin', obj['pos'])
                pos = obj['pos']
                rotated_pos = self.rotate_point(pos[0], pos[1], origin[0], origin[1], angle)
                ww = obj['width'] * scale
                hh = obj['height'] * scale
                x0 = (rotated_pos[0] - ww/2) * self.zoom + self.offset_x
                y0 = (rotated_pos[1] - hh/2) * self.zoom + self.offset_y
                x1 = (rotated_pos[0] + ww/2) * self.zoom + self.offset_x
                y1 = (rotated_pos[1] + hh/2) * self.zoom + self.offset_y
                if abs(angle) > 0.01:
                    rad = math.radians(angle)
                    hw, hh2 = ww/2, hh/2
                    corners = [
                        (-hw, -hh2), (hw, -hh2), (hw, hh2), (-hw, hh2)
                    ]
                    pts = []
                    for px, py in corners:
                        xr = rotated_pos[0] + px * math.cos(rad) - py * math.sin(rad)
                        yr = rotated_pos[1] + px * math.sin(rad) + py * math.cos(rad)
                        pts.append((xr * self.zoom + self.offset_x, yr * self.zoom + self.offset_y))
                    draw.polygon(pts, fill=(255,100,100,180))
                else:
                    draw.rectangle([x0, y0, x1, y1], fill=(255,100,100,180))
            self.raster_bg = ImageTk.PhotoImage(img)
            cache['zoom'] = self.zoom
            cache['offset_x'] = self.offset_x
            cache['offset_y'] = self.offset_y
            cache['size'] = (w, h)
            cache['objects_hash'] = bg_hash
        if self.raster_bg:
            self.canvas.create_image(0, 0, anchor='nw', image=self.raster_bg, tags='raster_bg')

        # --- Динамические объекты ---
        for obj_type in self.objects:
            if obj_type in ('walls', 'doors', 'iventAreas'):
                continue  # уже нарисованы на фоне
            for obj in self.objects[obj_type]:
                if any(sel[0] is obj for sel in self.selected_objects):
                    continue
                pos = obj["pos"]
                scale = obj.get("scale", 1.0)
                angle = obj.get("angle", 0.0)
                origin = obj.get("origin", pos)
                rotated_pos = self.rotate_point(pos[0], pos[1], origin[0], origin[1], angle)
                if obj_type == "enemies":
                    r = ENEMY_RADIUS * scale
                    self.canvas.create_oval((rotated_pos[0]-r)*self.zoom + self.offset_x,
                                            (rotated_pos[1]-r)*self.zoom + self.offset_y,
                                            (rotated_pos[0]+r)*self.zoom + self.offset_x,
                                            (rotated_pos[1]+r)*self.zoom + self.offset_y,
                                            fill="purple", outline="")
                elif obj_type == "playerSpawns":
                    r = PLAYERSPAWNS_RADIUS * scale
                    self.canvas.create_oval((rotated_pos[0]-r)*self.zoom + self.offset_x,
                                            (rotated_pos[1]-r)*self.zoom + self.offset_y,
                                            (rotated_pos[0]+r)*self.zoom + self.offset_x,
                                            (rotated_pos[1]+r)*self.zoom + self.offset_y,
                                            fill="green", outline="")
        # ... остальной код draw_all (оси, выделение, origin) ...

        zero_x, zero_y = self.to_canvas_coords(0, 0)
        w = self.canvas.winfo_width()
        h = self.canvas.winfo_height()
        self.canvas.create_line(0, zero_y, w, zero_y, fill="green", width=2)
        self.canvas.create_line(zero_x, 0, zero_x, h, fill="green", width=2)
        self.canvas.create_text(zero_x + 10, zero_y + 15, text="0,0", fill="green", font=("Arial", 10, "bold"))

        # Групповое выделение
        for obj, obj_type in self.selected_objects:
            scale = obj.get("scale", 1.0)
            angle = obj.get("angle", 0.0)
            origin = obj.get("origin", obj["pos"])
            pos = obj["pos"]
            rotated_pos = self.rotate_point(pos[0], pos[1], origin[0], origin[1], angle)
            if obj_type == "walls":
                w = obj["width"] * scale
                h = obj["height"] * scale
                self.draw_rotated_rect(rotated_pos[0], rotated_pos[1], w, h, angle, outline="blue", width=3, fill="", pivot="center")
                self.draw_rotated_rect(rotated_pos[0], rotated_pos[1], w, h, angle, fill="gray", pivot="center")
            elif obj_type == "doors":
                w = DOOR_BASE_WIDTH * scale
                h = DOOR_BASE_HEIGHT * scale
                self.draw_rotated_rect(rotated_pos[0], rotated_pos[1], w, h, angle, outline="blue", width=3, fill="", pivot="center")
                self.draw_rotated_rect(rotated_pos[0], rotated_pos[1], w, h, angle, fill="brown", pivot="center")
            elif obj_type == "iventAreas":
                w = obj["width"] * scale
                h = obj["height"] * scale
                self.draw_rotated_rect(rotated_pos[0], rotated_pos[1], w, h, angle, outline="blue", width=3, fill="", pivot="center")
                self.draw_rotated_rect(rotated_pos[0], rotated_pos[1], w, h, angle, fill="red", pivot="center")
            elif obj_type == "enemies":
                r = ENEMY_RADIUS * scale
                # синяя обводка
                self.canvas.create_oval((rotated_pos[0]-r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]-r)*self.zoom + self.offset_y,
                                        (rotated_pos[0]+r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]+r)*self.zoom + self.offset_y,
                                        outline="blue", width=3, fill="")
                # заполнение
                self.canvas.create_oval((rotated_pos[0]-r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]-r)*self.zoom + self.offset_y,
                                        (rotated_pos[0]+r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]+r)*self.zoom + self.offset_y,
                                        outline="", fill="purple")
            elif obj_type == "playerSpawns":
                r = PLAYERSPAWNS_RADIUS * scale
                # outline
                self.canvas.create_oval((rotated_pos[0]-r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]-r)*self.zoom + self.offset_y,
                                        (rotated_pos[0]+r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]+r)*self.zoom + self.offset_y,
                                        outline="blue", width=3, fill="")
                # fill
                self.canvas.create_oval((rotated_pos[0]-r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]-r)*self.zoom + self.offset_y,
                                        (rotated_pos[0]+r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]+r)*self.zoom + self.offset_y,
                                        outline="", fill="green")
                # no arrow for playerSpawns

            # Кружок origin только для последнего выделенного
        if self.selected_objects:
            obj, obj_type = self.selected_objects[-1]
            if obj_type not in ("enemies", "playerSpawns"):  # не показываем origin для врагов
                origin = obj.get("origin", obj["pos"])
                ox, oy = self.to_canvas_coords(*origin)
                r = 10
                self.canvas.create_oval(ox - r, oy - r, ox + r, oy + r, outline="#0077ff", width=2, fill="#e6f0ff", tags="origin_handle")
                self.canvas.create_line(ox, oy, ox, oy - 18, arrow=tk.LAST, fill="#0077ff", width=2, tags="origin_handle")
                self.origin_label.config(text=f"X: {origin[0]:.1f}, Y: {origin[1]:.1f}")
            else:
                self.origin_label.config(text="—")

    def draw_grid(self):
        step = GRID_SIZE * self.zoom
        left = -self.offset_x / self.zoom
        top = -self.offset_y / self.zoom
        right = left + CANVAS_WIDTH / self.zoom
        bottom = top + CANVAS_HEIGHT / self.zoom

        start_x = int(left // GRID_SIZE * GRID_SIZE)
        end_x = int((right // GRID_SIZE + 2) * GRID_SIZE)
        start_y = int(top // GRID_SIZE * GRID_SIZE)
        end_y = int((bottom // GRID_SIZE + 2) * GRID_SIZE)

        for x in range(start_x, end_x, GRID_SIZE):
            x_screen = x * self.zoom + self.offset_x
            self.canvas.create_line(x_screen, 0, x_screen, CANVAS_HEIGHT, fill="#ddd", tags="grid_line")

        for y in range(start_y, end_y, GRID_SIZE):
            y_screen = y * self.zoom + self.offset_y
            self.canvas.create_line(0, y_screen, CANVAS_WIDTH, y_screen, fill="#ddd", tags="grid_line")

    def snap_to_grid(self, x, y):
        # Привязка центра к сетке
        return round(x / GRID_SIZE) * GRID_SIZE, round(y / GRID_SIZE) * GRID_SIZE

    def to_canvas_coords(self, x, y):
        return x * self.zoom + self.offset_x, y * self.zoom + self.offset_y

    def from_canvas_coords(self, x, y):
        return (x - self.offset_x) / self.zoom, (y - self.offset_y) / self.zoom

    def point_in_rotated_rect(self, px, py, x, y, w, h, angle_deg, pivot="center"):
        """ Проверка попадания точки (px, py) в повернутый прямоугольник. """
        angle = math.radians(-angle_deg)

        if pivot == "center":
            cx, cy = x, y
            rel_x = px - cx
            rel_y = py - cy
            # Обратный поворот
            unrotated_x = rel_x * math.cos(angle) - rel_y * math.sin(angle)
            unrotated_y = rel_x * math.sin(angle) + rel_y * math.cos(angle)
            return -w / 2 <= unrotated_x <= w / 2 and -h / 2 <= unrotated_y <= h / 2

        elif pivot == "topleft":
            # Относительно левого верхнего угла
            rel_x = px - x
            rel_y = py - y
            # Обратный поворот
            unrotated_x = rel_x * math.cos(angle) - rel_y * math.sin(angle)
            unrotated_y = rel_x * math.sin(angle) + rel_y * math.cos(angle)
            return 0 <= unrotated_x <= w and 0 <= unrotated_y <= h

        else:
            raise ValueError("Invalid pivot")


    def draw_rotated_rect(self, x, y, w, h, angle, pivot="center", **kwargs):
        rad = math.radians(angle)

        if pivot == "center":
            cx, cy = x, y
            hw, hh = w / 2, h / 2
            corners = [
                (-hw, -hh),
                (hw, -hh),
                (hw, hh),
                (-hw, hh),
            ]
        elif pivot == "topleft":
            cx, cy = x, y
            corners = [
                (0, 0),
                (w, 0),
                (w, h),
                (0, h),
            ]
        else:
            raise ValueError("pivot must be 'center' or 'topleft'")

        points = []
        for px, py in corners:
            xr = cx + (px * math.cos(rad) - py * math.sin(rad))
            yr = cy + (px * math.sin(rad) + py * math.cos(rad))
            points.extend([xr * self.zoom + self.offset_x, yr * self.zoom + self.offset_y])

        self.canvas.create_polygon(points, **kwargs, joinstyle="round")

    def draw_object(self, obj, obj_type, simple_mode=False):
        scale = obj.get("scale", 1.0)
        angle = obj.get("angle", 0.0)
        origin = obj.get("origin", obj["pos"])
        pos = obj["pos"]
        rotated_pos = self.rotate_point(pos[0], pos[1], origin[0], origin[1], angle)

        if obj_type == "walls":
            w = obj["width"] * scale
            h = obj["height"] * scale
            if simple_mode:
                self.draw_rotated_rect(rotated_pos[0], rotated_pos[1], w, h, angle, pivot="center", fill="#bbbbbb")
            else:
                self.draw_rotated_rect(rotated_pos[0], rotated_pos[1], w, h, angle, pivot="center", fill="gray")
        elif obj_type == "doors":
            w = DOOR_BASE_WIDTH * scale
            h = DOOR_BASE_HEIGHT * scale
            if simple_mode:
                self.draw_rotated_rect(rotated_pos[0], rotated_pos[1], w, h, angle, pivot="center", fill="#a97b50")
            else:
                self.draw_rotated_rect(rotated_pos[0], rotated_pos[1], w, h, angle, pivot="center", fill="brown")
        elif obj_type == "iventAreas":
            w = obj["width"] * scale
            h = obj["height"] * scale
            if simple_mode:
                self.draw_rotated_rect(rotated_pos[0], rotated_pos[1], w, h, angle, pivot="center", fill="#ffb3b3")
            else:
                self.draw_rotated_rect(rotated_pos[0], rotated_pos[1], w, h, angle, pivot="center", fill="red")
        elif obj_type == "enemies":
            r = ENEMY_RADIUS * scale
            if simple_mode:
                self.canvas.create_oval((rotated_pos[0]-r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]-r)*self.zoom + self.offset_y,
                                        (rotated_pos[0]+r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]+r)*self.zoom + self.offset_y,
                                        fill="#a080c0", outline="")
            else:
                self.canvas.create_oval((rotated_pos[0]-r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]-r)*self.zoom + self.offset_y,
                                        (rotated_pos[0]+r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]+r)*self.zoom + self.offset_y,
                                        fill="purple", outline="")
        elif obj_type == "playerSpawns":
            r = PLAYERSPAWNS_RADIUS * scale
            if simple_mode:
                self.canvas.create_oval((rotated_pos[0]-r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]-r)*self.zoom + self.offset_y,
                                        (rotated_pos[0]+r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]+r)*self.zoom + self.offset_y,
                                        fill="#7fd97f", outline="")
            else:
                self.canvas.create_oval((rotated_pos[0]-r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]-r)*self.zoom + self.offset_y,
                                        (rotated_pos[0]+r)*self.zoom + self.offset_x,
                                        (rotated_pos[1]+r)*self.zoom + self.offset_y,
                                        fill="green", outline="")
            # no arrow for playerSpawns

        self.canvas_objects.append((obj, obj_type))

    @staticmethod
    def rotate_point(px, py, ox, oy, a_deg):
        import math
        a = math.radians(a_deg)
        dx, dy = px - ox, py - oy
        rx = ox + dx * math.cos(a) - dy * math.sin(a)
        ry = oy + dx * math.sin(a) + dy * math.cos(a)
        return rx, ry

    @staticmethod
    def rotate_point_inv(rx, ry, ox, oy, a_deg):
        # Обратный поворот
        import math
        a = math.radians(-a_deg)
        dx, dy = rx - ox, ry - oy
        px = ox + dx * math.cos(a) - dy * math.sin(a)
        py = oy + dx * math.sin(a) + dy * math.cos(a)
        return px, py

    def on_left_click(self, event):
        x, y = self.from_canvas_coords(event.x, event.y)
        # Shift+клик в пустоту — начать выделение рамкой
        if event.state & 0x0001 and not any(self.point_in_rotated_rect(x, y, *self.rotate_point(obj["pos"][0], obj["pos"][1], obj.get("origin", obj["pos"])[0], obj.get("origin", obj["pos"])[1], obj.get("angle", 0.0)),
                                            obj.get("width", 0) * obj.get("scale", 1.0) if t == "walls" or t == "iventAreas" else DOOR_BASE_WIDTH * obj.get("scale", 1.0),
                                            obj.get("height", 0) * obj.get("scale", 1.0) if t == "walls" or t == "iventAreas" else DOOR_BASE_HEIGHT * obj.get("scale", 1.0),
                                            obj.get("angle", 0.0), pivot="center")
                        for t in self.objects for obj in self.objects[t]):
            self.select_box_start = (event.x, event.y)
            self.select_box_rect = self.canvas.create_rectangle(event.x, event.y, event.x, event.y, outline="#3399ff", width=2, dash=(4, 2), tags="select_box")
            self.is_group_drag = False
            self.canvas.config(cursor="arrow")
            return
        # Проверяем, клик по origin
        if self.selected_objects:
            obj, obj_type_sel = self.selected_objects[-1]
            origin = obj.get("origin", obj["pos"])
            ox, oy = self.to_canvas_coords(*origin)
            # origin handle (для не-врагов/спавна)
            if obj_type_sel not in ("enemies", "playerSpawns") and (event.x - ox) ** 2 + (event.y - oy) ** 2 <= 100:
                self.moving_origin = True
                return

            # проверка клика по стрелке playerSpawns
            if obj_type_sel == "playerSpawns":
                # tip of arrow
                r_tip = PLAYERSPAWNS_RADIUS * 1.5
                angle_deg = obj.get("angle", 0.0)
                import math
                tip_x_world = obj["pos"][0] + math.cos(math.radians(angle_deg)) * r_tip
                tip_y_world = obj["pos"][1] + math.sin(math.radians(angle_deg)) * r_tip
                tip_cx, tip_cy = self.to_canvas_coords(tip_x_world, tip_y_world)
                if (event.x - tip_cx) ** 2 + (event.y - tip_cy) ** 2 <= 100:  # радиус 10
                    self.moving_spawn_angle = True
                    return

        found = False
        found_obj = None
        found_obj_type = None
        found_drag_offset = None
        found_angle = None
        found_origin = None

        for obj_type in reversed(list(self.objects.keys())):
            for obj in reversed(self.objects[obj_type]):
                scale = obj.get("scale", 1.0)
                angle = obj.get("angle", 0.0)
                origin = obj.get("origin", obj["pos"])
                pos = obj["pos"]
                rotated_pos = self.rotate_point(pos[0], pos[1], origin[0], origin[1], angle)

                if obj_type == "walls":
                    w = obj["width"] * scale
                    h = obj["height"] * scale
                    if self.point_in_rotated_rect(x, y, rotated_pos[0], rotated_pos[1], w, h, angle, pivot="center"):
                        found = True
                        found_obj = obj
                        found_obj_type = obj_type
                        found_drag_offset = (x - rotated_pos[0], y - rotated_pos[1])
                        found_angle = angle
                        found_origin = origin[:]
                        break

                elif obj_type == "doors":
                    w = DOOR_BASE_WIDTH * scale
                    h = DOOR_BASE_HEIGHT * scale
                    if self.point_in_rotated_rect(x, y, rotated_pos[0], rotated_pos[1], w, h, angle, pivot="center"):
                        found = True
                        found_obj = obj
                        found_obj_type = obj_type
                        found_drag_offset = (x - rotated_pos[0], y - rotated_pos[1])
                        found_angle = angle
                        found_origin = origin[:]
                        break

                elif obj_type == "iventAreas":
                    w = obj["width"] * scale
                    h = obj["height"] * scale
                    if self.point_in_rotated_rect(x, y, rotated_pos[0], rotated_pos[1], w, h, angle, pivot="center"):
                        found = True
                        found_obj = obj
                        found_obj_type = obj_type
                        found_drag_offset = (x - rotated_pos[0], y - rotated_pos[1])
                        found_angle = angle
                        found_origin = origin[:]
                        break
                elif obj_type == "enemies":
                    r = ENEMY_RADIUS
                    if (x - pos[0]) ** 2 + (y - pos[1]) ** 2 <= r ** 2:
                        found = True
                        found_obj = obj
                        found_obj_type = obj_type
                        found_drag_offset = (x - pos[0], y - pos[1])
                        found_angle = 0.0
                        found_origin = obj.get("origin", pos)
                        break
                elif obj_type == "playerSpawns":
                    r = PLAYERSPAWNS_RADIUS
                    if (x - pos[0]) ** 2 + (y - pos[1]) ** 2 <= r ** 2:
                        found = True
                        found_obj = obj
                        found_obj_type = obj_type
                        found_drag_offset = (x - pos[0], y - pos[1])
                        found_angle = 0.0
                        found_origin = obj.get("origin", pos)
                        break
            if found:
                break
        if found:
            # Ctrl — добавить/убрать объект из выделения
            if event.state & 0x0004:
                already = any(found_obj is o for o, _ in self.selected_objects)
                if already:
                    self.selected_objects = [item for item in self.selected_objects if item[0] is not found_obj]
                else:
                    self.selected_objects.append((found_obj, found_obj_type))
            else:
                self.selected_objects = [(found_obj, found_obj_type)]
            # drag_offset для группового drag
            self.drag_offset = found_drag_offset
            self.drag_angle = found_angle
            self.drag_origin = found_origin
            # Для группового drag всегда пересчитываем смещения для всех выделенных
            self.drag_offsets_multi = []
            for o, t in self.selected_objects:
                scale = o.get("scale", 1.0)
                angle = o.get("angle", 0.0)
                origin = o.get("origin", o["pos"])
                pos = o["pos"]
                rotated_pos = self.rotate_point(pos[0], pos[1], origin[0], origin[1], angle)
                self.drag_offsets_multi.append((x - rotated_pos[0], y - rotated_pos[1]))
            self.update_params_ui()
            self.draw_all()
            return  # Не создавать новый объект, если уже выбран
        # Клик вне объектов
        if event.state & 0x0004:
            if self.selected_objects:
                # Если Ctrl зажат и есть выделение — начинаем drag группы от курсора
                self.drag_offsets_multi = []
                for o, t in self.selected_objects:
                    scale = o.get("scale", 1.0)
                    angle = o.get("angle", 0.0)
                    origin = o.get("origin", o["pos"])
                    pos = o["pos"]
                    rotated_pos = self.rotate_point(pos[0], pos[1], origin[0], origin[1], angle)
                    self.drag_offsets_multi.append((x - rotated_pos[0], y - rotated_pos[1]))
                self.drag_offset = self.drag_offsets_multi[-1] if self.drag_offsets_multi else (0, 0)
                self.drag_angle = self.selected_objects[-1][0].get("angle", 0.0)
                self.drag_origin = self.selected_objects[-1][0].get("origin", self.selected_objects[-1][0]["pos"])
                self.drag_start = (x, y)
                self.is_group_drag = True
                self.canvas.config(cursor="fleur")
                return
            # Если Ctrl зажат, но выделения нет — ничего не делать
            self.drag_offsets_multi = []
            self.drag_offset = (0, 0)
            self.drag_angle = 0.0
            self.drag_origin = None
            self.is_group_drag = False
            return
        # Если есть выделение — начать drag для группы (без Ctrl)
        if self.selected_objects:
            self.drag_offsets_multi = []
            for o, t in self.selected_objects:
                scale = o.get("scale", 1.0)
                angle = o.get("angle", 0.0)
                origin = o.get("origin", o["pos"])
                pos = o["pos"]
                rotated_pos = self.rotate_point(pos[0], pos[1], origin[0], origin[1], angle)
                self.drag_offsets_multi.append((x - rotated_pos[0], y - rotated_pos[1]))
            self.drag_offset = self.drag_offsets_multi[-1] if self.drag_offsets_multi else (0, 0)
            self.drag_angle = self.selected_objects[-1][0].get("angle", 0.0)
            self.drag_origin = self.selected_objects[-1][0].get("origin", self.selected_objects[-1][0]["pos"])
            self.drag_start = (x, y)
            self.is_group_drag = True
            self.canvas.config(cursor="fleur")
            return
        # Без Ctrl — сброс выделения
        self.selected_objects = []
        self.update_params_ui()
        self.draw_all()
        self.is_group_drag = False
        self.canvas.config(cursor="arrow")
        # Создаем новый объект
        self.selected = None
        # self.clear_params_inputs()  # УБРАНО: не сбрасываем поля
        self.draw_all()

        user_type = self.object_type.get()
        obj_type = self.type_map[user_type]

        if obj_type == "doors":
            scale = self.scale_var.get()
            w = DOOR_BASE_WIDTH * scale
            h = DOOR_BASE_HEIGHT * scale
            cx, cy = self.snap_to_grid(x, y)
            obj = {"pos": [cx, cy], "scale": scale, "angle": 0.0}
            self.objects["doors"].append(obj)
            self.selected = (obj, "doors")

        elif obj_type == "iventAreas":
            w = self.width_var.get()
            h = self.height_var.get()
            scale = self.scale_var.get()
            cx, cy = self.snap_to_grid(x, y)
            obj = {
                "pos": [cx, cy],
                "width": w,
                "height": h,
                "scale": scale,
                "id": self.ivent_id_var.get(),
                "angle": 0.0
            }
            self.objects["iventAreas"].append(obj)
            self.selected = (obj, "iventAreas")

        elif obj_type == "enemies":  # создание врага
            cx, cy = self.snap_to_grid(x, y)
            obj = {"pos": [cx, cy], "id": self.enemy_id_var.get(), "origin": [cx, cy]}
            self.objects["enemies"].append(obj)
            self.selected = (obj, "enemies")

        elif obj_type == "playerSpawns":  # создание точки спавна (множество)
            cx, cy = self.snap_to_grid(x, y)
            obj = {"pos": [cx, cy]}
            self.objects["playerSpawns"].append(obj)
            self.selected = (obj, "playerSpawns")

        else:  # стены
            w = self.width_var.get()
            h = self.height_var.get()
            cx, cy = self.snap_to_grid(x, y)
            obj = {"pos": [cx, cy], "width": w, "height": h, "scale": 1.0, "angle": 0.0}
            self.objects[obj_type].append(obj)
            self.selected = (obj, obj_type)

        self.selected_objects = [self.selected]
        self.apply_changes()  # применяем параметры из UI к объекту
        self.draw_all()       # обновляем отображение
        # self.update_params_ui()  # НЕ вызываем!

    def update_params_ui(self):
        # Обновляем количество выбранных объектов
        count = len(self.selected_objects)
        self.selected_count_label.config(text=f"Выделено объектов: {count}")
        if not self.selected_objects:
            self.clear_params_inputs()
            return

        obj, obj_type = self.selected_objects[-1]

        # Обновляем вид переключателя
        for val, btn in zip(["wall", "door", "ivent", "enemy", "playerSpawns"], self.type_buttons):
            if self.type_map[val] == obj_type:
                self.object_type.set(val)
                break

        # Скрываем все поля
        for w in [self.width_label, self.width_entry,
                  self.height_label, self.height_entry,
                  self.scale_label, self.scale_entry,
                  self.ivent_label, self.ivent_id_spinbox,
                  self.enemy_label, self.enemy_id_spinbox,
                  self.angle_label, self.angle_entry]:
            w.pack_forget()

        t = self.object_type.get()
        # Показываем нужные поля в param_frame
        if t == "door":
            self.scale_label.pack(anchor="w", padx=10, pady=2)
            self.scale_entry.pack(anchor="w", padx=20, pady=2)
            self.angle_label.pack(anchor="w", padx=10, pady=2)
            self.angle_entry.pack(anchor="w", padx=20, pady=2)
        elif t == "ivent":
            self.width_label.pack(anchor="w", padx=10, pady=2)
            self.width_entry.pack(anchor="w", padx=20, pady=2)
            self.height_label.pack(anchor="w", padx=10, pady=2)
            self.height_entry.pack(anchor="w", padx=20, pady=2)
            self.scale_label.pack(anchor="w", padx=10, pady=2)
            self.scale_entry.pack(anchor="w", padx=20, pady=2)
            self.angle_label.pack(anchor="w", padx=10, pady=2)
            self.angle_entry.pack(anchor="w", padx=20, pady=2)
            self.ivent_label.pack(anchor="w", padx=10, pady=2)
            self.ivent_id_spinbox.pack(anchor="w", padx=20, pady=2)
        elif t == "enemy":
            self.enemy_label.pack(anchor="w", padx=10, pady=2)
            self.enemy_id_spinbox.pack(anchor="w", padx=20, pady=2)
        elif t == "playerSpawns":
            pass
        else:
            # стена
            self.width_label.pack(anchor="w", padx=10, pady=2)
            self.width_entry.pack(anchor="w", padx=20, pady=2)
            self.height_label.pack(anchor="w", padx=10, pady=2)
            self.height_entry.pack(anchor="w", padx=20, pady=2)
            self.angle_label.pack(anchor="w", padx=10, pady=2)
            self.angle_entry.pack(anchor="w", padx=20, pady=2)

        # Подставляем текущие значения
        self.width_var.set(obj.get("width", WALL_BASE_WIDTH))
        self.height_var.set(obj.get("height", WALL_BASE_HEIGHT))
        self.scale_var.set(obj.get("scale", 1.0))
        self.angle_var.set(obj.get("angle", 0.0))
        self.ivent_id_var.set(obj.get("id", 0) if t == "ivent" else 0)
        self.enemy_id_var.set(obj.get("id", 0) if t == "enemy" else 0)

        # Координаты центра
        cx, cy = obj["pos"]
        self.coord_label.config(text=f"X: {cx:.1f}, Y: {cy:.1f}")
        if obj_type not in ("enemies", "playerSpawns"):
            ox, oy = obj.get("origin", obj["pos"])
            self.origin_label.config(text=f"X: {ox:.1f}, Y: {oy:.1f} (dx: {ox-cx:.1f}, dy: {oy-cy:.1f})")
        else:
            self.origin_label.config(text="—")


    def apply_changes(self):
        if not self.selected_objects:
            return

        for obj, obj_type in self.selected_objects:
            if obj_type == "walls":
                obj["width"] = max(1, self.width_var.get())
                obj["height"] = max(1, self.height_var.get())
                obj["angle"] = self.angle_var.get()
                obj["scale"] = 1.0

            elif obj_type == "doors":
                scale = max(0.1, self.scale_var.get())
                obj["scale"] = scale
                obj["angle"] = self.angle_var.get()

            elif obj_type == "iventAreas":
                obj["width"] = max(1, self.width_var.get())
                obj["height"] = max(1, self.height_var.get())
                obj["scale"] = max(0.1, self.scale_var.get())
                obj["angle"] = self.angle_var.get()
                obj["id"] = self.ivent_id_var.get()
            elif obj_type == "enemies":
                obj["id"] = self.enemy_id_var.get()
            elif obj_type == "playerSpawns":
                pass

        self.draw_all()

    def on_drag(self, event):
        # Если идёт выделение рамкой
        if self.select_box_start is not None:
            x0, y0 = self.select_box_start
            x1, y1 = event.x, event.y
            self.canvas.coords(self.select_box_rect, x0, y0, x1, y1)
            # Выделяем все объекты, чьи центры попали в рамку
            x_min, x_max = min(x0, x1), max(x0, x1)
            y_min, y_max = min(y0, y1), max(y0, y1)
            selected = []
            for t in self.objects:
                for obj in self.objects[t]:
                    scale = obj.get("scale", 1.0)
                    angle = obj.get("angle", 0.0)
                    origin = obj.get("origin", obj["pos"])
                    pos = obj["pos"]
                    rotated_pos = self.rotate_point(pos[0], pos[1], origin[0], origin[1], angle)
                    cx, cy = self.to_canvas_coords(*rotated_pos)
                    if x_min <= cx <= x_max and y_min <= cy <= y_max:
                        selected.append((obj, t))
            self.selected_objects = selected
            self.update_params_ui()
            self.draw_all()
            return

        # Если есть выделение и drag_offsets_multi — всегда перемещаем группу
        if not self.selected_objects or not self.drag_offsets_multi or len(self.drag_offsets_multi) != len(self.selected_objects):
            return

        x, y = self.from_canvas_coords(event.x, event.y)

        if getattr(self, "moving_origin", False):
            # Перемещаем origin только для последнего выделенного
            obj, _ = self.selected_objects[-1]
            if event.state & 0x20000:  # Alt
                obj["origin"] = [x, y]
            else:
                new_ox, new_oy = self.snap_to_grid(x, y)
                obj["origin"] = [new_ox, new_oy]
            self.draw_all()
            return

        # Групповое перемещение
        # Если drag_offsets_multi короче, чем выделенных, дополняем нулями
        while len(self.drag_offsets_multi) < len(self.selected_objects):
            self.drag_offsets_multi.append((0, 0))
        for idx, (obj, obj_type) in enumerate(self.selected_objects):
            angle = obj.get("angle", 0.0)
            origin = obj.get("origin", obj["pos"])
            dx, dy = self.drag_offsets_multi[idx]
            rotated_pos = (x - dx, y - dy)
            px, py = self.rotate_point_inv(rotated_pos[0], rotated_pos[1], origin[0], origin[1], angle)
            # При угле 0° привязываем к сетке, либо если Alt не зажат и угол кратен 90 (для удобства)
            if not (hasattr(event, 'state') and event.state & 0x20000):
                if abs(angle) % 360 == 0:
                    px, py = self.snap_to_grid(px, py)
            old_pos = obj["pos"]
            obj["pos"] = [px, py]
            # смещаем origin только если угол == 0° (без поворота)
            if abs(angle) % 360 == 0 and obj_type in ("walls", "doors", "iventAreas"):
                dx_move = px - old_pos[0]
                dy_move = py - old_pos[1]
                obj["origin"] = [origin[0] + dx_move, origin[1] + dy_move]
        self.update_params_ui()
        self.draw_all()

    def on_release(self, event):
        # Завершить выделение рамкой
        if self.select_box_rect is not None:
            self.canvas.delete(self.select_box_rect)
            self.select_box_rect = None
            self.select_box_start = None
        # Завершить drag группы
        if self.is_group_drag:
            self.is_group_drag = False
            self.canvas.config(cursor="arrow")
        self.moving_origin = False
        self.moving_spawn_angle = False

    def on_right_click(self, event):
        x, y = self.from_canvas_coords(event.x, event.y)

        # Удаляем объект под курсором, если есть
        for obj_type in reversed(list(self.objects.keys())):
            for obj in reversed(self.objects[obj_type]):
                scale = obj.get("scale", 1.0)
                angle = obj.get("angle", 0.0)
                origin = obj.get("origin", obj["pos"])
                pos = obj["pos"]
                # вычисляем rotated_pos
                rotated_pos = self.rotate_point(pos[0], pos[1], origin[0], origin[1], angle)

                if obj_type == "walls":
                    w = obj["width"] * scale
                    h = obj["height"] * scale
                    if self.point_in_rotated_rect(x, y, rotated_pos[0], rotated_pos[1], w, h, angle, pivot="center"):
                        self.objects[obj_type].remove(obj)
                        if any(obj is o for o, _ in self.selected_objects):
                            self.selected_objects = [item for item in self.selected_objects if item[0] is not obj]
                        self.draw_all()
                        return

                elif obj_type == "doors":
                    w = DOOR_BASE_WIDTH * scale
                    h = DOOR_BASE_HEIGHT * scale
                    if self.point_in_rotated_rect(x, y, rotated_pos[0], rotated_pos[1], w, h, angle, pivot="center"):
                        self.objects[obj_type].remove(obj)
                        if any(obj is o for o, _ in self.selected_objects):
                            self.selected_objects = [item for item in self.selected_objects if item[0] is not obj]
                        self.draw_all()
                        return

                elif obj_type == "iventAreas":
                    w = obj["width"] * scale
                    h = obj["height"] * scale
                    if self.point_in_rotated_rect(x, y, rotated_pos[0], rotated_pos[1], w, h, angle, pivot="center"):
                        self.objects[obj_type].remove(obj)
                        if any(obj is o for o, _ in self.selected_objects):
                            self.selected_objects = [item for item in self.selected_objects if item[0] is not obj]
                        self.draw_all()
                        return
                elif obj_type == "enemies":
                    r = ENEMY_RADIUS
                    if (x - pos[0]) ** 2 + (y - pos[1]) ** 2 <= r ** 2:
                        self.objects[obj_type].remove(obj)
                        if any(obj is o for o, _ in self.selected_objects):
                            self.selected_objects = [item for item in self.selected_objects if item[0] is not obj]
                        self.draw_all()
                        return
                elif obj_type == "playerSpawns":
                    r = PLAYERSPAWNS_RADIUS
                    if (x - pos[0]) ** 2 + (y - pos[1]) ** 2 <= r ** 2:
                        self.objects[obj_type].remove(obj)
                        if any(obj is o for o, _ in self.selected_objects):
                            self.selected_objects = [item for item in self.selected_objects if item[0] is not obj]
                        self.draw_all()
                        return

    def on_mousewheel(self, event):
        # Zoom centered on cursor
        factor = 1.1 if event.delta > 0 else 0.9

        # Limit zoom
        new_zoom = self.zoom * factor
        if not (0.05 <= new_zoom <= 5):
            return

        mouse_x, mouse_y = event.x, event.y
        world_x, world_y = self.from_canvas_coords(mouse_x, mouse_y)

        self.zoom = new_zoom

        new_canvas_x, new_canvas_y = self.to_canvas_coords(world_x, world_y)
        self.offset_x += mouse_x - new_canvas_x
        self.offset_y += mouse_y - new_canvas_y

        self.draw_all()

    def on_pan_start(self, event):
        self.panning = True
        self.pan_start = (event.x, event.y)

    def on_pan_move(self, event):
        if not self.panning:
            return
        dx = event.x - self.pan_start[0]
        dy = event.y - self.pan_start[1]
        self.offset_x += dx
        self.offset_y += dy
        self.pan_start = (event.x, event.y)
        self.draw_all()

    def on_pan_end(self, event):
        self.panning = False

    def save_json(self):
        filename = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        if not filename:
            return

        # Подготавливаем списки объектов с позицией центра
        walls_data = []
        for obj in self.objects["walls"]:
            pos = obj["pos"]
            origin = obj.get("origin", pos)
            rel_origin = [origin[0] - pos[0], origin[1] - pos[1]]
            walls_data.append({
                "pos": pos,
                "width": obj["width"],
                "height": obj["height"],
                "scale": obj.get("scale", 1.0),
                "angle": obj.get("angle", 0.0),
                "origin": rel_origin
            })

        doors_data = []
        for obj in self.objects["doors"]:
            pos = obj["pos"]
            origin = obj.get("origin", pos)
            rel_origin = [origin[0] - pos[0], origin[1] - pos[1]]
            doors_data.append({
                "pos": pos,
                "scale": obj.get("scale", 1.0),
                "angle": obj.get("angle", 0.0),
                "origin": rel_origin
            })

        ivents_data = []
        for obj in self.objects["iventAreas"]:
            pos = obj["pos"]
            origin = obj.get("origin", pos)
            rel_origin = [origin[0] - pos[0], origin[1] - pos[1]]
            ivents_data.append({
                "pos": pos,
                "width": obj["width"],
                "height": obj["height"],
                "scale": obj.get("scale", 1.0),
                "id": obj.get("id", 0),
                "angle": obj.get("angle", 0.0),
                "origin": rel_origin
            })

        enemies_data = []
        for obj in self.objects["enemies"]:
            enemies_data.append({
                "pos": obj["pos"],
                "id": obj.get("id", 0)
            })

        player_spawn_data = []
        for obj in self.objects["playerSpawns"]:
            player_spawn_data.append({
                "pos": obj["pos"]
            })

        data = {
            "walls": walls_data,
            "doors": doors_data,
            "iventAreas": ivents_data,
            "enemies": enemies_data,
            "playerSpawns": player_spawn_data,
        }

        with open(filename, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=4)

        tk.messagebox.showinfo("Сохранено", f"Файл сохранен: {filename}")

        self.raster_bg = None
        self.raster_bg_cache = {'zoom': None, 'offset_x': None, 'offset_y': None, 'size': (None, None), 'objects_hash': None}

    def load_json(self):
        from tkinter import filedialog
        filename = filedialog.askopenfilename(
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        if not filename:
            return

        with open(filename, "r", encoding="utf-8") as f:
            data = json.load(f)

        self.objects = {"walls": [], "doors": [], "iventAreas": [], "enemies": [], "playerSpawns": []}
        for obj in data.get("walls", []):
            pos = obj["pos"]
            rel_origin = obj.get("origin", [0, 0])
            origin = [pos[0] + rel_origin[0], pos[1] + rel_origin[1]]
            self.objects["walls"].append({
                "pos": pos,
                "width": obj["width"],
                "height": obj["height"],
                "scale": obj.get("scale", 1.0),
                "angle": obj.get("angle", 0.0),
                "origin": origin
            })
        for obj in data.get("doors", []):
            pos = obj["pos"]
            rel_origin = obj.get("origin", [0, 0])
            origin = [pos[0] + rel_origin[0], pos[1] + rel_origin[1]]
            self.objects["doors"].append({
                "pos": pos,
                "scale": obj.get("scale", 1.0),
                "angle": obj.get("angle", 0.0),
                "origin": origin
            })
        for obj in data.get("iventAreas", []):
            pos = obj["pos"]
            rel_origin = obj.get("origin", [0, 0])
            origin = [pos[0] + rel_origin[0], pos[1] + rel_origin[1]]
            self.objects["iventAreas"].append({
                "pos": pos,
                "width": obj["width"],
                "height": obj["height"],
                "scale": obj.get("scale", 1.0),
                "id": obj.get("id", 0),
                "angle": obj.get("angle", 0.0),
                "origin": origin
            })

        for obj in data.get("enemies", []):
            self.objects["enemies"].append({
                "pos": obj["pos"],
                "id": obj.get("id", 0),
                "origin": obj["pos"]
            })

        for obj in data.get("playerSpawns", []):
            self.objects["playerSpawns"].append({
                "pos": obj["pos"]
            })

        self.selected_objects = []
        self.update_params_ui()
        self.draw_all()

        self.raster_bg = None
        self.raster_bg_cache = {'zoom': None, 'offset_x': None, 'offset_y': None, 'size': (None, None), 'objects_hash': None}

    def on_arrow_key(self, direction, event):
        if not self.selected_objects:
            return
        dx, dy = 0, 0
        if direction == 'up':
            dy = -1
        elif direction == 'down':
            dy = 1
        elif direction == 'left':
            dx = -1
        elif direction == 'right':
            dx = 1
        for obj, _ in self.selected_objects:
            obj["pos"] = [obj["pos"][0] + dx, obj["pos"][1] + dy]
        self.update_params_ui()
        self.draw_all()

    def on_resize(self, event):
        global CANVAS_WIDTH, CANVAS_HEIGHT
        CANVAS_WIDTH = event.width
        CANVAS_HEIGHT = event.height
        self.raster_bg = None
        self.raster_bg_cache = {'zoom': None, 'offset_x': None, 'offset_y': None, 'size': (None, None), 'objects_hash': None}
        self.draw_all()

    def clear_selection(self):
        self.selected_objects = []
        self.update_params_ui()
        self.draw_all()
        self.is_group_drag = False
        self.canvas.config(cursor="arrow")

    # ---------------- Генерация уровня: диалог параметров -----------------
    def ask_generation_params(self):
        """Показывает единое окно для ввода параметров автогенерации.
        Возвращает словарь или None при отмене."""
        dlg = tk.Toplevel(self)
        dlg.title("Параметры генерации уровня")
        dlg.transient(self)
        dlg.grab_set()

        # Центрируем
        dlg.update_idletasks()
        x = self.winfo_rootx() + self.winfo_width() // 2 - dlg.winfo_reqwidth() // 2
        y = self.winfo_rooty() + self.winfo_height() // 2 - dlg.winfo_reqheight() // 2
        dlg.geometry(f"+{x}+{y}")

        rooms_var = tk.IntVar(value=10)
        scale_var = tk.IntVar(value=5)
        corridor_var = tk.IntVar(value=6)

        ttk.Label(dlg, text="Количество комнат (2-200):").grid(row=0, column=0, sticky="w", padx=10, pady=5)
        rooms_entry = ttk.Spinbox(dlg, from_=2, to=200, textvariable=rooms_var, width=10)
        rooms_entry.grid(row=0, column=1, padx=10, pady=5)

        ttk.Label(dlg, text="Множитель размера комнат (1-10):").grid(row=1, column=0, sticky="w", padx=10, pady=5)
        scale_entry = ttk.Spinbox(dlg, from_=1, to=10, textvariable=scale_var, width=10)
        scale_entry.grid(row=1, column=1, padx=10, pady=5)

        ttk.Label(dlg, text="Ширина коридора (2-20):").grid(row=2, column=0, sticky="w", padx=10, pady=5)
        corridor_entry = ttk.Spinbox(dlg, from_=2, to=20, textvariable=corridor_var, width=10)
        corridor_entry.grid(row=2, column=1, padx=10, pady=5)

        result = {}

        def on_ok():
            try:
                rooms = int(rooms_var.get())
                scale = int(scale_var.get())
                corridor = int(corridor_var.get())
            except ValueError:
                tk.messagebox.showerror("Ошибка", "Введите корректные числовые значения.", parent=dlg)
                return
            if not (2 <= rooms <= 200 and 1 <= scale <= 10 and 2 <= corridor <= 20):
                tk.messagebox.showerror("Ошибка", "Значения вне допустимого диапазона.", parent=dlg)
                return
            result.update({"rooms": rooms, "scale": scale, "corridor": corridor})
            dlg.destroy()

        def on_cancel():
            dlg.destroy()

        btn_frame = ttk.Frame(dlg)
        btn_frame.grid(row=3, column=0, columnspan=2, pady=10)
        ttk.Button(btn_frame, text="OK", command=on_ok).pack(side="left", padx=5)
        ttk.Button(btn_frame, text="Отмена", command=on_cancel).pack(side="left", padx=5)

        dlg.wait_window()
        return result if result else None

    def generate_level(self):
        import random, itertools, tkinter.messagebox as messagebox

        params = self.ask_generation_params()
        if not params:
            return  # пользователь отменил

        num_rooms = params["rooms"]
        room_scale = params["scale"]
        corridor_width_input = params["corridor"]

        global SCALE
        SCALE = room_scale  # переопределяем глобальный масштаб для этой генерации

        GRID = GRID_SIZE
        W, H = CANVAS_WIDTH // GRID, CANVAS_HEIGHT // GRID
        corridor_width = corridor_width_input  # в клетках, как ввёл пользователь
        door_width = 6  # 192 px (6 клеток) – оставляем проёмы фиксированного размера
        for attempt in range(100):  # больше попыток генерации перед ошибкой
            self.objects = {"walls": [], "doors": [], "iventAreas": [], "enemies": [], "playerSpawns": []}
            self.selected_objects = []
            margin = 2 * SCALE
            rooms = []
            tries = 0
            occupied = set()
            # 1. --- размещаем комнаты по сетке с небольшой случайностью ---
            max_possible = min(W, H) - 2*margin
            # Размеры комнат
            min_size = max(4, min(32, max_possible // max(2, num_rooms))) * SCALE
            max_size = max(6, min(48, max_possible // max(1, num_rooms//3))) * SCALE

            # Разбиваем поле на крупные ячейки, учитывая минимальный размер комнат
            grid_size = int(math.sqrt(num_rooms)) + 1
            # Делаем ячейки достаточно большими для минимальной комнаты + отступы
            cell_w = max((W*SCALE - 2*margin) // grid_size, min_size + 2*margin)
            cell_h = max((H*SCALE - 2*margin) // grid_size, min_size + 2*margin)

            rooms = []
            occupied = set()
            # Создаем сетку ячеек с учетом размера поля
            max_cols = (W*SCALE - 2*margin) // cell_w
            max_rows = (H*SCALE - 2*margin) // cell_h
            cells = [(i, j) for i in range(min(grid_size, max_cols)) 
                          for j in range(min(grid_size, max_rows))]
            random.shuffle(cells)  # перемешиваем порядок ячеек

            # Пытаемся разместить комнату в каждой ячейке
            for i, j in cells:
                if len(rooms) >= num_rooms:
                    break
                
                # Базовая позиция в ячейке
                base_x = margin + i * cell_w
                base_y = margin + j * cell_h
                
                # Определяем максимальные размеры для этой ячейки
                max_w = min(max_size, cell_w - margin)
                max_h = min(max_size, cell_h - margin)
                
                if max_w > min_size and max_h > min_size:  # проверяем, что есть место для комнаты
                    # Пробуем несколько раз разместить комнату в ячейке
                    for _ in range(5):
                        w = random.randint(min_size, max_w)
                        h = random.randint(min_size, max_h)
                        
                        # Случайное смещение внутри ячейки
                        max_offset_x = cell_w - w - margin
                        max_offset_y = cell_h - h - margin
                        
                        if max_offset_x >= 0 and max_offset_y >= 0:
                            offset_x = random.randint(0, max_offset_x)
                            offset_y = random.randint(0, max_offset_y)
                            
                            x = base_x + offset_x
                            y = base_y + offset_y
                    
                    # Проверяем, не выходит ли за границы и не пересекается ли
                    if (x + w <= W*SCALE - margin and y + h <= H*SCALE - margin):
                        rect = {(xx,yy) for xx in range(x,x+w) for yy in range(y,y+h)}
                        if rect.isdisjoint(occupied):
                            rooms.append({"x":x, "y":y, "w":w, "h":h})
                            occupied |= rect
                            break

            # Если не хватает комнат - добавляем случайным образом
            tries = 0
            while len(rooms) < num_rooms and tries < 1000:
                tries += 1
                w = random.randint(min_size, max_size)
                h = random.randint(min_size, max_size)
                x = random.randint(margin, W*SCALE - w - margin)
                y = random.randint(margin, H*SCALE - h - margin)
                rect = {(xx,yy) for xx in range(x,x+w) for yy in range(y,y+h)}
                if rect.isdisjoint(occupied):
                    rooms.append({"x":x, "y":y, "w":w, "h":h})
                    occupied |= rect

            if len(rooms) < num_rooms:
                continue  # не удалось – пробуем заново

            # 2. Генерируем коридоры (MST + доп. связи)
            centers = [(r["x"] + r["w"] // 2, r["y"] + r["h"] // 2) for r in rooms]
            edges = []
            used = set([0])
            left = set(range(1, num_rooms))
            while left:
                min_dist = float('inf')
                min_pair = None
                for i in used:
                    for j in left:
                        d = abs(centers[i][0] - centers[j][0]) + abs(centers[i][1] - centers[j][1])
                        if d < min_dist:
                            min_dist = d
                            min_pair = (i, j)
                edges.append(min_pair)
                used.add(min_pair[1])
                left.remove(min_pair[1])
            all_pairs = list(itertools.combinations(range(num_rooms), 2))
            random.shuffle(all_pairs)
            extra = max(1, num_rooms // 5)
            added = 0
            for i, j in all_pairs:
                if (i, j) not in edges and (j, i) not in edges and i != j:
                    edges.append((i, j))
                    added += 1
                    if added >= extra:
                        break

            corridor_cells = set()
            for i, j in edges:
                x1, y1 = centers[i]
                x2, y2 = centers[j]
                # L-образный коридор шириной corridor_width
                if random.choice([True, False]):
                    # Горизонтальный, потом вертикальный
                    for xx in range(min(x1, x2), max(x1, x2) + 1):
                        for dy in range(-(corridor_width // 2), corridor_width // 2 + 1):
                            corridor_cells.add((xx, y1 + dy))
                    for yy in range(min(y1, y2), max(y1, y2) + 1):
                        for dx in range(-(corridor_width // 2), corridor_width // 2 + 1):
                            corridor_cells.add((x2 + dx, yy))
                else:
                    # Вертикальный, потом горизонтальный
                    for yy in range(min(y1, y2), max(y1, y2) + 1):
                        for dx in range(-(corridor_width // 2), corridor_width // 2 + 1):
                            corridor_cells.add((x1 + dx, yy))
                    for xx in range(min(x1, x2), max(x1, x2) + 1):
                        for dy in range(-(corridor_width // 2), corridor_width // 2 + 1):
                            corridor_cells.add((xx, y2 + dy))

            # 3. Собираем карту занятости
            area = set()
            for r in rooms:
                area.update((xx, yy) for xx in range(r["x"], r["x"] + r["w"]) for yy in range(r["y"], r["y"] + r["h"]))
            area.update(corridor_cells)

            # 4. Строим стены по периметру area
            walls = set()
            for (x, y) in area:
                for dx, dy in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    nx, ny = x + dx, y + dy
                    if (nx, ny) not in area:
                        # Стена по границе между (x, y) и (nx, ny)
                        if dx != 0:
                            # Вертикальная стена
                            wx = x + (dx + 1) // 2
                            wy = y
                            walls.add((wx, wy, 'v'))
                        else:
                            # Горизонтальная стена
                            wx = x
                            wy = y + (dy + 1) // 2
                            walls.add((wx, wy, 'h'))

            # 5. Двери: в местах соединения комнат и коридоров
            door_objs = []
            door_gaps = set()
            for (x, y) in corridor_cells:
                for dx, dy in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    nx, ny = x + dx, y + dy
                    if (nx, ny) in area and ((x, y) in occupied or (nx, ny) in occupied):
                        if dx != 0:
                            wx = x + (dx + 1) // 2
                            wy = y
                            # Центр двери
                            if (wx, wy, 'v') not in door_gaps:
                                door_gaps.add((wx, wy, 'v'))
                                door_objs.append({
                                    "pos": [wx * GRID, wy * GRID],
                                    "scale": door_width,
                                    "angle": 0.0,
                                    "origin": [wx * GRID, wy * GRID],
                                    "vertical": True
                                })
                        else:
                            wx = x
                            wy = y + (dy + 1) // 2
                            if (wx, wy, 'h') not in door_gaps:
                                door_gaps.add((wx, wy, 'h'))
                                door_objs.append({
                                    "pos": [wx * GRID, wy * GRID],
                                    "scale": door_width,
                                    "angle": 0.0,
                                    "origin": [wx * GRID, wy * GRID],
                                    "vertical": False
                                })

            # 6. Добавляем стены и двери в self.objects (разбиваем стены под проёмы)
            # Группируем стены в длинные сегменты
            from collections import defaultdict
            wall_segments = defaultdict(list)
            for wx, wy, orient in walls:
                wall_segments[(orient, wy if orient == 'h' else wx)].append((wx, wy))
            for key, segs in wall_segments.items():
                orient, const = key
                segs = sorted(segs)
                # Группируем подряд идущие клетки в сегменты
                curr = []
                for s in segs:
                    if not curr:
                        curr = [s]
                    else:
                        prev = curr[-1]
                        if orient == 'h' and s[0] == prev[0] + 1 and s[1] == prev[1]:
                            curr.append(s)
                        elif orient == 'v' and s[1] == prev[1] + 1 and s[0] == prev[0]:
                            curr.append(s)
                        else:
                            # Обрабатываем сегмент
                            x0, y0 = curr[0]
                            x1, y1 = curr[-1]
                            # Центр и длина сегмента
                            if orient == 'h':
                                seg_start = x0 * GRID
                                seg_end = (x1 + 1) * GRID
                                seg_len = seg_end - seg_start
                                seg_y = y0 * GRID
                                # Ищем дверь, которая помещается
                                door = None
                                for d in door_objs:
                                    if not d["vertical"] and d["pos"][1] == seg_y and seg_start + door_width * GRID // 2 < d["pos"][0] < seg_end - door_width * GRID // 2:
                                        door = d
                                        break
                                if door and seg_len > door_width * GRID:
                                    # Левая часть стены
                                    left_len = door["pos"][0] - door_width * GRID // 2 - seg_start
                                    if left_len > 0:
                                        self.objects["walls"].append({
                                            "pos": [seg_start + left_len // 2, seg_y],
                                            "width": left_len,
                                            "height": GRID,
                                            "scale": 1.0,
                                            "angle": 0.0,
                                            "origin": [seg_start + left_len // 2, seg_y]
                                        })
                                    # Правая часть стены
                                    right_start = door["pos"][0] + door_width * GRID // 2
                                    right_len = seg_end - right_start
                                    if right_len > 0:
                                        self.objects["walls"].append({
                                            "pos": [right_start + right_len // 2, seg_y],
                                            "width": right_len,
                                            "height": GRID,
                                            "scale": 1.0,
                                            "angle": 0.0,
                                            "origin": [right_start + right_len // 2, seg_y]
                                        })
                                    # Дверь
                                    self.objects["doors"].append({
                                        "pos": [door["pos"][0], seg_y],
                                        "scale": door_width,
                                        "angle": 90.0,
                                        "origin": [door["pos"][0], seg_y]
                                    })
                                else:
                                    # Нет двери или не помещается — вся стена
                                    pad = GRID  # удлиняем слева и справа на 1 клетку
                                    new_start = seg_start - pad
                                    new_end   = seg_end   + pad
                                    self.objects["walls"].append({
                                        "pos": [(new_start + new_end) // 2, seg_y],
                                        "width": new_end - new_start,
                                        "height": GRID,
                                        "scale": 1.0,
                                        "angle": 0.0
                                    })
                            else:
                                seg_start = y0 * GRID
                                seg_end = (y1 + 1) * GRID
                                seg_len = seg_end - seg_start
                                seg_x = x0 * GRID
                                door = None
                                for d in door_objs:
                                    if d["vertical"] and d["pos"][0] == seg_x and seg_start + door_width * GRID // 2 < d["pos"][1] < seg_end - door_width * GRID // 2:
                                        door = d
                                        break
                                if door and seg_len > door_width * GRID:
                                    # Верхняя часть стены
                                    top_len = door["pos"][1] - door_width * GRID // 2 - seg_start
                                    if top_len > 0:
                                        self.objects["walls"].append({
                                            "pos": [seg_x, seg_start + top_len // 2],
                                            "width": GRID,
                                            "height": top_len,
                                            "scale": 1.0,
                                            "angle": 0.0,
                                            "origin": [seg_x, seg_start + top_len // 2]
                                        })
                                    # Нижняя часть стены
                                    bottom_start = door["pos"][1] + door_width * GRID // 2
                                    bottom_len = seg_end - bottom_start
                                    if bottom_len > 0:
                                        self.objects["walls"].append({
                                            "pos": [seg_x, bottom_start + bottom_len // 2],
                                            "width": GRID,
                                            "height": bottom_len,
                                            "scale": 1.0,
                                            "angle": 0.0,
                                            "origin": [seg_x, bottom_start + bottom_len // 2]
                                        })
                                    # Дверь
                                    self.objects["doors"].append({
                                        "pos": [seg_x, door["pos"][1]],
                                        "scale": door_width,
                                        "angle": 0.0,
                                        "origin": [seg_x, door["pos"][1]]
                                    })
                                else:
                                    # Нет двери или не помещается — вся стена
                                    pad = GRID  # удлиняем вверх и вниз на 1 клетку
                                    new_start = seg_start - pad
                                    new_end   = seg_end   + pad
                                    self.objects["walls"].append({
                                        "pos": [seg_x, (new_start + new_end) // 2],
                                        "width": GRID,
                                        "height": new_end - new_start,
                                        "scale": 1.0,
                                        "angle": 0.0
                                    })
                            curr = []
                # Последний сегмент
                if curr:
                    x0, y0 = curr[0]
                    x1, y1 = curr[-1]
                    if orient == 'h':
                        seg_start = x0 * GRID
                        seg_end = (x1 + 1) * GRID
                        seg_len = seg_end - seg_start
                        seg_y = y0 * GRID
                        door = None
                        for d in door_objs:
                            if not d["vertical"] and d["pos"][1] == seg_y and seg_start + door_width * GRID // 2 < d["pos"][0] < seg_end - door_width * GRID // 2:
                                door = d
                                break
                        if door and seg_len > door_width * GRID:
                            left_len = door["pos"][0] - door_width * GRID // 2 - seg_start
                            if left_len > 0:
                                self.objects["walls"].append({
                                    "pos": [seg_start + left_len // 2, seg_y],
                                    "width": left_len,
                                    "height": GRID,
                                    "scale": 1.0,
                                    "angle": 0.0,
                                    "origin": [seg_start + left_len // 2, seg_y]
                                })
                            right_start = door["pos"][0] + door_width * GRID // 2
                            right_len = seg_end - right_start
                            if right_len > 0:
                                self.objects["walls"].append({
                                    "pos": [right_start + right_len // 2, seg_y],
                                    "width": right_len,
                                    "height": GRID,
                                    "scale": 1.0,
                                    "angle": 0.0,
                                    "origin": [right_start + right_len // 2, seg_y]
                                })
                            self.objects["doors"].append({
                                "pos": [door["pos"][0], seg_y],
                                "scale": door_width,
                                "angle": 90.0,
                                "origin": [door["pos"][0], seg_y]
                            })
                        else:
                            pad = GRID  # удлиняем слева и справа на 1 клетку
                            new_start = seg_start - pad
                            new_end   = seg_end   + pad
                            self.objects["walls"].append({
                                "pos": [(new_start + new_end) // 2, seg_y],
                                "width": new_end - new_start,
                                "height": GRID,
                                "scale": 1.0,
                                "angle": 0.0
                            })
                    else:
                        seg_start = y0 * GRID
                        seg_end = (y1 + 1) * GRID
                        seg_len = seg_end - seg_start
                        seg_x = x0 * GRID
                        door = None
                        for d in door_objs:
                            if d["vertical"] and d["pos"][0] == seg_x and seg_start + door_width * GRID // 2 < d["pos"][1] < seg_end - door_width * GRID // 2:
                                door = d
                                break
                        if door and seg_len > door_width * GRID:
                            top_len = door["pos"][1] - door_width * GRID // 2 - seg_start
                            if top_len > 0:
                                self.objects["walls"].append({
                                    "pos": [seg_x, seg_start + top_len // 2],
                                    "width": GRID,
                                    "height": top_len,
                                    "scale": 1.0,
                                    "angle": 0.0,
                                    "origin": [seg_x, seg_start + top_len // 2]
                                })
                            bottom_start = door["pos"][1] + door_width * GRID // 2
                            bottom_len = seg_end - bottom_start
                            if bottom_len > 0:
                                self.objects["walls"].append({
                                    "pos": [seg_x, bottom_start + bottom_len // 2],
                                    "width": GRID,
                                    "height": bottom_len,
                                    "scale": 1.0,
                                    "angle": 0.0,
                                    "origin": [seg_x, bottom_start + bottom_len // 2]
                                })
                            self.objects["doors"].append({
                                "pos": [seg_x, door["pos"][1]],
                                "scale": door_width,
                                "angle": 0.0,
                                "origin": [seg_x, door["pos"][1]]
                            })
                        else:
                            pad = GRID  # удлиняем вверх и вниз на 1 клетку
                            new_start = seg_start - pad
                            new_end   = seg_end   + pad
                            self.objects["walls"].append({
                                "pos": [seg_x, (new_start + new_end) // 2],
                                "width": GRID,
                                "height": new_end - new_start,
                                "scale": 1.0,
                                "angle": 0.0
                            })

            # --- 6+. Формируем непрерывные стены без щелей ------------------------
            h_by_y = defaultdict(list)
            v_by_x = defaultdict(list)
            for wx, wy, orient in walls:
                if orient == 'h':
                    h_by_y[wy].append(wx)
                else:
                    v_by_x[wx].append(wy)

            self.objects["walls"].clear()

            # горизонтальные
            for y, xs in h_by_y.items():
                xs.sort()
                start = xs[0]
                prev = xs[0]
                for x in xs[1:]:
                    if x == prev + 1:          # соседняя клетка
                        prev = x
                    else:                      # разрыв – закрываем сегмент
                        seg_len = (prev - start + 1) * GRID
                        cx = (start + prev + 1) * GRID // 2
                        self.objects["walls"].append(
                            {"pos": [cx, y * GRID],
                             "width": seg_len,
                             "height": GRID,
                             "scale": 1.0,
                             "angle": 0.0})
                        start = prev = x
                # последний сегмент строки
                seg_len = (prev - start + 1) * GRID
                cx = (start + prev + 1) * GRID // 2
                self.objects["walls"].append(
                    {"pos": [cx, y * GRID],
                     "width": seg_len,
                     "height": GRID,
                     "scale": 1.0,
                     "angle": 0.0})

            # вертикальные
            for x, ys in v_by_x.items():
                ys.sort()
                start = ys[0]
                prev = ys[0]
                for y in ys[1:]:
                    if y == prev + 1:
                        prev = y
                    else:
                        seg_len = (prev - start + 1) * GRID
                        cy = (start + prev + 1) * GRID // 2
                        self.objects["walls"].append(
                            {"pos": [x * GRID, cy],
                             "width": GRID,
                             "height": seg_len,
                             "scale": 1.0,
                             "angle": 0.0})
                        start = prev = y
                seg_len = (prev - start + 1) * GRID
                cy = (start + prev + 1) * GRID // 2
                self.objects["walls"].append(
                    {"pos": [x * GRID, cy],
                     "width": GRID,
                     "height": seg_len,
                     "scale": 1.0,
                     "angle": 0.0})

            self.update_params_ui()
            self.draw_all()
            return
        # Если не удалось разместить комнаты за 30 попыток
        messagebox.showerror("Ошибка генерации", "Не удалось разместить комнаты. Попробуйте уменьшить количество комнат или увеличить размер карты.")

    # Перемещение стрелки playerSpawns
    def on_drag_spawn_angle(self, event):
        if not self.selected_objects:
            return
        obj, obj_type_sel = self.selected_objects[-1]
        if obj_type_sel != "playerSpawns":
            return
        # вычисляем новый угол
        spawn_x, spawn_y = obj["pos"]
        mx, my = self.from_canvas_coords(event.x, event.y)
        import math
        new_angle = math.degrees(math.atan2(my - spawn_y, mx - spawn_x))
        obj["angle"] = new_angle % 360
        self.draw_all()
        return

    def on_ctrl_c(self, event=None):
        # Копируем выделенные объекты в буфер
        if not self.selected_objects:
            return
        self.clipboard_objects = []
        for obj, obj_type in self.selected_objects:
            # Копируем только поддерживаемые типы
            if obj_type in ("walls", "doors", "iventAreas", "enemies", "playerSpawns"):
                self.clipboard_objects.append((copy.deepcopy(obj), obj_type))

    def on_ctrl_v(self, event=None):
        # Вставляем объекты из буфера
        if not self.clipboard_objects:
            return
        new_objs = []
        offset = 32  # смещение при вставке
        for obj, obj_type in self.clipboard_objects:
            new_obj = copy.deepcopy(obj)
            # Смещаем позицию
            if "pos" in new_obj:
                new_obj["pos"] = [new_obj["pos"][0] + offset, new_obj["pos"][1] + offset]
            if "origin" in new_obj:
                new_obj["origin"] = [new_obj["origin"][0] + offset, new_obj["origin"][1] + offset]
            self.objects[obj_type].append(new_obj)
            new_objs.append((new_obj, obj_type))
        self.selected_objects = new_objs
        self.update_params_ui()
        self.draw_all()

def merge_walls(walls):
    horiz = [w for w in walls if w["width"] >= w["height"]]   # горизонтальные
    vert  = [w for w in walls if w["height"] >  w["width"]]   # вертикальные

    def merge(line, horizontal):
        # координаты начала/конца в КЛЕТКАХ
        for w in line:
            if horizontal:
                w["y"]   = w["pos"][1]               // GRID_SIZE
                w["x0"]  = (w["pos"][0] - w["width"]//2) // GRID_SIZE
                w["x1"]  = (w["pos"][0] + w["width"]//2) // GRID_SIZE
            else:
                w["x"]   = w["pos"][0]               // GRID_SIZE
                w["y0"]  = (w["pos"][1] - w["height"]//2) // GRID_SIZE
                w["y1"]  = (w["pos"][1] + w["height"]//2) // GRID_SIZE

        key = ("y","x0") if horizontal else ("x","y0")
        line.sort(key=lambda w: (w[key[0]], w[key[1]]))

        merged=[]
        for w in line:
            if not merged:
                merged.append(w); continue
            last=merged[-1]
            same_row = w["y"]==last["y"] if horizontal else w["x"]==last["x"]
            touch    = w["x0"]<=last["x1"]+1 if horizontal else w["y0"]<=last["y1"]+1
            if same_row and touch:
                # объединяем
                if horizontal:
                    last["x1"]=max(last["x1"], w["x1"])
                else:
                    last["y1"]=max(last["y1"], w["y1"])
            else:
                merged.append(w)
        # пересчитаем pos/width/height
        out=[]
        for w in merged:
            if horizontal:
                width  = (w["x1"]-w["x0"])*GRID_SIZE
                pos_x  = (w["x0"]+w["x1"])*GRID_SIZE//2
                out.append({"pos":[pos_x, w["y"]*GRID_SIZE],
                            "width":width,"height":GRID_SIZE,"scale":1.0,"angle":0.0})
            else:
                height = (w["y1"]-w["y0"])*GRID_SIZE
                pos_y  = (w["y0"]+w["y1"])*GRID_SIZE//2
                out.append({"pos":[w["x"]*GRID_SIZE, pos_y],
                            "width":GRID_SIZE,"height":height,"scale":1.0,"angle":0.0})
        return out

    return merge(horiz,True)+merge(vert,False)

# ---------------- fast Poisson-disk sampler (sparse grid) -----------------
def poisson_sample(n, width, height, min_d, k=30):
    """Memory-efficient Poisson-disk sampling using sparse hash grid."""
    import math, random
    cell = min_d / math.sqrt(2)
    grid = {}               # (gx,gy) -> index в pts
    pts = []
    active = []

    def add(pt):
        x, y = pt
        grid[int(x / cell), int(y / cell)] = len(pts)
        pts.append(pt)
        active.append(pt)

    add((random.random() * width, random.random() * height))
    while active and len(pts) < n:
        idx = random.randrange(len(active))
        ox, oy = active[idx]
        found = False
        for _ in range(k):
            ang = random.random() * 6.28318530718
            rad = random.uniform(min_d, 2 * min_d)
            nx = ox + math.cos(ang) * rad
            ny = oy + math.sin(ang) * rad
            if not (0 <= nx < width and 0 <= ny < height):
                continue
            gx, gy = int(nx / cell), int(ny / cell)
            ok = True
            for ix in range(gx - 2, gx + 3):
                for iy in range(gy - 2, gy + 3):
                    j = grid.get((ix, iy), -1)
                    if j == -1:
                        continue
                    px, py = pts[j]
                    if (px - nx) ** 2 + (py - ny) ** 2 < min_d * min_d:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                add((nx, ny))
                found = True
                break
        if not found:
            active.pop(idx)
    return pts[:n]

if __name__ == "__main__":
    app = MapEditor()
    app.mainloop()
