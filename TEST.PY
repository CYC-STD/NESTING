#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DXF自動排樣軟體
功能：讀取多個DXF零件，在指定板材上自動排列以最大化材料利用率
支持：零件旋轉、間距設置、板材尺寸設置、多文件載入
注意：每個DXF文件作為一個整體進行排樣
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
import ezdxf
import math
import random
import copy
from dataclasses import dataclass
from typing import List, Tuple, Optional, Dict
import time
import os
from collections import defaultdict


# ==================== 數據結構定義 ====================
@dataclass
class Point:
    """二維點"""
    x: float
    y: float

    def rotate(self, angle_deg: float, center=None) -> 'Point':
        """繞點旋轉（角度制）"""
        if center is None:
            center = Point(0, 0)
        angle_rad = math.radians(angle_deg)
        dx = self.x - center.x
        dy = self.y - center.y
        cos_a = math.cos(angle_rad)
        sin_a = math.sin(angle_rad)
        new_x = dx * cos_a - dy * sin_a + center.x
        new_y = dx * sin_a + dy * cos_a + center.y
        return Point(new_x, new_y)

    def distance(self, other: 'Point') -> float:
        """計算兩點距離"""
        return math.sqrt((self.x - other.x) ** 2 + (self.y - other.y) ** 2)

    def __add__(self, other: 'Point') -> 'Point':
        """點加法"""
        return Point(self.x + other.x, self.y + other.y)

    def __sub__(self, other: 'Point') -> 'Point':
        """點減法"""
        return Point(self.x - other.x, self.y - other.y)

    def __mul__(self, scalar: float) -> 'Point':
        """點乘以標量"""
        return Point(self.x * scalar, self.y * scalar)

    def __truediv__(self, scalar: float) -> 'Point':
        """點除以標量"""
        return Point(self.x / scalar, self.y / scalar)

    def __repr__(self) -> str:
        return f"Point({self.x:.2f}, {self.y:.2f})"


@dataclass
class BoundingBox:
    """軸對齊邊界框"""
    min_x: float
    min_y: float
    max_x: float
    max_y: float

    @property
    def width(self) -> float:
        return self.max_x - self.min_x

    @property
    def height(self) -> float:
        return self.max_y - self.min_y

    @property
    def area(self) -> float:
        return self.width * self.height

    def intersects(self, other: 'BoundingBox', spacing: float = 0) -> bool:
        """檢測兩個邊界框是否相交（帶間距）"""
        return not (self.max_x + spacing < other.min_x - spacing or
                    self.min_x - spacing > other.max_x + spacing or
                    self.max_y + spacing < other.min_y - spacing or
                    self.min_y - spacing > other.max_y + spacing)

    @property
    def center(self) -> Point:
        """邊界框中心點"""
        return Point((self.min_x + self.max_x) / 2, (self.min_y + self.max_y) / 2)

    def __repr__(self) -> str:
        return f"BBox({self.min_x:.1f},{self.min_y:.1f})-({self.max_x:.1f},{self.max_y:.1f})"


@dataclass
class DXFFile:
    """代表整個DXF文件作為一個單元"""
    filename: str
    filepath: str
    polygons: List[List[Point]]  # 文件中的所有多邊形
    angle: float = 0  # 當前旋轉角度
    quantity: int = 1  # 數量
    color: str = ""  # 顯示顏色

    def __post_init__(self):
        # 計算文件的包圍盒
        self.update_bounding_box()

        # 如果沒有指定顏色，隨機生成一個
        if not self.color:
            colors = ["red", "blue", "green", "orange", "purple", "brown",
                      "cyan", "magenta", "pink", "yellow", "lime", "teal"]
            self.color = random.choice(colors)

    def update_bounding_box(self):
        """更新文件的包圍盒"""
        all_points = []
        for polygon in self.polygons:
            all_points.extend(polygon)

        if not all_points:
            self.bbox = BoundingBox(0, 0, 0, 0)
            return

        xs = [p.x for p in all_points]
        ys = [p.y for p in all_points]
        self.bbox = BoundingBox(min(xs), min(ys), max(xs), max(ys))

    def rotate(self, angle_deg: float) -> 'DXFFile':
        """創建旋轉後的DXF文件副本（繞原點旋轉）"""
        if not self.polygons:
            return self.copy()

        # 計算中心點
        center = self.bbox.center

        # 旋轉所有多邊形的所有點
        rotated_polygons = []
        for polygon in self.polygons:
            rotated_polygon = [p.rotate(angle_deg, center) for p in polygon]
            rotated_polygons.append(rotated_polygon)

        new_file = DXFFile(self.filename, self.filepath, rotated_polygons,
                           self.angle + angle_deg, self.quantity, self.color)
        new_file.update_bounding_box()
        return new_file

    def translate(self, dx: float, dy: float) -> 'DXFFile':
        """平移DXF文件"""
        translated_polygons = []
        for polygon in self.polygons:
            translated_polygon = [Point(p.x + dx, p.y + dy) for p in polygon]
            translated_polygons.append(translated_polygon)

        new_file = DXFFile(self.filename, self.filepath, translated_polygons,
                           self.angle, self.quantity, self.color)
        new_file.bbox = BoundingBox(
            self.bbox.min_x + dx, self.bbox.min_y + dy,
            self.bbox.max_x + dx, self.bbox.max_y + dy
        )
        return new_file

    def contains_point(self, point: Point) -> bool:
        """檢測點是否在DXF文件的任何多邊形內（射線法）"""
        for polygon in self.polygons:
            if len(polygon) < 3:
                continue

            inside = False
            x, y = point.x, point.y

            p1 = polygon[0]
            for i in range(1, len(polygon) + 1):
                p2 = polygon[i % len(polygon)]
                if y > min(p1.y, p2.y):
                    if y <= max(p1.y, p2.y):
                        if x <= max(p1.x, p2.x):
                            if p1.y != p2.y:
                                xinters = (y - p1.y) * (p2.x - p1.x) / (p2.y - p1.y) + p1.x
                            if p1.x == p2.x or x <= xinters:
                                inside = not inside
                p1 = p2

            if inside:
                return True

        return False

    def intersects_file(self, other: 'DXFFile', spacing: float = 0) -> bool:
        """檢測兩個DXF文件是否相交（帶間距）"""
        # 快速邊界框檢測
        if not self.bbox.intersects(other.bbox, spacing):
            return False

        # 精確檢測：檢查每個頂點是否在另一個文件的任何多邊形內
        for polygon in self.polygons:
            for point in polygon:
                if other.contains_point(point):
                    return True

        for polygon in other.polygons:
            for point in polygon:
                if self.contains_point(point):
                    return True

        return True  # 如果邊界框相交，保守返回True

    def copy(self) -> 'DXFFile':
        """創建DXF文件的深拷貝"""
        copied_polygons = []
        for polygon in self.polygons:
            copied_polygon = [Point(p.x, p.y) for p in polygon]
            copied_polygons.append(copied_polygon)

        new_file = DXFFile(self.filename, self.filepath, copied_polygons,
                           self.angle, self.quantity, self.color)
        new_file.bbox = BoundingBox(
            self.bbox.min_x, self.bbox.min_y,
            self.bbox.max_x, self.bbox.max_y
        )
        return new_file

    def get_display_name(self) -> str:
        """獲取顯示名稱（去掉路徑和擴展名）"""
        return os.path.splitext(os.path.basename(self.filename))[0]

    def __repr__(self) -> str:
        return f"DXFFile('{self.get_display_name()}', {len(self.polygons)} polygons, bbox={self.bbox}, qty={self.quantity})"


@dataclass
class Board:
    """板材類"""
    width: float
    height: float
    placed_files: List[DXFFile] = None

    def __post_init__(self):
        if self.placed_files is None:
            self.placed_files = []

    def can_place_file(self, dxf_file: DXFFile, spacing: float = 0) -> bool:
        """檢測DXF文件是否可以放置在當前位置"""
        # 檢查是否在板材範圍內
        bbox = dxf_file.bbox
        if (bbox.min_x - spacing < 0 or bbox.max_x + spacing > self.width or
                bbox.min_y - spacing < 0 or bbox.max_y + spacing > self.height):
            return False

        # 檢查是否與已放置文件衝突
        for placed_file in self.placed_files:
            if dxf_file.intersects_file(placed_file, spacing):
                return False

        return True

    def place_file(self, dxf_file: DXFFile) -> None:
        """放置DXF文件到板材上"""
        self.placed_files.append(dxf_file)

    @property
    def utilization(self) -> float:
        """計算板材利用率"""
        if not self.placed_files:
            return 0.0

        total_area = sum(f.bbox.area for f in self.placed_files)
        board_area = self.width * self.height
        return (total_area / board_area) * 100.0

    def get_placed_area(self) -> float:
        """計算已放置文件的總面積"""
        return sum(f.bbox.area for f in self.placed_files)

    def get_files_statistics(self) -> Dict[str, Dict]:
        """獲取文件統計信息"""
        stats = defaultdict(lambda: {"count": 0, "area": 0.0})

        for dxf_file in self.placed_files:
            key = dxf_file.get_display_name()
            stats[key]["count"] += 1
            stats[key]["area"] += dxf_file.bbox.area

        return dict(stats)

    def __repr__(self) -> str:
        return f"Board({self.width}x{self.height}, {len(self.placed_files)} files, util={self.utilization:.1f}%)"


# ==================== 排樣算法 ====================
class NestingAlgorithm:
    """排樣算法核心類"""

    def __init__(self, board_width: float, board_height: float,
                 part_spacing: float = 0, max_rotation: float = 180,
                 rotation_step: float = 90):
        self.board = Board(board_width, board_height)
        self.part_spacing = part_spacing
        self.max_rotation = max_rotation
        self.rotation_step = rotation_step

    def find_best_placement(self, dxf_file: DXFFile) -> Optional[Tuple[float, float, float]]:
        """尋找最佳放置位置和角度"""
        best_placement = None
        best_fitness = float('inf')

        # 生成可能的旋轉角度
        rotations = [0]
        if self.max_rotation > 0 and self.rotation_step > 0:
            max_rot = int(self.max_rotation)
            rot_step = int(self.rotation_step)
            for angle in range(rot_step, max_rot + 1, rot_step):
                rotations.append(angle)
                rotations.append(-angle)

        for angle in rotations:
            rotated_file = dxf_file.rotate(angle)
            bbox = rotated_file.bbox

            # 如果文件太大，跳過
            if bbox.width > self.board.width or bbox.height > self.board.height:
                continue

            # 嘗試放置位置
            y_step = max(bbox.height / 3, 10)
            x_step = max(bbox.width / 3, 10)

            max_y = int(self.board.height - bbox.height)
            max_x = int(self.board.width - bbox.width)

            if max_y < 0 or max_x < 0:
                continue

            for y in range(0, max_y + 1, int(y_step)):
                for x in range(0, max_x + 1, int(x_step)):
                    candidate = rotated_file.translate(x, y)

                    if self.board.can_place_file(candidate, self.part_spacing):
                        # 適應度：盡量靠近左下角
                        fitness = y + x * 0.001
                        if fitness < best_fitness:
                            best_fitness = fitness
                            best_placement = (x, y, angle)

        return best_placement

    def nest_files(self, dxf_files: List[DXFFile],
                   sort_by: str = 'area_desc') -> Board:
        """主排樣函數"""
        # 展開所有文件，考慮數量
        expanded_files = []
        for dxf_file in dxf_files:
            for _ in range(dxf_file.quantity):
                expanded_files.append(dxf_file.copy())

        # 根據指定方式排序
        if sort_by == 'area_desc':
            expanded_files.sort(key=lambda f: f.bbox.area, reverse=True)
        elif sort_by == 'width_desc':
            expanded_files.sort(key=lambda f: f.bbox.width, reverse=True)
        elif sort_by == 'height_desc':
            expanded_files.sort(key=lambda f: f.bbox.height, reverse=True)

        placed_count = 0

        for i, dxf_file in enumerate(expanded_files):
            placement = self.find_best_placement(dxf_file)

            if placement:
                x, y, angle = placement
                rotated_file = dxf_file.rotate(angle).translate(x, y)
                self.board.place_file(rotated_file)
                placed_count += 1

        print(f"成功放置 {placed_count}/{len(expanded_files)} 個文件")
        print(f"材料利用率: {self.board.utilization:.2f}%")

        return self.board


# ==================== DXF處理 ====================
class DXFProcessor:
    """處理DXF文件讀取"""

    @staticmethod
    def load_dxf_file(filepath: str) -> DXFFile:
        """從單個DXF文件讀取所有圖形作為一個整體"""
        polygons = []
        try:
            # 檢查文件是否存在
            if not os.path.exists(filepath):
                raise FileNotFoundError(f"文件不存在: {filepath}")

            # 使用ezdxf讀取DXF文件
            doc = ezdxf.readfile(filepath)
            msp = doc.modelspace()

            # 計數器
            entity_count = 0
            polygon_count = 0

            # 處理所有實體
            for entity in msp:
                entity_count += 1
                points = []

                # 處理LWPOLYLINE
                if entity.dxftype() == 'LWPOLYLINE':
                    if entity.closed:
                        for vertex in entity.vertices:
                            x, y = vertex[0], vertex[1]
                            points.append(Point(x, y))

                # 處理POLYLINE
                elif entity.dxftype() == 'POLYLINE':
                    if entity.is_closed:
                        for vertex in entity.vertices:
                            location = vertex.dxf.location
                            points.append(Point(location.x, location.y))

                # 處理LINE（將線段組合）
                elif entity.dxftype() == 'LINE':
                    start = entity.dxf.start
                    end = entity.dxf.end
                    points.append(Point(start.x, start.y))
                    points.append(Point(end.x, end.y))
                    # 對於線段，我們需要至少3個點來形成多邊形，所以添加一個虛擬點
                    if len(points) == 2:
                        points.append(Point((start.x + end.x) / 2, (start.y + end.y) / 2))

                # 處理CIRCLE
                elif entity.dxftype() == 'CIRCLE':
                    center = entity.dxf.center
                    radius = entity.dxf.radius
                    # 將圓近似為24邊形
                    for i in range(24):
                        angle = 2 * math.pi * i / 24
                        x = center.x + radius * math.cos(angle)
                        y = center.y + radius * math.sin(angle)
                        points.append(Point(x, y))

                # 處理ARC
                elif entity.dxftype() == 'ARC':
                    center = entity.dxf.center
                    radius = entity.dxf.radius
                    start_angle = math.radians(entity.dxf.start_angle)
                    end_angle = math.radians(entity.dxf.end_angle)

                    # 確保end_angle大於start_angle
                    if end_angle < start_angle:
                        end_angle += 2 * math.pi

                    # 將圓弧近似為多邊形
                    num_segments = 12
                    for i in range(num_segments + 1):
                        angle = start_angle + (end_angle - start_angle) * i / num_segments
                        x = center.x + radius * math.cos(angle)
                        y = center.y + radius * math.sin(angle)
                        points.append(Point(x, y))

                # 如果有足夠的點，添加到多邊形列表
                if len(points) >= 3:
                    polygon_count += 1

                    # 確保多邊形是閉合的
                    if abs(points[0].x - points[-1].x) > 0.001 or abs(points[0].y - points[-1].y) > 0.001:
                        points.append(Point(points[0].x, points[0].y))

                    # 確保點是順時針方向
                    if not DXFProcessor._is_clockwise(points):
                        points.reverse()

                    polygons.append(points)

            print(f"從 {filepath} 讀取了 {len(polygons)} 個多邊形")

            if len(polygons) == 0:
                print(f"警告：{filepath} 中未找到有效的多邊形")
                # 創建一個空文件
                return DXFFile(filepath, filepath, [], quantity=1)

        except Exception as e:
            print(f"讀取DXF文件 {filepath} 時出錯: {str(e)}")
            import traceback
            traceback.print_exc()
            return DXFFile(filepath, filepath, [], quantity=1)

        return DXFFile(filepath, filepath, polygons, quantity=1)

    @staticmethod
    def load_multiple_dxf_files(filepaths: List[str]) -> List[DXFFile]:
        """從多個DXF文件讀取，每個文件作為一個整體"""
        all_files = []

        for filepath in filepaths:
            dxf_file = DXFProcessor.load_dxf_file(filepath)
            all_files.append(dxf_file)
            print(f"已載入文件 {dxf_file.get_display_name()}: {len(dxf_file.polygons)} 個多邊形")

        print(f"總共載入 {len(all_files)} 個文件")
        return all_files

    @staticmethod
    def _is_clockwise(points: List[Point]) -> bool:
        """判斷多邊形是否順時針"""
        if len(points) < 3:
            return True

        area = 0
        n = len(points)
        for i in range(n):
            x1, y1 = points[i].x, points[i].y
            x2, y2 = points[(i + 1) % n].x, points[(i + 1) % n].y
            area += (x2 - x1) * (y2 + y1)
        return area > 0

    @staticmethod
    def save_nesting_result(board: Board, filepath: str) -> bool:
        """保存排樣結果到DXF文件"""
        try:
            doc = ezdxf.new('R2010')
            msp = doc.modelspace()

            # 添加板材邊界
            msp.add_lwpolyline([
                (0, 0),
                (board.width, 0),
                (board.width, board.height),
                (0, board.height),
                (0, 0)
            ], dxfattribs={'closed': True})

            # 添加所有文件
            for i, dxf_file in enumerate(board.placed_files):
                # 添加文件中的所有多邊形
                for polygon in dxf_file.polygons:
                    points = [(p.x, p.y) for p in polygon]

                    # 創建閉合多段線
                    polyline = msp.add_lwpolyline(points)
                    polyline.dxf.layer = f"{dxf_file.get_display_name()}"

                    # 設置顏色
                    color_map = {
                        "red": 1, "blue": 5, "green": 3, "orange": 30,
                        "purple": 6, "brown": 20, "cyan": 4, "magenta": 6,
                        "pink": 13, "yellow": 2, "lime": 92, "teal": 84
                    }
                    if dxf_file.color in color_map:
                        polyline.dxf.color = color_map[dxf_file.color]
                    else:
                        polyline.dxf.color = i % 7 + 1

                # 添加文件編號標註
                centroid = dxf_file.bbox.center
                bbox = dxf_file.bbox
                text_height = min(bbox.width, bbox.height) * 0.1

                msp.add_text(f"{i + 1}",
                             dxfattribs={
                                 'insert': (centroid.x, centroid.y),
                                 'height': text_height
                             })

            doc.saveas(filepath)
            print(f"排樣結果已保存到: {filepath}")
            return True

        except Exception as e:
            print(f"保存DXF文件時出錯: {str(e)}")
            messagebox.showerror("錯誤", f"保存DXF文件失敗: {str(e)}")
            return False


# ==================== GUI介面 ====================
class NestingApp:
    def __init__(self, root):
        self.root = root
        self.root.title("DXF自動排樣系統 (整體文件排樣)")
        self.root.geometry("1200x800")

        self.dxf_files = []  # 存儲DXFFile對象
        self.current_board = None

        self.setup_ui()

    def setup_ui(self):
        """設置用戶界面"""
        # 主框架
        main_frame = ttk.Frame(self.root, padding="10")
        main_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))

        # 左側控制面板
        control_frame = ttk.LabelFrame(main_frame, text="控制面板", padding="10")
        control_frame.grid(row=0, column=0, sticky=(tk.N, tk.S, tk.W), padx=(0, 10))

        # 板材設置
        ttk.Label(control_frame, text="板材設置", font=("Arial", 10, "bold")).grid(
            row=0, column=0, columnspan=2, pady=(0, 5), sticky=tk.W
        )

        ttk.Label(control_frame, text="寬度 (mm):").grid(row=1, column=0, sticky=tk.W, pady=2)
        self.board_width_var = tk.StringVar(value="1000")
        ttk.Entry(control_frame, textvariable=self.board_width_var, width=15).grid(row=1, column=1, pady=2, padx=(5, 0))

        ttk.Label(control_frame, text="高度 (mm):").grid(row=2, column=0, sticky=tk.W, pady=2)
        self.board_height_var = tk.StringVar(value="1000")
        ttk.Entry(control_frame, textvariable=self.board_height_var, width=15).grid(row=2, column=1, pady=2,
                                                                                    padx=(5, 0))

        # 分隔線
        ttk.Separator(control_frame, orient='horizontal').grid(row=3, column=0, columnspan=2, pady=10,
                                                               sticky=(tk.W, tk.E))

        # 排樣參數
        ttk.Label(control_frame, text="排樣參數", font=("Arial", 10, "bold")).grid(
            row=4, column=0, columnspan=2, pady=(0, 5), sticky=tk.W
        )

        ttk.Label(control_frame, text="文件間距 (mm):").grid(row=5, column=0, sticky=tk.W, pady=2)
        self.spacing_var = tk.StringVar(value="5")
        ttk.Entry(control_frame, textvariable=self.spacing_var, width=15).grid(row=5, column=1, pady=2, padx=(5, 0))

        ttk.Label(control_frame, text="最大旋轉角度:").grid(row=6, column=0, sticky=tk.W, pady=2)
        self.max_rotation_var = tk.StringVar(value="180")
        ttk.Entry(control_frame, textvariable=self.max_rotation_var, width=15).grid(row=6, column=1, pady=2,
                                                                                    padx=(5, 0))

        ttk.Label(control_frame, text="旋轉步長:").grid(row=7, column=0, sticky=tk.W, pady=2)
        self.rotation_step_var = tk.StringVar(value="90")
        ttk.Entry(control_frame, textvariable=self.rotation_step_var, width=15).grid(row=7, column=1, pady=2,
                                                                                     padx=(5, 0))

        ttk.Label(control_frame, text="排序方式:").grid(row=8, column=0, sticky=tk.W, pady=2)
        self.sort_method_var = tk.StringVar(value="area_desc")
        sort_combo = ttk.Combobox(control_frame, textvariable=self.sort_method_var,
                                  values=["area_desc", "width_desc", "height_desc"],
                                  width=13, state="readonly")
        sort_combo.grid(row=8, column=1, pady=2, padx=(5, 0))

        # 分隔線
        ttk.Separator(control_frame, orient='horizontal').grid(row=9, column=0, columnspan=2, pady=10,
                                                               sticky=(tk.W, tk.E))

        # 按鈕區域
        button_frame = ttk.Frame(control_frame)
        button_frame.grid(row=10, column=0, columnspan=2, pady=10)

        ttk.Button(button_frame, text="載入DXF文件", command=self.load_dxf, width=15).grid(row=0, column=0, pady=5)
        ttk.Button(button_frame, text="開始排樣", command=self.start_nesting, width=15).grid(row=1, column=0, pady=5)
        ttk.Button(button_frame, text="保存結果", command=self.save_result, width=15).grid(row=2, column=0, pady=5)
        ttk.Button(button_frame, text="清空所有", command=self.clear_files, width=15).grid(row=3, column=0, pady=5)
        ttk.Button(button_frame, text="測試數據", command=self.test, width=15).grid(row=4, column=0, pady=5)

        # 右側顯示區域
        display_frame = ttk.LabelFrame(main_frame, text="排樣結果", padding="10")
        display_frame.grid(row=0, column=1, sticky=(tk.N, tk.S, tk.E, tk.W))

        # 文件列表區域
        files_frame = ttk.LabelFrame(display_frame, text="已載入文件列表", padding="5")
        files_frame.grid(row=0, column=0, sticky=(tk.W, tk.E), pady=(0, 10))

        # 創建Treeview顯示文件列表
        self.create_files_treeview(files_frame)

        # 文件操作按鈕
        file_buttons_frame = ttk.Frame(files_frame)
        file_buttons_frame.grid(row=2, column=0, sticky=(tk.W, tk.E), pady=(5, 0))

        ttk.Button(file_buttons_frame, text="修改數量", command=self.edit_quantity, width=12).pack(side=tk.LEFT, padx=2)
        ttk.Button(file_buttons_frame, text="刪除選中", command=self.delete_selected, width=12).pack(side=tk.LEFT,
                                                                                                     padx=2)
        ttk.Button(file_buttons_frame, text="全部刪除", command=self.delete_all, width=12).pack(side=tk.LEFT, padx=2)

        # 結果信息
        info_frame = ttk.LabelFrame(display_frame, text="排樣信息", padding="5")
        info_frame.grid(row=1, column=0, sticky=(tk.W, tk.E), pady=(0, 10))

        self.info_text = tk.Text(info_frame, height=8, width=50, font=("Consolas", 9))
        self.info_text.grid(row=0, column=0)
        scrollbar = ttk.Scrollbar(info_frame, command=self.info_text.yview)
        scrollbar.grid(row=0, column=1, sticky=(tk.N, tk.S))
        self.info_text.config(yscrollcommand=scrollbar.set)

        # 圖形顯示區域
        canvas_frame = ttk.LabelFrame(display_frame, text="排樣預覽", padding="5")
        canvas_frame.grid(row=2, column=0, sticky=(tk.N, tk.S, tk.E, tk.W), pady=(0, 10))

        self.canvas = tk.Canvas(canvas_frame, width=700, height=400, bg="white",
                                highlightthickness=1, highlightbackground="gray")
        self.canvas.grid(row=0, column=0, sticky=(tk.N, tk.S, tk.E, tk.W))

        # 狀態欄
        self.status_var = tk.StringVar(value="就緒")
        status_bar = ttk.Label(display_frame, textvariable=self.status_var, relief=tk.SUNKEN)
        status_bar.grid(row=3, column=0, sticky=(tk.W, tk.E), pady=(5, 0))

        # 配置權重
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)
        main_frame.columnconfigure(1, weight=1)
        main_frame.rowconfigure(0, weight=1)
        display_frame.columnconfigure(0, weight=1)
        display_frame.rowconfigure(2, weight=1)
        canvas_frame.columnconfigure(0, weight=1)
        canvas_frame.rowconfigure(0, weight=1)

    def create_files_treeview(self, parent):
        """創建文件列表樹狀視圖"""
        # 創建Treeview
        self.files_tree = ttk.Treeview(parent, height=6, columns=("filename", "polygons", "size", "quantity"),
                                       show="headings")

        # 定義列
        self.files_tree.heading("filename", text="文件名")
        self.files_tree.heading("polygons", text="多邊形數量")
        self.files_tree.heading("size", text="尺寸 (mm)")
        self.files_tree.heading("quantity", text="數量")

        # 設置列寬
        self.files_tree.column("filename", width=150)
        self.files_tree.column("polygons", width=80)
        self.files_tree.column("size", width=120)
        self.files_tree.column("quantity", width=60)

        # 添加滾動條
        scrollbar = ttk.Scrollbar(parent, orient=tk.VERTICAL, command=self.files_tree.yview)
        self.files_tree.configure(yscrollcommand=scrollbar.set)

        # 佈局
        self.files_tree.grid(row=1, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        scrollbar.grid(row=1, column=1, sticky=(tk.N, tk.S))

        # 綁定事件
        self.files_tree.bind("<Double-1>", self.on_tree_double_click)

        # 配置父框架的權重
        parent.columnconfigure(0, weight=1)
        parent.rowconfigure(1, weight=1)

    def load_dxf(self):
        """載入DXF文件（自動追加新文件）"""
        filepaths = filedialog.askopenfilenames(
            title="選擇DXF文件（可多選）",
            filetypes=[("DXF files", "*.dxf"), ("All files", "*.*")]
        )

        if not filepaths:
            return  # 用戶取消選擇

        self.status_var.set(f"載入文件中...")
        self.root.update()  # 更新UI

        # 載入新文件
        new_files = DXFProcessor.load_multiple_dxf_files(filepaths)

        if new_files:
            # 追加新文件到現有列表
            self.dxf_files.extend(new_files)

            # 更新文件列表顯示
            self.update_files_treeview()

            # 計算統計信息
            self.update_statistics()

            # 在畫布上預覽文件
            self.preview_files()

            total_files = sum(dxf_file.quantity for dxf_file in self.dxf_files)
            self.status_var.set(f"已載入 {len(self.dxf_files)} 個文件，總數 {total_files} 個")
        else:
            messagebox.showwarning("警告", "未找到有效的DXF文件")
            self.status_var.set("載入失敗")

    def update_files_treeview(self):
        """更新文件樹狀視圖"""
        # 清空現有項目
        for item in self.files_tree.get_children():
            self.files_tree.delete(item)

        # 添加所有文件
        for i, dxf_file in enumerate(self.dxf_files):
            display_name = dxf_file.get_display_name()
            polygons_count = len(dxf_file.polygons)
            size = f"{dxf_file.bbox.width:.1f}x{dxf_file.bbox.height:.1f}"
            quantity = dxf_file.quantity

            # 插入到Treeview
            self.files_tree.insert("", "end", iid=str(i),
                                   values=(display_name, polygons_count, size, quantity))

    def on_tree_double_click(self, event):
        """樹狀視圖雙擊事件"""
        selection = self.files_tree.selection()
        if selection:
            self.edit_quantity()

    def edit_quantity(self):
        """修改選中文件的數量"""
        selection = self.files_tree.selection()
        if not selection:
            messagebox.showwarning("警告", "請先選擇一個文件")
            return

        index = int(selection[0])
        if index < 0 or index >= len(self.dxf_files):
            return

        dxf_file = self.dxf_files[index]

        # 彈出輸入對話框
        new_quantity = simpledialog.askinteger("修改數量",
                                               f"請輸入 {dxf_file.get_display_name()} 的數量:",
                                               initialvalue=dxf_file.quantity,
                                               minvalue=1, maxvalue=1000)

        if new_quantity is not None:
            dxf_file.quantity = new_quantity
            # 更新Treeview
            self.update_files_treeview()
            # 更新統計信息
            self.update_statistics()
            # 重新預覽
            self.preview_files()

            self.status_var.set(f"已更新 {dxf_file.get_display_name()} 的數量為 {new_quantity}")

    def delete_selected(self):
        """刪除選中的文件"""
        selection = self.files_tree.selection()
        if not selection:
            messagebox.showwarning("警告", "請先選擇要刪除的文件")
            return

        # 從後往前刪除，避免索引問題
        indices = [int(i) for i in selection]
        indices.sort(reverse=True)

        deleted_names = []
        for index in indices:
            if 0 <= index < len(self.dxf_files):
                deleted_names.append(self.dxf_files[index].get_display_name())
                del self.dxf_files[index]

        # 更新Treeview
        self.update_files_treeview()
        # 更新統計信息
        self.update_statistics()
        # 重新預覽
        self.preview_files()

        if deleted_names:
            self.status_var.set(f"已刪除 {len(deleted_names)} 個文件")

    def delete_all(self):
        """刪除所有文件"""
        if not self.dxf_files:
            return

        if messagebox.askyesno("確認", "確定要刪除所有文件嗎？"):
            self.dxf_files.clear()
            self.update_files_treeview()
            self.update_statistics()
            self.preview_files()
            self.status_var.set("已刪除所有文件")

    def update_statistics(self):
        """更新統計信息"""
        if not self.dxf_files:
            self.update_info("尚未載入任何文件")
            return

        # 計算總面積
        total_area = sum(f.bbox.area * f.quantity for f in self.dxf_files)
        total_files = sum(f.quantity for f in self.dxf_files)
        unique_files = len(self.dxf_files)

        # 顯示統計信息
        info = f"文件統計:\n"
        info += f"唯一文件數量: {unique_files} 個\n"
        info += f"總文件數量: {total_files} 個\n"
        info += f"總面積: {total_area:.2f} mm²\n"

        # 添加每個文件的詳細信息
        info += f"\n文件詳情:\n"
        for i, dxf_file in enumerate(self.dxf_files):
            info += f"{i + 1}. {dxf_file.get_display_name()}: "
            info += f"尺寸 {dxf_file.bbox.width:.1f}x{dxf_file.bbox.height:.1f}, "
            info += f"面積 {dxf_file.bbox.area:.1f} mm², "
            info += f"數量 {dxf_file.quantity} 個\n"

        self.update_info(info)

    def preview_files(self):
        """預覽載入的文件"""
        self.canvas.delete("all")

        if not self.dxf_files:
            return

        # 計算所有文件的邊界
        all_points = []
        for dxf_file in self.dxf_files:
            for polygon in dxf_file.polygons:
                all_points.extend([(p.x, p.y) for p in polygon])

        if not all_points:
            return

        xs = [p[0] for p in all_points]
        ys = [p[1] for p in all_points]
        min_x, max_x = min(xs), max(xs)
        min_y, max_y = min(ys), max(ys)

        width = max_x - min_x
        height = max_y - min_y

        if width == 0 or height == 0:
            width = height = 100

        # 計算縮放比例
        canvas_width = 650
        canvas_height = 350

        scale_x = canvas_width / width if width > 0 else 1
        scale_y = canvas_height / height if height > 0 else 1
        scale = min(scale_x, scale_y, 5) * 0.8  # 限制最大縮放

        offset_x = -min_x * scale + 20
        offset_y = -min_y * scale + 20

        # 繪製文件
        for i, dxf_file in enumerate(self.dxf_files):
            color = dxf_file.color

            # 繪製文件中的所有多邊形
            for polygon in dxf_file.polygons:
                points = []
                for point in polygon:
                    x = point.x * scale + offset_x
                    y = point.y * scale + offset_y
                    points.extend([x, y])

                if len(points) >= 6:  # 至少3個點
                    self.canvas.create_polygon(points, fill=color, outline="black", width=1, tags="file")

            # 標註文件編號
            centroid = dxf_file.bbox.center
            text_x = centroid.x * scale + offset_x
            text_y = centroid.y * scale + offset_y
            self.canvas.create_text(text_x, text_y, text=str(i + 1), fill="white",
                                    font=("Arial", 8, "bold"))

        # 顯示信息
        total_files = sum(dxf_file.quantity for dxf_file in self.dxf_files)
        info_text = f"文件預覽: {len(self.dxf_files)} 個文件, 總數: {total_files} 個"
        self.canvas.create_text(10, 10, text=info_text,
                                anchor=tk.NW, font=("Arial", 10, "bold"), fill="darkblue")

        # 顯示圖例
        legend_x = 10
        legend_y = 30
        for i, dxf_file in enumerate(self.dxf_files[:5]):  # 最多顯示5個圖例
            # 繪製顏色方塊
            self.canvas.create_rectangle(legend_x, legend_y + i * 20, legend_x + 15, legend_y + i * 20 + 15,
                                         fill=dxf_file.color, outline="black")
            # 顯示文件名
            self.canvas.create_text(legend_x + 20, legend_y + i * 20 + 7,
                                    text=f"{i + 1}. {dxf_file.get_display_name()}",
                                    anchor=tk.W, font=("Arial", 8))

    def start_nesting(self):
        """開始排樣計算"""
        if not self.dxf_files:
            messagebox.showwarning("警告", "請先載入DXF文件")
            return

        try:
            board_width = float(self.board_width_var.get())
            board_height = float(self.board_height_var.get())
            spacing = float(self.spacing_var.get())
            max_rotation = float(self.max_rotation_var.get())
            rotation_step = float(self.rotation_step_var.get())
            sort_method = self.sort_method_var.get()

            if board_width <= 0 or board_height <= 0:
                messagebox.showerror("錯誤", "板材尺寸必須大於0")
                return

            if max_rotation < 0 or max_rotation > 360:
                messagebox.showerror("錯誤", "最大旋轉角度必須在0-360度之間")
                return

            if rotation_step <= 0 or rotation_step > 360:
                messagebox.showerror("錯誤", "旋轉步長必須在0-360度之間")
                return

            # 計算文件總面積
            total_file_area = sum(f.bbox.area * f.quantity for f in self.dxf_files)
            total_file_count = sum(f.quantity for f in self.dxf_files)
            board_area = board_width * board_height

            if total_file_area > board_area * 2:  # 允許200%的估算
                response = messagebox.askyesno("警告",
                                               f"文件總面積 ({total_file_area:.1f} mm²) 明顯超過板材面積 ({board_area:.1f} mm²)。\n"
                                               f"文件總數: {total_file_count} 個\n"
                                               f"可能無法放置所有文件。是否繼續？")
                if not response:
                    return

            self.status_var.set("正在排樣...")
            self.root.update()  # 更新UI

            # 創建排樣算法實例
            algorithm = NestingAlgorithm(
                board_width, board_height,
                spacing, max_rotation, rotation_step
            )

            # 開始計時
            start_time = time.time()

            # 執行排樣
            self.current_board = algorithm.nest_files(self.dxf_files, sort_method)

            # 計算時間
            elapsed_time = time.time() - start_time

            # 顯示結果
            self.display_result(elapsed_time)
            self.status_var.set(f"排樣完成，利用率: {self.current_board.utilization:.1f}%")

        except ValueError as e:
            messagebox.showerror("錯誤", f"參數錯誤: {str(e)}")
            self.status_var.set("參數錯誤")

    def display_result(self, elapsed_time):
        """顯示排樣結果"""
        self.canvas.delete("all")

        if not self.current_board:
            return

        board_width = self.current_board.width
        board_height = self.current_board.height

        # 計算縮放比例
        canvas_width = 650
        canvas_height = 350

        scale_x = canvas_width / board_width if board_width > 0 else 1
        scale_y = canvas_height / board_height if board_height > 0 else 1
        scale = min(scale_x, scale_y, 5) * 0.9

        offset_x = 20
        offset_y = 20

        # 繪製板材邊界
        board_points = [
            offset_x, offset_y,
            board_width * scale + offset_x, offset_y,
            board_width * scale + offset_x, board_height * scale + offset_y,
            offset_x, board_height * scale + offset_y
        ]
        self.canvas.create_polygon(board_points, fill="lightgray", outline="black", width=2)

        # 繪製已放置文件
        for i, dxf_file in enumerate(self.current_board.placed_files):
            color = dxf_file.color

            # 繪製文件中的所有多邊形
            for polygon in dxf_file.polygons:
                points = []
                for point in polygon:
                    x = point.x * scale + offset_x
                    y = point.y * scale + offset_y
                    points.extend([x, y])

                if len(points) >= 6:  # 至少3個點
                    self.canvas.create_polygon(points, fill=color, outline="black", width=1)

            # 標註文件編號
            centroid = dxf_file.bbox.center
            text_x = centroid.x * scale + offset_x
            text_y = centroid.y * scale + offset_y
            self.canvas.create_text(text_x, text_y, text=str(i + 1), fill="white",
                                    font=("Arial", 8, "bold"))

        # 更新信息顯示
        total_files = sum(dxf_file.quantity for dxf_file in self.dxf_files)
        placed_count = len(self.current_board.placed_files)

        info = f"排樣完成！\n"
        info += f"計算時間: {elapsed_time:.2f}秒\n"
        info += f"板材尺寸: {board_width} x {board_height} mm\n"
        info += f"板材面積: {board_width * board_height:.1f} mm²\n"
        info += f"文件種類: {len(self.dxf_files)} 種\n"
        info += f"文件總數: {total_files} 個\n"
        info += f"成功放置: {placed_count} 個\n"
        info += f"放置率: {placed_count / total_files * 100:.1f}% (按數量)\n"
        info += f"已用面積: {self.current_board.get_placed_area():.1f} mm²\n"
        info += f"材料利用率: {self.current_board.utilization:.2f}%\n"

        # 顯示文件統計
        stats = self.current_board.get_files_statistics()
        if stats:
            info += f"\n文件統計:\n"
            for filename, stat in stats.items():
                info += f"  {filename}: {stat['count']} 個, 面積: {stat['area']:.1f} mm²\n"

        self.update_info(info)

        # 顯示統計信息
        stats_x = offset_x + 10
        stats_y = offset_y + 20
        self.canvas.create_text(stats_x, stats_y,
                                text=f"利用率: {self.current_board.utilization:.1f}%",
                                anchor=tk.NW, font=("Arial", 10, "bold"), fill="darkblue")

        # 顯示板材信息
        board_info = f"板材: {board_width} x {board_height} mm"
        self.canvas.create_text(stats_x, stats_y + 20,
                                text=board_info,
                                anchor=tk.NW, font=("Arial", 9), fill="darkgreen")

        # 顯示放置數量
        placed_info = f"已放置: {placed_count}/{total_files} 個"
        self.canvas.create_text(stats_x, stats_y + 40,
                                text=placed_info,
                                anchor=tk.NW, font=("Arial", 9), fill="darkred")

    def update_info(self, text):
        """更新信息顯示"""
        self.info_text.delete(1.0, tk.END)
        self.info_text.insert(1.0, text)

    def save_result(self):
        """保存排樣結果"""
        if not self.current_board:
            messagebox.showwarning("警告", "沒有可保存的排樣結果")
            return

        filepath = filedialog.asksaveasfilename(
            title="保存排樣結果",
            defaultextension=".dxf",
            filetypes=[("DXF files", "*.dxf"), ("All files", "*.*")]
        )

        if filepath:
            self.status_var.set("正在保存...")
            self.root.update()

            success = DXFProcessor.save_nesting_result(self.current_board, filepath)
            if success:
                messagebox.showinfo("成功", f"排樣結果已保存到: {filepath}")
                self.status_var.set("保存完成")
            else:
                self.status_var.set("保存失敗")

    def clear_files(self):
        """清空文件列表"""
        self.dxf_files = []
        self.current_board = None
        self.update_files_treeview()
        self.canvas.delete("all")
        self.update_info("")
        self.status_var.set("已清空文件")
        self.info_text.insert(1.0, "歡迎使用DXF自動排樣系統 (整體文件排樣)\n\n")
        self.info_text.insert(tk.END, "特點: 每個DXF文件作為一個整體進行排樣\n\n")
        self.info_text.insert(tk.END, "使用步驟:\n")
        self.info_text.insert(tk.END, "1. 點擊'載入DXF文件'選擇DXF文件（可多選）\n")
        self.info_text.insert(tk.END, "2. 在文件列表中查看和修改每個文件的數量\n")
        self.info_text.insert(tk.END, "3. 設置板材尺寸和排樣參數\n")
        self.info_text.insert(tk.END, "4. 點擊'開始排樣'進行自動排列\n")
        self.info_text.insert(tk.END, "5. 點擊'保存結果'導出排樣DXF文件\n")
        self.info_text.insert(tk.END, "6. 點擊'測試數據'創建測試文件\n")

    def test(self):
        """測試功能：創建測試文件"""
        self.dxf_files = []

        # 創建測試文件1：包含多個多邊形
        polygons1 = [
            # 矩形
            [Point(0, 0), Point(100, 0), Point(100, 50), Point(0, 50), Point(0, 0)],
            # 內部的小矩形
            [Point(20, 10), Point(80, 10), Point(80, 40), Point(20, 40), Point(20, 10)],
        ]

        # 創建測試文件2：包含多個多邊形
        polygons2 = [
            # 三角形
            [Point(0, 0), Point(80, 0), Point(40, 60), Point(0, 0)],
        ]

        # 添加圓形
        circle_points = []
        for i in range(24):
            angle = 2 * math.pi * i / 24
            x = 40 + 25 * math.cos(angle)
            y = 40 + 25 * math.sin(angle)
            circle_points.append(Point(x, y))
        circle_points.append(circle_points[0])  # 閉合
        polygons2.append(circle_points)

        # 創建測試文件3：L形
        polygons3 = [
            [Point(0, 0), Point(60, 0), Point(60, 20), Point(20, 20),
             Point(20, 60), Point(0, 60), Point(0, 0)],
        ]

        # 創建DXF文件對象
        self.dxf_files.append(DXFFile("test1.dxf", "test1.dxf", polygons1, quantity=2, color="red"))
        self.dxf_files.append(DXFFile("test2.dxf", "test2.dxf", polygons2, quantity=1, color="blue"))
        self.dxf_files.append(DXFFile("test3.dxf", "test3.dxf", polygons3, quantity=3, color="green"))

        self.update_files_treeview()
        self.update_statistics()
        self.preview_files()
        self.status_var.set(f"已創建 {len(self.dxf_files)} 個測試文件")


def main():
    root = tk.Tk()
    app = NestingApp(root)

    # 設置窗口初始信息
    app.info_text.insert(1.0, "歡迎使用DXF自動排樣系統 (整體文件排樣)\n\n")
    app.info_text.insert(tk.END, "特點: 每個DXF文件作為一個整體進行排樣\n\n")
    app.info_text.insert(tk.END, "使用步驟:\n")
    app.info_text.insert(tk.END, "1. 點擊'載入DXF文件'選擇DXF文件（可多選）\n")
    app.info_text.insert(tk.END, "2. 在文件列表中查看和修改每個文件的數量\n")
    app.info_text.insert(tk.END, "3. 設置板材尺寸和排樣參數\n")
    app.info_text.insert(tk.END, "4. 點擊'開始排樣'進行自動排列\n")
    app.info_text.insert(tk.END, "5. 點擊'保存結果'導出排樣DXF文件\n")
    app.info_text.insert(tk.END, "6. 點擊'測試數據'創建測試文件\n")

    root.mainloop()


if __name__ == "__main__":
    main()