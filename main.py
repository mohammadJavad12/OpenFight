from __future__ import annotations

import asyncio
import heapq
import math
import random
import secrets
import threading
import time
from dataclasses import dataclass
from concurrent.futures import ThreadPoolExecutor, as_completed
from enum import Enum

from replay_saver import ReplayManager
import numpy as np
import uvicorn
from fastapi import Body, FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse
from fastapi.staticfiles import StaticFiles
from PIL import Image


# -------------------------------
#  CONFIGURATION & DATA 
# -------------------------------


@dataclass(frozen=True)
class GameConfig:
    width: int = 888
    height: int = 500
    players_needed: int = 5
    simulation_interval: float = 0.05

    radiation_team_id: int = -2

    water: int = 0
    land: int = 1

    join_secret: str = "ch"
    admin_secret: str = "ch1"
    starting_tiles: int = 80
    naval_range: int = 900

    min_players_to_start: int = 2
    game_duration_minutes: int = 30
    lobby_timeout_seconds: int = 120

class GameStatus(Enum):
    WAITING = "waiting"
    ACTIVE = "active"
    ENDED = "ended"

class ResourceType(Enum):
    IRON = "iron"
    URANIUM = "uranium"

RESOURCE_DEFS = {
    ResourceType.IRON : {
        "rarity": 0.002,
        "Amount": 100,
        "extraction_rate" : 1,
        "description" : "Iron is used to make citys and factorys"
    },
    ResourceType.URANIUM :{
        "rarity":0.0003,
        "Amount": 10,
        "extraction_rate" : 0.2,
        "description": "Uranium is used to make nukes and nuclear reactors"
    }
}


class BuildingType(Enum):
    CITY = "city"
    FACTORY = "factory"
    PORT = "port"
    IRON_MINE = "iron_mine"
    LAUNCHER = "launcher"
    URANIUM_MINE = "uranium_mine"

BUILDING_DEFS = {
    BuildingType.CITY: {
        "cost": 3000,
        "hp": 500,
        "needed_resources": {ResourceType.IRON: 200,ResourceType.URANIUM: 0},
        "regen_bonus": 5,
        "description": "Increases army regeneration"
    },
    BuildingType.FACTORY: {
        "cost": 3000,
        "hp": 400,
        "needed_resources": {ResourceType.IRON: 300,ResourceType.URANIUM: 0},
        "attack_bonus": 1.5,
        "description": "Boosts attack strength"
    },
    BuildingType.PORT: {
        "cost": 1500,
        "hp": 300,
        "needed_resources": {ResourceType.IRON: 200,ResourceType.URANIUM: 0},
        "naval_range_bonus": 50,
        "description": "Extends naval invasion range"
    },
    BuildingType.IRON_MINE: {
        "cost": 1000,
        "hp": 600,
        "needed_resources": {ResourceType.IRON: 0,ResourceType.URANIUM: 0},
        "description": "Allows GETTING IRON"
    },
    BuildingType.URANIUM_MINE: {
        "cost": 1000,
        "hp": 600,
        "needed_resources": {ResourceType.IRON: 500,ResourceType.URANIUM: 0},
        "description": "Allows GETTING IRON"
    },
    BuildingType.LAUNCHER: {
        "cost": 1500,
        "hp": 200,
        "needed_resources": {ResourceType.IRON: 200,ResourceType.URANIUM: 0},
        "missile_damage": 80,
        "description": "Can launch missiles"
    }
}


class MissileType(Enum):
    NUKE = "nuke"
    CONVENTIONAL = "conventional"


MISSILE_DEFS = {
    MissileType.NUKE: {
        "cost": 3000,
        "damage": 200,
        "needed_resources": {ResourceType.IRON: 500,ResourceType.URANIUM: 20},
        "blast_radius": 22,
        "speed": 0.3,
        "description": "Nuclear missile – destroys everything in blast radius"
    },
    MissileType.CONVENTIONAL: {
        "cost": 1000,
        "damage": 100,
        "needed_resources": {ResourceType.IRON: 500,ResourceType.URANIUM: 0},
        "blast_radius": 8,
        "speed": 0.7,
        "description": "Conventional missile – smaller blast"
    }
}



@dataclass
class Missile:
    missile_id: int
    owner: int
    missile_type: MissileType
    path: list[tuple[int, int]]
    current_index: int = 0
    progress: float = 0.0
    speed: float = 0.2

    def current_position(self) -> tuple[float, float]:
        if self.current_index >= len(self.path) - 1:
            return self.path[-1]
        x1, y1 = self.path[self.current_index]
        x2, y2 = self.path[self.current_index + 1]
        x = x1 + (x2 - x1) * self.progress
        y = y1 + (y2 - y1) * self.progress
        return x, y

    def update(self) -> bool:
        if self.current_index >= len(self.path) - 1:
            return True
        self.progress += self.speed
        while self.progress >= 1.0:
            self.progress -= 1.0
            self.current_index += 1
            if self.current_index >= len(self.path) - 1:
                return True
        return False


@dataclass
class Fleet:
    fleet_id: int
    owner: int
    path: list[tuple[int, int]]
    current_index: int = 0
    progress: float = 0.0
    speed: float = 0.15
    is_trade: bool = False
    def current_position(self) -> tuple[float, float]:
        if self.current_index >= len(self.path) - 1:
            return self.path[-1]
        x1, y1 = self.path[self.current_index]
        x2, y2 = self.path[self.current_index + 1]
        x = x1 + (x2 - x1) * self.progress
        y = y1 + (y2 - y1) * self.progress
        return x, y

    def update(self) -> bool:
        if self.current_index >= len(self.path) - 1:
            return True
        self.progress += self.speed
        while self.progress >= 1.0:
            self.progress -= 1.0
            self.current_index += 1
            if self.current_index >= len(self.path) - 1:
                return True
        return False


# -------------------------------
#  GAME STATE 
# -------------------------------
class GameState:
    def __init__(self, config: GameConfig):
        self.config = config

        self.send_ship_tick = 0

        self.current_tick = 0

        self.players: dict[str, dict] = {}
        self.country_owner: dict[int, str] = {}

        self.countries: dict[int, dict] = {}
        self.next_country_id = 1


        self.countries[self.config.radiation_team_id] = {
            "army": 50000,
            "max_army": 100000,
            "target": None,
            "money": 0,
            "resources": {resource_t : 0 for resource_t in RESOURCE_DEFS}
        }

        self.radiation: dict[tuple[int, int], dict] = {}
        self.radiation_damage_per_tick = 5
        self.radiation_duration = 300

        self.fleets: dict[int, Fleet] = {}
        self._next_fleet_id = 1
        self.attack_orders: dict[int, dict | None] = {}

        self.missiles: dict[int, Missile] = {}
        self._next_missile_id = 1

        self.buildings: dict[tuple[int, int], dict] = {}
        self.resources : dict[tuple[int, int], dict] = {}
        self.changed_buildings: set[tuple[int, int]] = set()


        self.world = np.zeros((config.height, config.width), dtype=np.int16)
        self.terrain = np.zeros((config.height, config.width), dtype=np.uint8)

        self.pressure = np.zeros((config.height, config.width), dtype=np.float32)
        self.tile_strength = np.full((config.height, config.width), 100, dtype=np.float32)

        self.territory_count: dict[int, int] = {}
        self.building_counts: dict[int, dict[str, int]] = {}  


        self._world_list: list[list[int]] = []
        self._terrain_list: list[list[int]] = []

        self.active_tiles: set[tuple[int, int]] = set()
        self.changed_tiles: set[tuple[int, int]] = set()
        self.coastal_tiles: dict[int, set[tuple[int, int]]] = {}

        self.game_status = GameStatus.WAITING
        self.game_start_time = None
        self.game_end_time = None
        self.game_duration_seconds = config.game_duration_minutes * 60
        self.lobby_start_time = time.time()
        self.winner_country_id = None
        self.final_scores = {}
        self.is_game_locked = False

    @property
    def neighbors(self):
        return ((1, 0), (-1, 0), (0, 1), (0, -1))

    def start_game(self) -> dict:
        if self.game_status != GameStatus.WAITING:
            return {"success": False, "error": f"Game already {self.game_status.value}"}
        
        active_players = [p for p in self.players.values() if p["country"] is not None]
        if len(active_players) < self.config.min_players_to_start:
            return {
                "success": False, 
                "error": f"Need at least {self.config.min_players_to_start} players with countries. Currently: {len(active_players)}"
            }
        
        self.game_status = GameStatus.ACTIVE
        self.game_start_time = time.time()
        self.is_game_locked = False
        
        return {
            "success": True,
            "message": "Game started!",
            "players": len(active_players),
            "duration_minutes": self.config.game_duration_minutes
        }
    
    def check_end_conditions(self) -> bool:
        if self.game_status != GameStatus.ACTIVE:
            return False
        
        if self.game_start_time:
            elapsed = time.time() - self.game_start_time
            if elapsed > self.game_duration_seconds:
                print(f"⏰ Time limit reached ({self.config.game_duration_minutes} minutes)")
                self.end_game()
                return True
        
        active_countries = []
        for cid in self.countries.keys():
            if cid != self.config.radiation_team_id:
                if self.territory_count.get(cid, 0) > 0:
                    active_countries.append(cid)
        
        if len(active_countries) <= 1:
            winner = active_countries[0] if active_countries else None
            print(f"Winner: {winner}")
            self.end_game(winner)
            return True
        
        return False
    
    def end_game(self, winner_id: int = None) -> dict:
        if self.game_status == GameStatus.ENDED:
            return {"success": False, "error": "Game already ended"}
        
        self.game_status = GameStatus.ENDED
        self.game_end_time = time.time()
        self.is_game_locked = True
        self.winner_country_id = winner_id
        
        scores = {}
        for cid, country in self.countries.items():
            if cid == self.config.radiation_team_id:
                continue
            
            territory = self.territory_count.get(cid, 0)
            army = country.get("army", 0)
            money = country.get("money", 0)
            buildings = self.building_counts.get(cid, {})
            
            score = (
                territory * 2 + 
                army * 1 + 
                money / 100 + 
                buildings.get("city", 0) * 50 +
                buildings.get("factory", 0) * 30 +
                buildings.get("port", 0) * 20
            )
            
            player_name = "Unknown"
            for token, player in self.players.items():
                if player.get("country") == cid:
                    player_name = player.get("name", "Unknown")
                    break
            
            scores[cid] = {
                "name": player_name,
                "score": round(score, 2),
                "territory": territory,
                "army": int(army),
                "money": int(money),
                "buildings": buildings
            }
        
        sorted_scores = sorted(scores.items(), key=lambda x: x[1]["score"], reverse=True)
        self.final_scores = dict(sorted_scores)
        
        if winner_id is None and sorted_scores:
            self.winner_country_id = sorted_scores[0][0]

        
        return {
            "success": True,
            "winner": self.winner_country_id,
            "scores": self.final_scores,
            "duration_seconds": int(self.game_end_time - self.game_start_time) if self.game_start_time else 0
        }
    
    def in_bounds(self, x: int, y: int) -> bool:
        return 0 <= x < self.config.width and 0 <= y < self.config.height

    def has_different_neighbor(self, x: int, y: int) -> bool:
        owner = self.world[y, x]
        if owner == 0:
            return False
        for dx, dy in self.neighbors:
            nx, ny = x + dx, y + dy
            if self.in_bounds(nx, ny) and self.world[ny, nx] != owner:
                return True
        return False

    def is_coastal(self, x: int, y: int) -> bool:
        if self.terrain[y, x] != self.config.land:
            return False
        for dx, dy in self.neighbors:
            nx, ny = x + dx, y + dy
            if self.in_bounds(nx, ny) and self.terrain[ny, nx] == self.config.water:
                return True
        return False

    def _add_building(self, x: int, y: int, btype: BuildingType, owner: int, hp: int):
        building_data = {"type": btype, "owner": owner, "hp": hp}
        
        building_data["resource_id"] = None  

        if btype == BuildingType.IRON_MINE:
            resource_pos = self.getNearestResource((x, y), ResourceType.IRON, 10)
            building_data["resource_id"] = resource_pos

        if btype == BuildingType.URANIUM_MINE:
            resource_pos = self.getNearestResource((x, y), ResourceType.URANIUM, 10)
            building_data["resource_id"] = resource_pos
        

        self.buildings[(x, y)] = building_data
        if owner not in self.building_counts:
            self.building_counts[owner] = {"city": 0, "factory": 0, "port": 0}
        if btype == BuildingType.CITY:
            self.building_counts[owner]["city"] += 1
        elif btype == BuildingType.FACTORY:
            self.building_counts[owner]["factory"] += 1
        elif btype == BuildingType.PORT:
            self.building_counts[owner]["port"] += 1

    def _remove_building(self, x: int, y: int):
        if (x, y) in self.buildings:
            b = self.buildings.pop((x, y))
            owner = b["owner"]
            if owner in self.building_counts:
                if b["type"] == BuildingType.CITY:
                    self.building_counts[owner]["city"] -= 1
                elif b["type"] == BuildingType.FACTORY:
                    self.building_counts[owner]["factory"] -= 1
                elif b["type"] == BuildingType.PORT:
                    self.building_counts[owner]["port"] -= 1

    def update_active_tile(self, x: int, y: int) -> None:
        if self.world[y, x] == 0:
            self.active_tiles.discard((x, y))
            return
        if self.has_different_neighbor(x, y):
            self.active_tiles.add((x, y))
        else:
            self.active_tiles.discard((x, y))

    def update_neighbours(self, x: int, y: int) -> None:
        self.update_active_tile(x, y)
        for dx, dy in self.neighbors:
            nx, ny = x + dx, y + dy
            if self.in_bounds(nx, ny):
                self.update_active_tile(nx, ny)

    # -----------------------------------------------------------------
    #  IMPROVED BIDIRECTIONAL A* (tighter bounding box)
    # -----------------------------------------------------------------
    def find_water_path(self, start: tuple[int, int], end: tuple[int, int]) -> tuple[int | None, list[tuple[int, int]]]:
        if start == end:
            return 0, [start]
        if abs(start[0] - end[0]) + abs(start[1] - end[1]) == 1:
            return 1, [start, end]

        straight_dist = math.hypot(start[0] - end[0], start[1] - end[1])
        margin = min(int(straight_dist * 0.5), self.config.naval_range) + 10
        min_x = max(0, min(start[0], end[0]) - margin)
        max_x = min(self.config.width - 1, max(start[0], end[0]) + margin)
        min_y = max(0, min(start[1], end[1]) - margin)
        max_y = min(self.config.height - 1, max(start[1], end[1]) + margin)

        terrain = self.terrain
        water = self.config.water
        in_bounds = self.in_bounds

        def in_bb(tile):
            x, y = tile
            return min_x <= x <= max_x and min_y <= y <= max_y and in_bounds(x, y)

        def is_passable(tile):
            if tile == end:
                return True
            x, y = tile
            return terrain[y, x] == water

        def heuristic(a, b):
            return abs(a[0] - b[0]) + abs(a[1] - b[1])

        open_f, open_b = [], []
        heapq.heappush(open_f, (heuristic(start, end), 0, start[0], start[1]))
        heapq.heappush(open_b, (heuristic(end, start), 0, end[0], end[1]))

        g_f, g_b = {start: 0}, {end: 0}
        parent_f, parent_b = {start: None}, {end: None}
        visited_f, visited_b = {start}, {end}
        max_dist = self.config.naval_range

        while open_f and open_b:
            if open_f:
                _, g, cx, cy = heapq.heappop(open_f)
                current = (cx, cy)
                if current in visited_b:
                    return self._reconstruct_bidirectional(current, parent_f, parent_b)

                for dx, dy in self.neighbors:
                    nx, ny = cx + dx, cy + dy
                    neighbor = (nx, ny)
                    if not in_bb(neighbor) or not is_passable(neighbor):
                        continue
                    tentative_g = g_f[current] + 1
                    if tentative_g > max_dist:
                        continue
                    if tentative_g < g_f.get(neighbor, float('inf')):
                        g_f[neighbor] = tentative_g
                        parent_f[neighbor] = current
                        f = tentative_g + heuristic(neighbor, end)
                        heapq.heappush(open_f, (f, tentative_g, nx, ny))
                        visited_f.add(neighbor)

            if open_b:
                _, g, cx, cy = heapq.heappop(open_b)
                current = (cx, cy)
                if current in visited_f:
                    return self._reconstruct_bidirectional(current, parent_f, parent_b)

                for dx, dy in self.neighbors:
                    nx, ny = cx + dx, cy + dy
                    neighbor = (nx, ny)
                    if not in_bb(neighbor) or not is_passable(neighbor):
                        continue
                    tentative_g = g_b[current] + 1
                    if tentative_g > max_dist:
                        continue
                    if tentative_g < g_b.get(neighbor, float('inf')):
                        g_b[neighbor] = tentative_g
                        parent_b[neighbor] = current
                        f = tentative_g + heuristic(neighbor, start)
                        heapq.heappush(open_b, (f, tentative_g, nx, ny))
                        visited_b.add(neighbor)

        return None, []

    def _reconstruct_bidirectional(self, meeting, parent_f, parent_b):
        path = []
        node = meeting
        while node is not None:
            path.append(node)
            node = parent_f[node]
        path.reverse()
        node = parent_b[meeting]
        while node is not None:
            path.append(node)
            node = parent_b[node]
        return len(path) - 1, path

    def generate_straight_path(self, start, end, steps=50):
        path = []
        for i in range(steps + 1):
            t = i / steps
            x = start[0] + (end[0] - start[0]) * t
            y = start[1] + (end[1] - start[1]) * t
            path.append((x, y))
        return path

    def spawn_missile(self, owner, missile_type, start, target):
        mid = self._next_missile_id
        self._next_missile_id += 1
        path = self.generate_straight_path(start, target)
        speed = MISSILE_DEFS[missile_type]["speed"]
        missile = Missile(missile_id=mid, owner=owner, missile_type=missile_type, path=path, speed=speed)
        self.missiles[mid] = missile
        return missile

    def spawn_fleet(self, owner, path,isTrade):
        fid = self._next_fleet_id
        self._next_fleet_id += 1
        fleet = Fleet(fleet_id=fid, owner=owner, path=path, is_trade=isTrade)
        self.fleets[fid] = fleet
        return fleet
    def send_trade_ship(self):
        ports = []
        for (x, y), building in self.buildings.items():
            if building["type"] == BuildingType.PORT:
                ports.append((x, y))
        
        if len(ports) < 2:
            return
        

        from_port = random.choice(ports)
        to_port = random.choice([p for p in ports if p != from_port])
        
        distance, path = self.find_water_path(from_port, to_port)
        
        if path:

            port_owner = self.buildings[from_port]["owner"]

            self.spawn_fleet(port_owner, path,True)
            print(f"Trade ship sent from {from_port} to {to_port}")
        

            
            
    def update_country_stats(self) -> None:
        for cid, stats in self.countries.items():
            territory = self.territory_count.get(cid, 0)
            base_max = max(500, territory * 15)
            base_regen = max(1, territory // 100)

            bcounts = self.building_counts.get(cid, {"city": 0, "factory": 0, "port": 0})
            for (x, y), building in list(self.buildings.items()):
                    
                    if building["type"] == BuildingType.IRON_MINE and building["owner"] == cid:
                        if building.get("resource_id") is not None:  
                            stats['resources'][ResourceType.IRON] += RESOURCE_DEFS[ResourceType.IRON]["extraction_rate"]  / 10
                    if building["type"] == BuildingType.URANIUM_MINE and building["owner"] == cid:
                        if building.get("resource_id") is not None:  
                            stats['resources'][ResourceType.URANIUM] +=  RESOURCE_DEFS[ResourceType.URANIUM]["extraction_rate"] / 10
            extra_regen = bcounts["city"] * 5
            extra_max = bcounts["factory"] * 200

            stats["max_army"] = base_max + extra_max
            stats["army"] = min(base_max + extra_max, stats["army"] + base_regen + extra_regen) + 2
            stats["money"] += 0.8 + bcounts["city"] * 0.2 + bcounts["factory"] * 0.5 + max(1, territory // 500)



    def create_country(self, token: str, seed_x: int, seed_y: int) -> dict:
        if not self.in_bounds(seed_x, seed_y):
            return {"success": False, "error": "Coordinates out of bounds"}
        if self.terrain[seed_y, seed_x] != self.config.land:
            return {"success": False, "error": "Must place on land"}
        if self.world[seed_y, seed_x] != 0:
            return {"success": False, "error": "Tile already owned"}

        country_id = self.next_country_id
        self.next_country_id += 1

        claimed = set()
        heap = []
        self.world[seed_y, seed_x] = country_id
        claimed.add((seed_x, seed_y))
        self._push_neighbors_to_heap(heap, seed_x, seed_y, seed_x, seed_y, claimed)

        count = 1
        while heap and count < self.config.starting_tiles:
            _, x, y = heapq.heappop(heap)
            if (x, y) in claimed:
                continue
            claimed.add((x, y))
            self.world[y, x] = country_id
            count += 1
            self._push_neighbors_to_heap(heap, x, y, seed_x, seed_y, claimed)

        self.countries[country_id] = {
            "army": count * 10,
            "max_army": count * 10,
            "target": None,
            "money": 2000,
            "resources": {resource_t : 0 for resource_t in RESOURCE_DEFS}
        }
        print(self.countries[country_id])
        self.attack_orders[country_id] = None
        self.players[token]["country"] = country_id
        self.country_owner[country_id] = token

        self.territory_count[country_id] = count
        self.building_counts[country_id] = {"city": 0, "factory": 0, "port": 0}

        if country_id not in self.coastal_tiles:
            self.coastal_tiles[country_id] = set()

        for (x, y) in claimed:
            self.update_active_tile(x, y)
            for dx, dy in self.neighbors:
                nx, ny = x + dx, y + dy
                if self.in_bounds(nx, ny):
                    self.update_active_tile(nx, ny)
            if self.is_coastal(x, y):
                self.coastal_tiles[country_id].add((x, y))

        self._sync_world_list()

        print(f"Country {country_id} created with {count} tiles at ({seed_x}, {seed_y})")
        return {
            "success": True,
            "country": country_id,
            "tiles": count,
        }
    def getNearestResource(self, pos, resourceType, radius):
        px, py = pos
        nearest = None
        nearest_dist_sq = radius * radius

        for (x, y), resource in self.resources.items():
            if resource.get("type") != resourceType:
                continue

            dx = x - px
            dy = y - py
            dist_sq = dx * dx + dy * dy

            if dist_sq <= nearest_dist_sq:
                nearest_dist_sq = dist_sq
                nearest = (x, y)
        if(nearest != None):
            return True
    def _push_neighbors_to_heap(self, heap, x, y, seed_x, seed_y, claimed):
        for dx, dy in self.neighbors:
            nx, ny = x + dx, y + dy
            if not self.in_bounds(nx, ny):
                continue
            if self.terrain[ny, nx] != self.config.land or (nx, ny) in claimed:
                continue
            d2 = (nx - seed_x) ** 2 + (ny - seed_y) ** 2
            heapq.heappush(heap, (d2, nx, ny))

    def _sync_world_list(self):
        """Rebuild the entire world list from numpy array (call after initial generation)."""
        self._world_list = self.world.tolist()
        self._terrain_list = self.terrain.tolist()

    def _update_world_list_cell(self, x: int, y: int, value: int):
        self._world_list[y][x] = value


# -------------------------------
#  TERRAIN GENERATOR
# -------------------------------
class TerrainGenerator:
    def __init__(self, state: GameState):
        self.state = state
        self.cfg = state.config
        

    def load_from_image(self, image_path: str) -> None:
        img = Image.open(image_path).convert("L")
        if img.size != (self.cfg.width, self.cfg.height):
            img = img.resize((self.cfg.width, self.cfg.height), Image.NEAREST)
        pixels = img.load()
        for y in range(self.cfg.height):
            for x in range(self.cfg.width):
                if pixels[x, y] < 128:
                    self.state.terrain[y, x] = self.cfg.land
                else:
                    self.state.terrain[y, x] = self.cfg.water

    def generate_world(self) -> None:
        print("Loading world from image ...")
        self.state.world.fill(0)
        self.state.pressure.fill(0)
        self.state.tile_strength.fill(100)

        self.load_from_image("my_map.png")
        
        self.state._sync_world_list()
        self.place_resources()
        land_positions = np.argwhere(self.state.terrain == self.cfg.land)
        if land_positions.size == 0:
            raise RuntimeError("No land in the image – map too dark or empty.")
        print("Custom map loaded. Waiting for players.")
    def place_resources(self) -> None:

        land_pos = np.argwhere(self.state.terrain == self.cfg.land).tolist()
        resouces_placed_count = { resource_type: 0 for resource_type in RESOURCE_DEFS }
        random.shuffle(land_pos)
        for r,defi in RESOURCE_DEFS.items():
            rarity = defi["rarity"]
            total_spawn_count = int(len(land_pos) * rarity)
            for i in range(total_spawn_count):
                if not land_pos:
                    break
                x,y = land_pos.pop()

                self.state.resources[(y,x)] = {
                    "type" : r,
                    "amount" : defi["Amount"],
                    "owner": -1,
                    "extract_rate" : defi["extraction_rate"]

                }
                resouces_placed_count[r] += 1
            print(resouces_placed_count)

# -------------------------------
#  COMBAT ENGINE
# -------------------------------
class CombatEngine:
    def __init__(self, state: GameState):
        self.state = state
        self.cfg = state.config

    def attack(self, token: str, target: int) -> dict:
        if token not in self.state.players:
            return {"success": False, "error": "Unauthorized"}
        country = self.state.players[token]["country"]
        if country is None:
            return {"success": False, "error": "You must spawn a country first"}
        if target != 0 and target not in self.state.countries:
            return {"success": False, "error": "Invalid target"}
        
        # --- FIX: Check if target is actually adjacent ---
        defender_tiles = self._compute_defender_tiles(country, target)
        if not defender_tiles:
            # Only return error if target is an enemy (not neutral)
            if target != 0:
                return {
                    "success": False, 
                    "error": f"Target country {target} is not adjacent to your territory. You must share a border to attack."
                }
            # For neutral (target=0), check if there are any neutral tiles adjacent
            neutral_tiles = self._get_neutral_tiles(country)
            if not neutral_tiles:
                return {
                    "success": False, 
                    "error": "No neutral tiles adjacent to your territory to attack."
                }
        
        army = self.state.countries[country]["army"]
        
        # Only deduct army if we have valid targets
        if target == 0:
            neutral_tiles = self._get_neutral_tiles(country)
            if not neutral_tiles:
                return {"success": False, "error": "No adjacent neutral tiles to attack"}
            # Use all neutral tiles as targets
            self.state.attack_orders[country] = {
                "target": target,
                "committed": army/2,
                "remaining": army - army/2,
                "defender_tiles": neutral_tiles,
            }
        else:
            self.state.attack_orders[country] = {
                "target": target,
                "committed": army/2,
                "remaining": army - army/2,
                "defender_tiles": defender_tiles,
            }
        
        self.state.countries[country]["army"] = army/2
        
        target_state = None
        if target != 0:
            target_state = {
                "army": round(self.state.countries[target].get("army", 0), 2),
                "money": round(self.state.countries[target].get("money", 0), 2),
                "territory": self.state.territory_count.get(target, 0),
                "cities": self.state.building_counts.get(target, {}).get("city", 0),
                "factories": self.state.building_counts.get(target, {}).get("factory", 0),
                "ports": self.state.building_counts.get(target, {}).get("port", 0),
                "launchers": self.state.building_counts.get(target, {}).get("launcher", 0),
            }
        else:
            target_state = {
                "army": 0,
                "money": 0,
                "territory": 0,
                "cities": 0,
                "factories": 0,
                "ports": 0,
                "launchers": 0,
            }
        
        replay.record({
            "player": country,
            "action": f"attack:{target}",
            "tick": self.state.current_tick,
            "army": round(self.state.countries[country]["army"], 2),
            "money": round(self.state.countries[country]["money"], 2),
            "iron": round(self.state.countries[country]["resources"].get(ResourceType.IRON, 0), 2),
            "uranium": round(self.state.countries[country]["resources"].get(ResourceType.URANIUM, 0), 2),
            "territory": self.state.territory_count.get(country, 0),
            "cities": self.state.building_counts.get(country, {}).get("city", 0),
            "factories": self.state.building_counts.get(country, {}).get("factory", 0),
            "ports": self.state.building_counts.get(country, {}).get("port", 0),
            "launchers": self.state.building_counts.get(country, {}).get("launcher", 0),
            "target_player": target,
            "target_army": target_state.get("army", 0),
            "target_money": target_state.get("money", 0),
            "target_territory": target_state.get("territory", 0),
            "target_cities": target_state.get("cities", 0),
            "target_factories": target_state.get("factories", 0),
            "target_ports": target_state.get("ports", 0),
            "target_launchers": target_state.get("launchers", 0),
        })
        
        return {"success": True, "message": f"Attack ordered against {'neutral' if target == 0 else f'country {target}'}"}

    def _get_neutral_tiles(self, country: int) -> list[tuple[int, int]]:
        """Get all neutral tiles adjacent to the country."""
        tiles = []
        world = self.state.world
        terrain = self.state.terrain
        land = self.cfg.land
        
        for x, y in self.state.active_tiles:
            if world[y, x] != country:
                continue
            for dx, dy in self.state.neighbors:
                nx, ny = x + dx, y + dy
                if not self.state.in_bounds(nx, ny):
                    continue
                if terrain[ny, nx] != land:
                    continue
                if world[ny, nx] == 0:
                    tiles.append((nx, ny))
        return tiles

    def _compute_defender_tiles(self, attacker: int, target: int) -> list[tuple[int, int]]:
        tiles = []
        world = self.state.world
        terrain = self.state.terrain
        land = self.cfg.land
        for x, y in self.state.active_tiles:
            if world[y, x] != attacker:
                continue
            for dx, dy in self.state.neighbors:
                nx, ny = x + dx, y + dy
                if not self.state.in_bounds(nx, ny):
                    continue
                if terrain[ny, nx] != land:
                    continue
                if world[ny, nx] == target:
                    tiles.append((nx, ny))
        return tiles


    def naval_attack(self, token: str, target_x: int, target_y: int) -> dict:
        if token not in self.state.players:
            return {"success": False, "error": "Unauthorized"}
        country = self.state.players[token]["country"]
        if country is None:
            return {"success": False, "error": "You must spawn a country first"}

        army = self.state.countries[country]["army"]
        if army <= 0:
            return {"success": False, "error": "No army available"}

        if not self.state.in_bounds(target_x, target_y):
            return {"success": False, "error": "Invalid coordinates"}
        if self.state.terrain[target_y, target_x] != self.cfg.land:
            return {"success": False, "error": "Cannot naval invade water - target must be land"}
        target_owner = int(self.state.world[target_y, target_x])
        if target_owner == country:
            return {"success": False, "error": "Target is your own tile"}
        if not self.state.is_coastal(target_x, target_y):
            return {"success": False, "error": "Target is not a coastal tile"}

        coast_set = self.state.coastal_tiles.get(country, set())
        if not coast_set:
            return {"success": False, "error": "You have no coastal tiles"}

        # OPTIMIZATION: Create a bounding box around the target`    `
        # Only check coastal tiles within naval_range * 2 distance
        search_radius = self.cfg.naval_range * 2
        min_x = max(0, target_x - search_radius)
        max_x = min(self.cfg.width - 1, target_x + search_radius)
        min_y = max(0, target_y - search_radius)
        max_y = min(self.cfg.height - 1, target_y + search_radius)
        
        # Filter coastal tiles to only those in the bounding box
        candidates = []
        min_straight_dist = float('inf')
        
        for sx, sy in coast_set:
            # Quick bounding box check first
            if min_x <= sx <= max_x and min_y <= sy <= max_y:
                dist = math.hypot(sx - target_x, sy - target_y)
                if dist < min_straight_dist:
                    min_straight_dist = dist
                if dist <= self.cfg.naval_range * 1.5:
                    candidates.append((sx, sy))
        
        if min_straight_dist > self.cfg.naval_range * 2:
            return {
                "success": False,
                "error": f"Target too far (closest coast: {int(min_straight_dist)} tiles away, max naval range: {self.cfg.naval_range})"
            }
        
        if not candidates:
            return {"success": False, "error": "No coastal tiles within reachable distance"}

        # Sort candidates by distance (closest first for faster pathfinding)
        candidates.sort(key=lambda coord: math.hypot(coord[0] - target_x, coord[1] - target_y))
        
        # Only check top 10 closest candidates (they're most likely to find a path)
        candidates = candidates[:10]

        best_path = None
        best_dist = float('inf')

        with ThreadPoolExecutor(max_workers=20) as executor:
            futures = {executor.submit(self.state.find_water_path, start, (target_x, target_y)): start
                    for start in candidates}
            for future in as_completed(futures):
                dist, path = future.result()
                if path and dist < best_dist:
                    best_dist = dist
                    best_path = path
                    if best_dist <= 10:
                        break

        if best_path is None:
            return {"success": False, "error": "No water path found"}
        if best_dist > self.cfg.naval_range:
            return {"success": False, "error": f"Shortest water path ({best_dist} tiles) exceeds naval range ({self.cfg.naval_range})"}

        cost = max(100, army // 2)
        if cost > army:
            return {"success": False, "error": f"Not enough army (need {cost}, have {army})"}

        self.state.countries[country]["army"] -= cost
        fleet = self.state.spawn_fleet(country, best_path, isTrade=False)

        print(f"Naval invasion launched: Country {country} -> ({target_x},{target_y}) "
            f"distance={best_dist} tiles, fleet={fleet.fleet_id}, "
            f"army_cost={cost}, remaining_army={self.state.countries[country]['army']}")

        replay.record({
            "player": country,
            "action": "naval_attack",
            "tick": self.state.current_tick,
            "target_player": target_owner,
            "army": round(self.state.countries[country]["army"], 2),
            "money": round(self.state.countries[country]["money"], 2),
            "iron": round(self.state.countries[country]["resources"].get(ResourceType.IRON, 0), 2),
            "uranium": round(self.state.countries[country]["resources"].get(ResourceType.URANIUM, 0), 2),
            "territory": self.state.territory_count.get(country, 0),
            "cities": self.state.building_counts.get(country, {}).get("city", 0),
            "factories": self.state.building_counts.get(country, {}).get("factory", 0),
            "ports": self.state.building_counts.get(country, {}).get("port", 0),
            "launchers": self.state.building_counts.get(country, {}).get("launcher", 0),
        })

        return {
            "success": True,
            "fleet_id": fleet.fleet_id,
            "path": best_path,
            "distance": best_dist,
            "army_cost": cost,
            "message": f"Naval fleet dispatched! Distance: {best_dist} tiles"
        }

    def _capture_tile(self, x: int, y: int, new_owner: int):
        if self.state.terrain[y, x] != self.cfg.land:
            return
        prev_owner = int(self.state.world[y, x])
        if prev_owner == new_owner:
            return

        # Update numpy array and prebuilt world list
        self.state.world[y, x] = new_owner
        self.state._update_world_list_cell(x, y, new_owner)
        self.state.pressure[y, x] = 0
        self.state.tile_strength[y, x] = 100
        self.state.changed_tiles.add((x, y))
        self.state.update_neighbours(x, y)

        # Territory counts
        if prev_owner in self.state.territory_count:
            self.state.territory_count[prev_owner] -= 1
        if new_owner not in self.state.territory_count:
            self.state.territory_count[new_owner] = 0
        self.state.territory_count[new_owner] += 1

        # Army adjustments
        if prev_owner in self.state.countries:
            self.state.countries[prev_owner]["army"] = max(
                0, self.state.countries[prev_owner]["army"] - 3)
        if new_owner in self.state.countries:
            self.state.countries[new_owner]["army"] = min(
                self.state.countries[new_owner]["max_army"],
                self.state.countries[new_owner]["army"] + 1)

        # Coastal handling
        if self.state.is_coastal(x, y):
            if new_owner not in self.state.coastal_tiles:
                self.state.coastal_tiles[new_owner] = set()
            self.state.coastal_tiles[new_owner].add((x, y))
        if prev_owner in self.state.coastal_tiles:
            self.state.coastal_tiles[prev_owner].discard((x, y))

        # Building capture / destroy
        if (x, y) in self.state.buildings:
            if self.state.buildings[(x, y)]["owner"] != new_owner:
                self.state.buildings[(x, y)]["owner"] = new_owner
        if (x, y) in self.state.resources:
            print("fuck")
            if self.state.resources[(x, y)]["owner"] != new_owner:
                self.state.resources[(x, y)]["owner"] = new_owner

    def resolve_attacks(self) -> None:
        for attacker, order in list(self.state.attack_orders.items()):
            if not order:
                continue
            target = order["target"]
            remaining = order["remaining"]
            if remaining <= 0:
                self.state.attack_orders[attacker] = None
                continue
            
            defender_tiles = order["defender_tiles"]
            if not defender_tiles:
                self.state.attack_orders[attacker] = None
                continue
            
            # Committed army determines how many troops are used per tick
            committed = order["committed"]
            # Each tick uses a fraction of committed, but at least 1
            tick_cost = max(1, committed // 20)   # adjust divisor for balance
            tick_cost = min(tick_cost, remaining) # don't exceed remaining
            
            # Deduct from country's actual army (if they still have it)
            if attacker in self.state.countries:
                actual_army = self.state.countries[attacker]["army"]
                used = min(tick_cost, actual_army)
                self.state.countries[attacker]["army"] -= used
                # If no army left, we still continue with the order (using committed)
                # but we reduce remaining by the full tick_cost
            else:
                used = tick_cost  # fallback
            
            order["remaining"] -= tick_cost
            
            # Sort tiles by weakness
            sorted_tiles = sorted(defender_tiles,
                                key=lambda pos: (self.state.tile_strength[pos[1], pos[0]],
                                                -self.state.pressure[pos[1], pos[0]]))
            
            # Focus fire: 70% on weakest, 30% spread
            if len(sorted_tiles) > 1:
                weakest = sorted_tiles[0]
                others = sorted_tiles[1:]
                self.apply_damage(attacker, target, weakest[0], weakest[1], tick_cost * 0.7)
                if others:
                    spread = (tick_cost * 0.3) / len(others)
                    for x, y in others:
                        self.apply_damage(attacker, target, x, y, spread)
            else:
                x, y = sorted_tiles[0]
                self.apply_damage(attacker, target, x, y, tick_cost)
            
            if order["remaining"] <= 0:
                self.state.attack_orders[attacker] = None
    def resolve_attacks(self) -> None:
        for attacker in list(self.state.countries.keys()):
            order = self.state.attack_orders.get(attacker)
            if not order:
                continue
            target = order["target"]
            remaining = order["remaining"]
            if remaining <= 0:
                self.state.attack_orders[attacker] = None
                continue

            defender_tiles = self.find_defender_tiles(attacker, target)
            if not defender_tiles:
                continue

            tick_cost = max(1, order["committed"] // 50)
            tick_cost = min(tick_cost, remaining)
            order["remaining"] -= tick_cost

            attack_power = tick_cost / max(1, len(defender_tiles))
            for x, y in defender_tiles:
                self.apply_damage(attacker, target, x, y, attack_power)

            if order["remaining"] <= 0:
                self.state.attack_orders[attacker] = None
                if attacker in self.state.countries:
                    self.state.countries[attacker]["army"] = int(
                        self.state.countries[attacker]["max_army"] * 0.1
                    )

    def apply_fleet_capture(self, owner: int, x: int, y: int):
        self.state.pressure[y, x] += 50
        self.state.tile_strength[y, x] -= 50
        if self.state.terrain[y, x] == self.cfg.land:
            self._capture_tile(x, y, owner)

    def apply_damage(self, attacker: int, target: int, x: int, y: int, attack_power: float) -> None:
        if self.state.terrain[y, x] != self.state.config.land:
            return

        # Add ±20% random noise to attack power
        noisy_power = attack_power * random.uniform(0.6, 1.5)

        # # Damage building first (unchanged)
        # if (x, y) in self.state.buildings:
        #     building = self.state.buildings[(x, y)]
        #     if building["owner"] != attacker:
        #         building["hp"] -= noisy_power * 2
        #         if building["hp"] <= 0:
        #             del self.state.buildings[(x, y)]
        #             self.state.changed_tiles.add((x, y))
        #             self.state.changed_buildings.add((x,y))
        #         return

        if target == 0:
            self.state.pressure[y, x] += noisy_power * 2
            capture_threshold = 10 + random.randint(-8, 8)   # slightly variable threshold
        else:
            self.state.pressure[y, x] += noisy_power
            capture_threshold = 20 + random.randint(-3, 3)

        self.state.tile_strength[y, x] -= noisy_power

        if self.state.pressure[y, x] < capture_threshold and self.state.tile_strength[y, x] > 0:
            return

        # ---- CAPTURE ----
        self._capture_tile(x, y, attacker)

    def find_defender_tiles(self, attacker: int, target: int) -> list[tuple[int, int]]:
        tiles = []
        for x, y in self.state.active_tiles:
            if self.state.world[y, x] != attacker:
                continue
            for dx, dy in self.state.neighbors:
                nx, ny = x + dx, y + dy
                if not self.state.in_bounds(nx, ny):
                    continue
                if self.state.terrain[ny, nx] != self.state.config.land:
                    continue
                if self.state.world[ny, nx] == target:
                    tiles.append((nx, ny))
        return tiles
    def apply_missile_impact(self, owner: int, missile_type: MissileType, x: int, y: int):
        mdef = MISSILE_DEFS[missile_type]
        blast_radius = mdef["blast_radius"]
        tx, ty = int(x), int(y)
        terrain = self.state.terrain
        world = self.state.world
        config = self.cfg
        buildings = self.state.buildings
        countries = self.state.countries
        radiation = self.state.radiation
        changed_tiles = self.state.changed_tiles
        radiation_team = config.radiation_team_id

        for dy in range(-blast_radius, blast_radius + 1):
            for dx in range(-blast_radius, blast_radius + 1):
                nx, ny = tx + dx, ty + dy
                if not self.state.in_bounds(nx, ny):
                    continue
                dist = math.hypot(dx, dy)
                if dist > blast_radius:
                    continue

                current_owner = int(world[ny, nx])

                if missile_type == MissileType.NUKE:
                    # Destroy building
                    if (nx, ny) in buildings:
                        b = buildings[(nx, ny)]
                        self.state._remove_building(nx, ny)
                        if b["owner"] != owner and b["owner"] in countries:
                            countries[b["owner"]]["army"] = max(0, countries[b["owner"]]["army"] - 25)

                    if terrain[ny, nx] == config.land:
                        if current_owner != owner:
                            # Set to radiation team
                            world[ny, nx] = radiation_team
                            self.state._update_world_list_cell(nx, ny, radiation_team)
                            self.state.tile_strength[ny, nx] = 10
                            self.state.pressure[ny, nx] = 0

                            # Territory adjustment
                            if current_owner in self.state.territory_count:
                                self.state.territory_count[current_owner] -= 1
                            if radiation_team not in self.state.territory_count:
                                self.state.territory_count[radiation_team] = 0
                            self.state.territory_count[radiation_team] += 1

                            if current_owner in countries:
                                countries[current_owner]["army"] = max(0, countries[current_owner]["army"] - 20)

                    rad_ticks = int(self.state.radiation_duration * (1 - dist / (blast_radius + 1)))
                    if rad_ticks > 0:
                        key = (nx, ny)
                        if key in radiation:
                            existing = radiation[key]
                            existing["ticks"] = max(existing["ticks"], rad_ticks)
                            existing["owner"] = owner
                        else:
                            radiation[key] = {"owner": owner, "ticks": rad_ticks}
                else:  # Conventional
                    if terrain[ny, nx] == config.land and current_owner != owner:
                        if (nx, ny) in buildings:
                            self.state._remove_building(nx, ny)
                        if current_owner > 0:
                            world[ny, nx] = 0
                            self.state._update_world_list_cell(nx, ny, 0)
                            self.state.tile_strength[ny, nx] = 30
                            self.state.pressure[ny, nx] = 0

                            if current_owner in self.state.territory_count:
                                self.state.territory_count[current_owner] -= 1

                            if current_owner in countries:
                                countries[current_owner]["army"] = max(0, countries[current_owner]["army"] - 10)

                changed_tiles.add((nx, ny))

        # Update neighbours around blast area
        for dy in range(-blast_radius - 1, blast_radius + 2):
            for dx in range(-blast_radius - 1, blast_radius + 2):
                nx, ny = tx + dx, ty + dy
                if self.state.in_bounds(nx, ny):
                    self.state.update_neighbours(nx, ny)

        print(f"💥 {missile_type.value.upper()} IMPACT at ({tx},{ty}): radius={blast_radius}")


# -------------------------------
#  CONNECTION MANAGER
# -------------------------------
class ConnectionManager:
    def __init__(self):
        self.active_connections: list[WebSocket] = []

    async def connect(self, websocket: WebSocket):
        await websocket.accept()
        self.active_connections.append(websocket)

    def disconnect(self, websocket: WebSocket):
        if websocket in self.active_connections:
            self.active_connections.remove(websocket)

    async def broadcast(self, message: dict):
        dead = []
        for conn in self.active_connections:
            try:
                await conn.send_json(message)
            except Exception:
                dead.append(conn)
        for conn in dead:
            self.disconnect(conn)


# -------------------------------
#  GAME SERVER (FASTAPI)
# -------------------------------
class GameServer:
    def __init__(self, config: GameConfig | None = None):
        self.config = config or GameConfig()
        self.state = GameState(self.config)
        self.terrain = TerrainGenerator(self.state)
        self.combat = CombatEngine(self.state)
        self.manager = ConnectionManager()

        self.update_queue: asyncio.Queue = asyncio.Queue()
        self.main_loop: asyncio.AbstractEventLoop | None = None

        self.app = FastAPI()
        self.app.mount("/static", StaticFiles(directory="static"), name="static")
        self._register_routes()
        self._register_events()

    def generate_world(self) -> None:
        self.terrain.generate_world()

    def simulation_loop(self):
        last_growth = time.time()
        last_trade_sent = time.time()
        last_end_check = time.time()
        
        while True:
            if self.state.game_status == GameStatus.ACTIVE:
                self.combat.resolve_attacks()
                
                arrived_fleets = []
                for fid, fleet in list(self.state.fleets.items()):
                    if fleet.update():
                        arrived_fleets.append(fid)
                        tx, ty = fleet.path[-1]
                        if not fleet.is_trade:
                            self.combat.apply_fleet_capture(fleet.owner, tx, ty)
                        else:
                            self.state.countries[fleet.owner]["money"] += 2000
                
                for fid in arrived_fleets:
                    if fid in self.state.fleets:
                        del self.state.fleets[fid]
                
                arrived_missiles = []
                for mid, missile in list(self.state.missiles.items()):
                    if missile.update():
                        arrived_missiles.append(mid)
                        tx, ty = missile.path[-1]
                        self.combat.apply_missile_impact(missile.owner, missile.missile_type, tx, ty)
                
                for mid in arrived_missiles:
                    if mid in self.state.missiles:
                        del self.state.missiles[mid]
                
                expired = []
                for pos, rad in list(self.state.radiation.items()):
                    rad["ticks"] -= 1
                    if rad["ticks"] <= 0:
                        expired.append(pos)
                
                for pos in expired:
                    if pos in self.state.radiation:
                        del self.state.radiation[pos]
                
                now = time.time()
                if now - last_growth > 0.1:
                    self.state.update_country_stats()
                    last_growth = now
            
            now = time.time()
            if now - last_end_check > 5.0 and self.state.game_status == GameStatus.ACTIVE:
                if self.state.check_end_conditions():
                    if self.main_loop:
                        asyncio.run_coroutine_threadsafe(
                            self.manager.broadcast({
                                "type": "game_ended",
                                "winner": self.state.winner_country_id,
                                "scores": self.state.final_scores
                            }),
                            self.main_loop
                        )
                last_end_check = now
            
            if self.state.game_status == GameStatus.WAITING:
                if time.time() - self.state.lobby_start_time > self.config.lobby_timeout_seconds:
                    active_players = [p for p in self.state.players.values() if p["country"] is not None]
                    if len(active_players) >= self.config.min_players_to_start:
                        print(f"Lobby timeout reached, auto-starting game...")
                        self.state.start_game()
                        if self.main_loop:
                            asyncio.run_coroutine_threadsafe(
                                self.manager.broadcast({
                                    "type": "game_started",
                                    "message": "Game started"
                                }),
                                self.main_loop
                            )
            
            if self.state.game_status != GameStatus.WAITING:
                self.publish_updates()
            
            self.state.current_tick += 1
            elapsed = time.time() - now
            time.sleep(max(0, self.config.simulation_interval - elapsed))

    def publish_updates(self):
        if not self.main_loop:
            return

        tile_updates = [(x, y, int(self.state.world[y, x])) for x, y in self.state.changed_tiles]
        self.state.changed_tiles.clear()

        fleet_updates = [(fid, fleet.owner, fleet.current_position()[0], fleet.current_position()[1])
                         for fid, fleet in self.state.fleets.items()]

        missile_updates = [(mid, m.owner, m.current_position()[0], m.current_position()[1], m.missile_type.value)
                           for mid, m in self.state.missiles.items()]

        if tile_updates or fleet_updates or missile_updates:
            data = {"tiles": tile_updates, "fleets": fleet_updates, "missiles": missile_updates}
            asyncio.run_coroutine_threadsafe(self.update_queue.put(data), self.main_loop)

    async def broadcast_updates(self):
        while True:
            data = await self.update_queue.get()
            if data and (data.get("tiles") or data.get("fleets") or data.get("missiles")):
                await self.manager.broadcast(data)

    def _register_events(self):
        @self.app.on_event("startup")
        async def startup():
            self.main_loop = asyncio.get_running_loop()
            asyncio.create_task(self.broadcast_updates())
            print("Broadcaster started.")

    def _register_routes(self):
        @self.app.get("/")
        async def home():
            with open("templates/login.html", encoding="utf-8") as f:
                return HTMLResponse(f.read())

        @self.app.get("/game")
        async def game():
            import os
            js_path = "static/game.js"
            if os.path.exists(js_path):
                version = int(os.path.getmtime(js_path))
            else:
                version = int(time.time())
            
            with open("templates/game.html", encoding="utf-8") as f:
                html = f.read()
            
            html = html.replace("{{ version }}", str(version))
            return HTMLResponse(html)
        
        @self.app.post("/build")
        async def build(data: dict = Body(...)):
            token = data.get("token")
            x = int(data.get("x"))
            y = int(data.get("y"))
            building_type_str = data.get("type")

            if token not in self.state.players:
                return {"success": False, "error": "Invalid token"}
            country = self.state.players[token]["country"]
            if country is None:
                return {"success": False, "error": "You must spawn a country first"}

            if not self.state.in_bounds(x, y):
                return {"success": False, "error": "Invalid coordinates"}
            if self.state.terrain[y, x] != self.config.land:
                return {"success": False, "error": "Must build on land"}
            if self.state.world[y, x] != country:
                return {"success": False, "error": "You don't own this tile"}
            if building_type_str == "port" and (x, y) not in self.state.coastal_tiles.get(country, set()):
                return {"success": False, "error": "Port should be built on a coastal tile"}
            if (x, y) in self.state.buildings:
                return {"success": False, "error": "Tile already has a building"}

            try:
                btype = BuildingType(building_type_str)
            except ValueError:
                return {"success": False, "error": "Invalid building type" + building_type_str}

            bdef = BUILDING_DEFS[btype]
            money = self.state.countries[country]["money"]
            resources = self.state.countries[country]["resources"]
            print(resources)
            if money < bdef["cost"]:
                return {"success": False, "error": f"Not enough money (cost: {bdef['cost']})"}
            needed_resources = bdef["needed_resources"]
            for resource_key, needed_amount in needed_resources.items():
                if resources.get(resource_key, 0) < needed_amount:
                    return {
                        "success": False, 
                        "error": f"Not enough {resource_key} (need: {needed_amount}, have: {resources.get(resource_key, 0)})"
                    }
            self.state.countries[country]["money"] -= bdef["cost"]
            self.state.countries[country]["resources"] =  {key: resources[key] - bdef["needed_resources"][key] for key in resources}
            self.state._add_building(x, y, btype, country, bdef["hp"])
            self.state.changed_tiles.add((x, y))  
            self.state.changed_buildings.add((x, y))  
            
            building_msg = {
                "buildings": [{
                    "x": x,
                    "y": y,
                    "type": btype.value,
                    "owner": country,
                    "hp": bdef["hp"]
                }]
            }
            asyncio.run_coroutine_threadsafe(
                self.manager.broadcast(building_msg),
                self.main_loop
            )
            replay.record({
                "player": country,
                "action": f"build:{building_type_str}",
                "tick": self.state.current_tick,
                "army": round(self.state.countries[country]["army"], 2),
                "money": round(self.state.countries[country]["money"], 2),
                "iron": round(self.state.countries[country]["resources"].get(ResourceType.IRON, 0), 2),
                "uranium": round(self.state.countries[country]["resources"].get(ResourceType.URANIUM, 0), 2),
                "territory": self.state.territory_count.get(country, 0),
                "cities": self.state.building_counts.get(country, {}).get("city", 0),
                "factories": self.state.building_counts.get(country, {}).get("factory", 0),
                "ports": self.state.building_counts.get(country, {}).get("port", 0),
                "launchers": self.state.building_counts.get(country, {}).get("launcher", 0),
            })
            print(f"Player {country} built {btype.value} at ({x},{y})")
            return {"success": True, "message": f"{btype.value} built!"}

        @self.app.get("/buildings")
        async def get_buildings():
            return {"buildings": [
                {"x": x, "y": y, "type": b["type"].value, "owner": b["owner"], "hp": b["hp"]}
                for (x, y), b in self.state.buildings.items()
            ]}

        @self.app.get("/armies")
        async def get_armies():
            return {
                str(cid): {"army": int(s["army"]), "max_army": int(s["max_army"])}
                for cid, s in self.state.countries.items()
            }

        @self.app.get("/moneys")
        async def get_moneys():
            return {
                str(cid): {"money": int(s["money"])}
                for cid, s in self.state.countries.items()
            }
        
        @self.app.get("/resources")
        async def get_resources():
            return {
                str(cid): {"resources": s["resources"]}
                for cid, s in self.state.countries.items()
            }
        @self.app.get("/world")
        async def get_world():
            building_list = [
                {"x": x, "y": y, "type": b["type"].value, "owner": b["owner"], "hp": b["hp"]}
                for (x, y), b in self.state.buildings.items()
            ]
            resource_list = [
                {"x": x, "y": y, "type": b["type"].value ,"owner": b["owner"]}
                for (x, y), b in self.state.resources.items()
            ]
            return {
                "width": self.config.width,
                "height": self.config.height,
                "owners": self.state._world_list,
                "terrain": self.state._terrain_list,
                "buildings": building_list,
                "resources": resource_list
            }

        @self.app.get("/diff")
        async def get_diff():
            tile_updates = [[x, y, int(self.state.world[y, x])] for x, y in self.state.changed_tiles]
            self.state.changed_tiles.clear()

            fleet_updates = [[fid, fleet.owner, fleet.current_position()[0], fleet.current_position()[1]]
                             for fid, fleet in self.state.fleets.items()]

            missile_updates = [[mid, m.owner, m.current_position()[0], m.current_position()[1], m.missile_type.value]
                               for mid, m in self.state.missiles.items()]
            building_updates = [self.state.buildings[x,y] for x , y in self.state.changed_buildings]
            self.state.changed_buildings.clear()
            return {"tiles": tile_updates, "fleets": fleet_updates, "missiles": missile_updates, "buildings":building_updates}

        @self.app.post("/join")
        async def join_player(data: dict = Body(...)):
            secret = data.get("secret")
            name = data.get("name", "Unnamed")
            if secret != self.config.join_secret and secret != self.config.admin_secret:
                return {"success": False, "error": "Invalid game secret"}
            token = secrets.token_urlsafe(16)
            self.state.players[token] = {"country": None, "name": name}
            print(f"Player '{name}' joined with token {token[:8]}...")
            return {"success": True, "token": token}

        @self.app.post("/spawn")
        async def spawn_country(data: dict = Body(...)):
            token = data.get("token")
            x = int(data.get("x"))
            y = int(data.get("y"))
            
            if token not in self.state.players:
                return {"success": False, "error": "Invalid token"}
            if self.state.players[token]["country"] is not None:
                return {"success": False, "error": "You already have a country"}
            
            result = self.state.create_country(token, x, y)
            
            if result["success"]:
                country_id = result["country"]
                
                owned_tiles = []
                for ty in range(self.config.height):
                    for tx in range(self.config.width):
                        if self.state.world[ty, tx] == country_id:
                            owned_tiles.append([tx, ty, country_id])
                
                if self.main_loop and owned_tiles:
                    asyncio.run_coroutine_threadsafe(
                        self.manager.broadcast({
                            "type": "spawn",
                            "country": country_id,
                            "x": x,
                            "y": y,
                            "tiles": owned_tiles,
                            "total_tiles": len(owned_tiles)
                        }),
                        self.main_loop
                    )
                    
                    print(f"🏴 Country {country_id} spawned with {len(owned_tiles)} tiles")
            
            return result

        @self.app.post("/attack")
        async def attack(data: dict = Body(...)):
            token = data.get("token")
            # Naval attack if x,y present
            if "x" in data and "y" in data:
                target_x = int(data["x"])
                target_y = int(data["y"])
                return self.combat.naval_attack(token, target_x, target_y)
            target = int(data.get("target"))

            return self.combat.attack(token, target)

        @self.app.websocket("/ws")
        async def ws_endpoint(websocket: WebSocket):
            await self.manager.connect(websocket)
            try:
                while True:
                    await websocket.receive_text()
            except WebSocketDisconnect:
                self.manager.disconnect(websocket)

        @self.app.post("/launch_missile")
        async def launch_missile(data: dict = Body(...)):
            token = data.get("token")
            target_x = int(data.get("x"))
            target_y = int(data.get("y"))
            missile_type_str = data.get("missile_type", "conventional")

            if token not in self.state.players:
                return {"success": False, "error": "Invalid token"}
            country = self.state.players[token]["country"]
            if country is None:
                return {"success": False, "error": "You must spawn a country first"}

            try:
                mtype = MissileType(missile_type_str)
            except ValueError:
                return {"success": False, "error": f"Invalid missile type: {missile_type_str}"}

            mdef = MISSILE_DEFS[mtype]
            money = self.state.countries[country]["money"]
            resources = self.state.countries[country]["resources"]

            if money < mdef["cost"]:
                return {"success": False, "error": f"Not enough money (cost: {mdef['cost']})"}
            needed_resources = mdef["needed_resources"]
            for resource_key, needed_amount in needed_resources.items():
                if resources.get(resource_key, 0) < needed_amount:
                    return {
                        "success": False, 
                        "error": f"Not enough {resource_key} (need: {needed_amount}, have: {resources.get(resource_key, 0)})"
                    }
            
            self.state.countries[country]["money"] -= mdef["cost"]
            self.state.countries[country]["resources"] =  {key: resources[key] - mdef["needed_resources"][key] for key in resources}
            launcher_pos = None
            min_distance = float('inf')
            
            for (bx, by), b in self.state.buildings.items():
                if b["owner"] == country and b["type"] == BuildingType.LAUNCHER:
                    distance = math.hypot(bx - target_x, by - target_y)
                    if distance < min_distance:
                        min_distance = distance
                        launcher_pos = (bx, by)
            if launcher_pos is None: 
                return {"success": False, "error": "You need a Launcher building to fire missiles"}

            if not self.state.in_bounds(target_x, target_y):
                return {"success": False, "error": "Invalid target coordinates"}
            if mtype == MissileType.CONVENTIONAL and self.state.terrain[target_y, target_x] != self.config.land:
                return {"success": False, "error": "Conventional missiles must target land"}
            if math.hypot(launcher_pos[0] - target_x, launcher_pos[1] - target_y) < 5:
                return {"success": False, "error": "Target too close (minimum range: 5 tiles)"}

            self.state.countries[country]["money"] -= mdef["cost"]
            missile = self.state.spawn_missile(country, mtype, launcher_pos, (target_x, target_y))
            print(f"Country {country} launched {mtype.value} #{missile.missile_id} -> ({target_x},{target_y}) cost={mdef['cost']}")
            return {
                "success": True,
                "missile_id": missile.missile_id,
                "missile_type": mtype.value,
                "message": f"{mtype.value} missile launched!"
            }
        @self.app.get("/country_state/{country_id}")
        async def country_state(country_id: int):

            country = self.state.countries.get(country_id)

            if not country:
                return {"error": "invalid country"}

            return {
                "army": country["army"],
                "max_army": country["max_army"],
                "money": country["money"],

                "territory": self.state.territory_count.get(country_id, 0),

                "cities": self.state.building_counts.get(country_id, {}).get("city", 0),
                "factories": self.state.building_counts.get(country_id, {}).get("factory", 0),
                "ports": self.state.building_counts.get(country_id, {}).get("port", 0),
                "launchers": self.state.building_counts.get(country_id, {}).get("launcher", 0),

                "coastal": bool(self.state.coastal_tiles.get(country_id))
            }
        @self.app.post("/spawn_bot")
        async def spawn_bot(data: dict = Body(...)):
            try:
                token = data["token"]

                free_tiles = np.argwhere(
                    (self.state.world == 0) &
                    (self.state.terrain == 1)
                )

                if free_tiles.shape[0] == 0:
                    return {"success": False, "reason": "no_free_tiles"}

                idx = random.randrange(free_tiles.shape[0])
                y, x = free_tiles[idx]

                result = self.state.create_country(token, int(x), int(y))

                return {
                    "success": True,
                    "country": result.get("country"),
                }

            except Exception as e:
                return {
                    "success": False,
                    "error": str(e)
                }
        @self.app.post("/build_auto")
        async def build_auto(data: dict = Body(...)):
            token = data.get("token")
            building_type_str = data.get("type")
            
            if token not in self.state.players:
                return {"success": False, "error": "Invalid token"}
            
            country = self.state.players[token]["country"]
            if country is None:
                return {"success": False, "error": "You must spawn a country first"}
            
            try:
                btype = BuildingType(building_type_str)
            except ValueError:
                return {"success": False, "error": f"Invalid building type: {building_type_str}"}
            
            bdef = BUILDING_DEFS[btype]
            
            money = self.state.countries[country]["money"]
            if money < bdef["cost"]:
                return {"success": False, "error": f"Not enough money (need: {bdef['cost']}, have: {money})"}
            
            # Check resources
            resources = self.state.countries[country]["resources"]
            needed_resources = bdef["needed_resources"]
            for resource_key, needed_amount in needed_resources.items():
                if resources.get(resource_key, 0) < needed_amount:
                    return {
                        "success": False, 
                        "error": f"Not enough {resource_key.value} (need: {needed_amount}, have: {resources.get(resource_key, 0)})"
                    }
            
            valid_tiles = []
            world = self.state.world
            terrain = self.state.terrain
            buildings = self.state.buildings
            coastal_tiles = self.state.coastal_tiles.get(country, set())
            
            owned_tiles = np.argwhere(world == country)
            
            for y, x in owned_tiles:
                if terrain[y, x] != self.config.land:
                    continue
                
                if (int(x), int(y)) in buildings:
                    continue
                
                if btype == BuildingType.PORT:
                    if (int(x), int(y)) not in coastal_tiles:
                        continue
                elif btype == BuildingType.IRON_MINE:
                    if not self.state.getNearestResource((int(x), int(y)), ResourceType.IRON, 10):
                        continue
                elif btype == BuildingType.URANIUM_MINE:
                    if not self.state.getNearestResource((int(x), int(y)), ResourceType.URANIUM, 10):
                        continue
                
                valid_tiles.append((int(x), int(y)))
            
            if not valid_tiles:
                return {"success": False, "error": f"No valid tile found for {btype.value}"}
            
            def tile_score(tile):
                x, y = tile
                score = 0

                for dx, dy in self.state.neighbors:
                    nx, ny = x + dx, y + dy
                    if self.state.in_bounds(nx, ny) and world[ny, nx] == country:
                        score += 1
                return score
            
            valid_tiles.sort(key=tile_score, reverse=True)
            
            x, y = valid_tiles[0]
            
            self.state.countries[country]["money"] -= bdef["cost"]
            resources = self.state.countries[country]["resources"]
            self.state.countries[country]["resources"] = {
                key: resources[key] - bdef["needed_resources"][key] 
                for key in resources
            }
            self.state._add_building(x, y, btype, country, bdef["hp"])
            self.state.changed_tiles.add((x, y))
            self.state.changed_buildings.add((x, y))

            building_msg = {
                "buildings": [{
                    "x": x,
                    "y": y,
                    "type": btype.value,
                    "owner": country,
                    "hp": bdef["hp"]
                }]
            }
            if self.main_loop:
                asyncio.run_coroutine_threadsafe(
                    self.manager.broadcast(building_msg),
                    self.main_loop
                )
            
            # Record replay
            money = round(money, 2)
            resources = {
                resource.name: round(amount, 2)
                for resource, amount in self.state.countries[country]["resources"].items()
            }
            building_counts = self.state.building_counts.get(country, {})
            
            replay.record({
                "player": country,
                "action": f"build_auto:{btype.value}",
                "army": round(self.state.countries[country]["army"], 2),
                "money": money,
                "iron": resources.get("IRON", 0),
                "uranium": resources.get("URANIUM", 0),
                "territory": self.state.territory_count.get(country, 0),
                "cities": building_counts.get("city", 0),
                "factories": building_counts.get("factory", 0),
                "launchers": building_counts.get("launcher", 0),
                "ports": building_counts.get("port", 0),
                "tick": self.state.current_tick
            })
            
            print(f"Player {country} auto-built {btype.value} at ({x},{y})")
            return {
                "success": True,
                "message": f"{btype.value} built at ({x},{y})!",
                "x": x,
                "y": y,
                "building_type": btype.value
            }



        @self.app.post("/admin/start")
        async def admin_start(data: dict = Body(...)):
            token = data.get("token")
            secret = data.get("secret")
            
            # First validate token
            if token not in self.state.players:
                return {"success": False, "error": "Invalid token"}
            
            # Then check admin secret
            if secret != self.config.admin_secret:
                return {"success": False, "error": "Invalid admin secret"}
            
            if self.state.game_status != GameStatus.WAITING:
                return {"success": False, "error": f"Game already {self.state.game_status.value}"}
            
            result = self.state.start_game()
            if result["success"] and self.main_loop:
                await self.manager.broadcast({
                    "type": "game_started",
                    "message": "Game started by admin"
                })
            return result

        @self.app.post("/admin/end")
        async def admin_end(data: dict = Body(...)):
            token = data.get("token")
            secret = data.get("secret")
            
            # First validate token
            if token not in self.state.players:
                return {"success": False, "error": "Invalid token"}
            
            # Then check admin secret
            if secret != self.config.admin_secret:
                return {"success": False, "error": "Invalid admin secret"}
            
            if self.state.game_status != GameStatus.ACTIVE:
                return {"success": False, "error": "Game is not active"}
            
            result = self.state.end_game()
            if result["success"] and self.main_loop:
                await self.manager.broadcast({
                    "type": "game_ended",
                    "winner": result.get("winner"),
                    "scores": result.get("scores")
                })
            return result

        # ============================================================
        # OPTIONAL: ADMIN LOGIN ENDPOINT
        # ============================================================

        @self.app.post("/admin/login")
        async def admin_login(data: dict = Body(...)):
            secret = data.get("secret")
            
            if secret != self.config.admin_secret:
                return {"success": False, "error": "Invalid admin secret"}
            
            # Create a special admin token or mark existing token as admin
            token = secrets.token_urlsafe(32)
            
            # Store admin token (you might want a separate storage)
            if not hasattr(self.state, 'admin_tokens'):
                self.state.admin_tokens = set()
            self.state.admin_tokens.add(token)
            
            return {
                "success": True,
                "admin_token": token,
                "message": "Admin authenticated successfully"
            }

        @self.app.post("/admin/check")
        async def admin_check(data: dict = Body(...)):
            token = data.get("token")
            
            # Check if token is admin
            if token not in self.state.players:
                return {"success": False, "error": "Invalid token"}
            
            # Check if user has admin privileges (you might want to store this in player data)
            is_admin = self.state.players[token].get("is_admin", False)
            print(is_admin)
            
            return {
                "success": True,
                "is_admin": is_admin
            }

        @self.app.get("/game/status")
        async def game_status():
            status = self.state.game_status.value
            players_with_country = sum(1 for p in self.state.players.values() if p["country"] is not None)
            data = {
                "status": status,
                "players": len(self.state.players),
                "active_players": players_with_country,
                "min_players_to_start": self.config.min_players_to_start,
            }
            if status == GameStatus.ACTIVE.value and self.state.game_start_time:
                elapsed = time.time() - self.state.game_start_time
                remaining = max(0, self.state.game_duration_seconds - elapsed)
                data["time_remaining"] = int(remaining)
            if status == GameStatus.ENDED.value:
                data["winner"] = self.state.winner_country_id
                data["scores"] = self.state.final_scores
            return data

    def run(self):
        i = int(input("port: "))
        global replay
        replay = ReplayManager(f"replay{i}.csv")
        self.generate_world()
        threading.Thread(target=self.simulation_loop, daemon=True).start()
        uvicorn.run(self.app, host="0.0.0.0", port=i)


if __name__ == "__main__":
    GameServer().run()