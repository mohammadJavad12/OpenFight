import random
from engine.world import Tile

WIDTH = 64
HEIGHT = 64

tiles = [
    [Tile() for _ in range(WIDTH)]
    for _ in range(HEIGHT)
]

def generate_world():
    for y in range(HEIGHT):
        for x in range(WIDTH):
            tiles[y][x].owner = 0

    # Player spawn
    for y in range(20, 25):
        for x in range(10, 15):
            tiles[y][x].owner = 1

    # AI spawn
    for y in range(35, 40):
        for x in range(45, 50):
            tiles[y][x].owner = 2