from dataclasses import dataclass

@dataclass
class Tile:
    owner: int = 0      # 0 = neutral
    terrain: int = 0    # 0 = plains