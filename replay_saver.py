import csv
import os
import json


class ReplayManager:
    HEADER = [
        "player",
        "action",
        "army",
        "money",
        "iron",
        "uranium",
        "territory",
        "cities",
        "factories",
        "ports",
        "launchers",
        "tick",
        "target_player",
        "target_army",
        "target_money",
        "target_territory",
        "target_cities",
        "target_factories",
        "target_ports",
        "target_launchers",
        "all_players_json",
    ]

    def __init__(self, filename="replay.csv"):
        self.filename = filename

        needs_header = (
            not os.path.exists(filename)
            or os.path.getsize(filename) == 0
        )

        if needs_header:
            with open(filename, "w", newline="", encoding="utf8") as f:
                writer = csv.DictWriter(f, fieldnames=self.HEADER)
                writer.writeheader()

    def record(self, data):
        """Record immediately to file (real-time)."""
        row = {key: data.get(key, 0) for key in self.HEADER}
        
        with open(self.filename, "a", newline="", encoding="utf8") as f:
            writer = csv.DictWriter(f, fieldnames=self.HEADER)
            writer.writerow(row)

    def save(self):
        """Just for compatibility - already saving in real-time."""
        print(f"✅ Replay saved to {self.filename}")

    def load(self):
        records = []
        with open(self.filename, "r", encoding="utf8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                if row.get("all_players_json"):
                    try:
                        row["all_players"] = json.loads(row["all_players_json"])
                    except:
                        row["all_players"] = {}
                records.append(row)
        return records