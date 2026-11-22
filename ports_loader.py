import csv
import os
import re
import requests

UN_CSV = "unlocode_ports.csv"
UN_URL = "https://raw.githubusercontent.com/datasets/un-locode/main/data/code-list.csv"

def parse_coords(s):
    m = re.match(r"^(\d{2})(\d{2})([NS])\s+(\d{3})(\d{2})([EW])$", (s or "").strip())
    if not m:
        return None, None
    lat = int(m.group(1)) + int(m.group(2)) / 60.0
    if m.group(3) == "S":
        lat = -lat
    lon = int(m.group(4)) + int(m.group(5)) / 60.0
    if m.group(6) == "W":
        lon = -lon
    return round(lat, 4), round(lon, 4)

def load_all(register_port, extra_ports, stats, ports_by_id, has_searoute):
    if not os.path.exists(UN_CSV):
        print("[*] Downloading global UN/LOCODE seaports (~10,000+ world ports)...")
        try:
            r = requests.get(UN_URL, timeout=45)
            if r.status_code == 200 and len(r.content) > 500000:
                with open(UN_CSV, "wb") as f:
                    f.write(r.content)
                print(f"[+] Downloaded {UN_CSV} ({len(r.content)//1024} KB)")
            else:
                print(f"[!] Download status {r.status_code}, using built-in ports.")
        except Exception as e:
            print(f"[!] Download error ({e}), using built-in ports.")

    if os.path.exists(UN_CSV):
        with open(UN_CSV, "r", encoding="utf-8", errors="ignore") as f:
            for row in csv.DictReader(f):
                func = (row.get("Function") or "").strip()
                if not func.startswith("1"):
                    continue
                lat, lon = parse_coords(row.get("Coordinates"))
                if lat is None:
                    continue
                cc = (row.get("Country") or "").strip().upper()
                loc = (row.get("Location") or "").strip().upper()
                name = (row.get("NameWoDiacritics") or row.get("Name") or "").strip()
                if not cc or not loc or not name:
                    continue
                pid = f"{cc}{loc}"
                register_port(pid, name, cc, lat, lon, 9.0, False, 0.0, [pid, f"{cc} {loc}", name.upper()])

    for pid, name, country, lat, lon, rad, roro, md, aliases in extra_ports:
        register_port(pid, name, country, lat, lon, rad, roro, md, aliases + [name.upper()])

    stats["ports_loaded"] = len(ports_by_id)
    mode = "ON" if has_searoute else "FALLBACK"
    print(f"[+] Indexed {stats['ports_loaded']} global seaports in spatial grid (searoute={mode})")
