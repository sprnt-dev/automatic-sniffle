import asyncio
import csv
import io
import json
import math
import os
import re
import socket
import sqlite3
import threading
import time
from collections import Counter
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse
import requests
import fleet_views

try:
    import searoute as sr
    HAS_SEAROUTE = True
except Exception:
    HAS_SEAROUTE = False

AISSTREAM_KEY = os.environ.get("AISSTREAM_API_KEY", "").strip()
GEMINI_KEY = os.environ.get("GEMINI_API_KEY", "").strip()
EXA_KEY = os.environ.get("EXA_API_KEY", "").strip()
PORT = int(os.environ.get("PORT", "8080"))

DB_PATH = "port_intel_v2.db"
WPI_CSV = "world_ports.csv"
WPI_URL = "https://msi.nga.mil/api/publications/download?type=view&key=16920959/SFH00000/UpdatedPub150.csv"

# Global bounding box by default; set CORRIDOR_ONLY=1 to focus on Med/Red Sea/West Africa
BOUNDING_BOXES = (
    [[[12.0, 12.0], [47.5, 44.0]], [[-2.0, -10.0], [8.5, 11.0]]]
    if os.environ.get("CORRIDOR_ONLY") == "1"
    else [[[-90.0, -180.0], [90.0, 180.0]]]
)

# Built-in core ports + extra Turkish/Red Sea/African aliases (merged on top of NGA 3,800+ ports)
EXTRA_PORTS = [
    ("TRDRC", "Derince (Safiport)", "TR", 40.75, 29.83, 10, True, 14.5, ["TRDRC", "DERINCE", "SAFIPORT"]),
    ("TRGEM", "Gemlik (Gemport / Borusan)", "TR", 40.43, 29.13, 10, True, 14.0, ["TRGEM", "GEMLIK", "BORUSAN", "GEMPORT", "MUDANYA"]),
    ("TRIZT", "Izmit / Gebze / Diliskelesi", "TR", 40.75, 29.62, 14, True, 14.0, ["TRIZT", "TRDIL", "TRGEB", "TRDER", "TRYAR", "IZMIT", "GEBZE", "DILISKELESI", "DILOVASI", "HEREKE", "YARIMCA", "KORFEZ"]),
    ("TRIST", "Istanbul / Ambarli", "TR", 40.96, 28.88, 12, True, 15.0, ["TRIST", "TRAMR", "TRAMB", "ISTANBUL", "AMBARLI", "AHIRKAPI"]),
    ("TRTUZ", "Tuzla / Yalova", "TR", 40.78, 29.26, 9, True, 12.0, ["TRTUZ", "TRYAL", "TUZLA", "YALOVA", "PENDIK"]),
    ("TRBDM", "Bandirma", "TR", 40.36, 27.97, 10, True, 12.0, ["TRBDM", "BANDIRMA"]),
    ("TRTEK", "Tekirdag / Asyaport", "TR", 40.96, 27.72, 14, True, 15.0, ["TRTEK", "TRMRE", "TEKIRDAG", "MARMARA EREGLISI", "MARTAS", "ASYAPORT"]),
    ("JOAQB", "Aqaba", "JO", 29.51, 35.00, 12, True, 15.0, ["JOAQB", "AQABA", "EL AKABA"]),
    ("SAJED", "Jeddah Islamic Port", "SA", 21.46, 39.15, 14, True, 16.0, ["SAJED", "JEDDAH"]),
    ("EGPSD", "Port Said", "EG", 31.26, 32.32, 14, True, 16.0, ["EGPSD", "PORT SAID", "SUEZ"]),
    ("EGSUZ", "Suez", "EG", 29.93, 32.55, 14, True, 16.0, ["EGSUZ", "SUEZ", "AIN SUKHNA"]),
    ("NGLOS", "Lagos / Apapa / Tin Can", "NG", 6.42, 3.38, 15, True, 13.5, ["NGLOS", "NGAPP", "LAGOS", "APAPA", "TIN CAN"]),
    ("NGLEK", "Lekki Deep Sea Port", "NG", 6.42, 3.96, 12, True, 16.5, ["NGLEK", "LEKKI"]),
    ("NGONN", "Onne / Port Harcourt", "NG", 4.68, 7.15, 15, True, 12.0, ["NGONN", "NGPHC", "ONNE", "PORT HARCOURT"]),
    ("TGLFW", "Lome", "TG", 6.13, 1.29, 13, True, 15.0, ["TGLFW", "LOME"]),
    ("BJCOO", "Cotonou", "BJ", 6.34, 2.43, 12, True, 13.0, ["BJCOO", "COTONOU"]),
    ("GHTEM", "Tema", "GH", 5.62, 0.01, 13, True, 16.0, ["GHTEM", "TEMA"]),
    ("SIKOP", "Koper", "SI", 45.55, 13.73, 10, True, 15.0, ["SIKOP", "KOPER"]),
    ("ITTRS", "Trieste", "IT", 45.64, 13.76, 10, True, 16.0, ["ITTRS", "TRIESTE"]),
    ("GRPIR", "Piraeus", "GR", 37.93, 23.62, 12, True, 16.0, ["GRPIR", "PIRAEUS"]),
    ("ROCND", "Constanta", "RO", 44.14, 28.66, 13, True, 16.0, ["ROCND", "CONSTANTA"]),
]

CLUSTERS = {
    "CLUSTER:MARMARA": {
        "id": "CLUSTER:MARMARA", "name": "All Marmara Ports (Derince, Gemlik, Izmit, Istanbul, Bandirma, Tekirdag)",
        "country": "TR", "lat": 40.72, "lon": 28.80, "port_ids": {"TRDRC", "TRGEM", "TRIZT", "TRIST", "TRTUZ", "TRBDM", "TRTEK"},
        "aliases": ["MARMARA", "TRDRC", "DERINCE", "TRGEM", "GEMLIK", "TRIZT", "IZMIT", "GEBZE", "DILISKELESI", "TRIST", "TRAMR", "AMBARLI", "TRBDM", "BANDIRMA", "TRTEK", "TEKIRDAG"],
    },
    "CLUSTER:DERINCE_GEMLIK": {
        "id": "CLUSTER:DERINCE_GEMLIK", "name": "Derince & Gemlik Only (Marmara RoRo/Breakbulk)",
        "country": "TR", "lat": 40.60, "lon": 29.45, "port_ids": {"TRDRC", "TRGEM", "TRIZT"},
        "aliases": ["TRDRC", "DERINCE", "SAFIPORT", "TRGEM", "GEMLIK", "BORUSAN", "GEMPORT", "TRIZT", "IZMIT", "GEBZE", "DILISKELESI"],
    },
    "CLUSTER:WEST_AFRICA": {
        "id": "CLUSTER:WEST_AFRICA", "name": "West Africa Hub (Lagos, Lekki, Lome, Cotonou, Tema, Onne)",
        "country": "WA", "lat": 6.10, "lon": 2.40, "port_ids": {"NGLOS", "NGLEK", "NGONN", "TGLFW", "BJCOO", "GHTEM"},
        "aliases": ["NGLOS", "LAGOS", "APAPA", "NGLEK", "LEKKI", "TGLFW", "LOME", "BJCOO", "COTONOU", "GHTEM", "TEMA", "NGONN", "ONNE"],
    },
    "CLUSTER:RED_SEA": {
        "id": "CLUSTER:RED_SEA", "name": "North Red Sea (Aqaba, Suez, Jeddah)",
        "country": "RS", "lat": 27.50, "lon": 35.00, "port_ids": {"JOAQB", "EGSUZ", "EGPSD", "SAJED"},
        "aliases": ["JOAQB", "AQABA", "EGSUZ", "SUEZ", "SAJED", "JEDDAH"],
    },
}

NAV_STATUS_MAP = {
    0: "Underway (Engine)", 1: "At Anchor", 2: "Not Under Command", 3: "Restricted Maneuver",
    4: "Constrained by Draught", 5: "Moored", 6: "Aground", 7: "Fishing", 8: "Sailing", 15: "Undefined",
}

PORTS_BY_ID = {}
PORT_GRID = {}       # (int_lat, int_lon) -> list of port dicts
ALIAS_TO_PID = {}    # UPPER alias / UNLOCODE -> port_id
VESSELS = {}         # In-memory hot table keyed by mmsi
DIRTY_MMSIS = set()
PENDING_CALLS = []   # ("OPEN"|"CLOSE", data)
PENDING_TRACKS = []
LAST_TRACK_TS = {}
SEAROUTE_CACHE = {}

MEM_LOCK = threading.Lock()
DB_LOCK = threading.Lock()
STATS = {"messages": 0, "connected": False, "ports_loaded": 0, "exa_spend": 0.0}


def haversine_nm(lat1, lon1, lat2, lon2):
    R = 3440.065
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp = math.radians(lat2 - lat1)
    dl = math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * R * math.asin(min(1.0, math.sqrt(a)))


def sea_distance_nm(lat1, lon1, lat2, lon2):
    key = (round(lat1 * 2) / 2, round(lon1 * 2) / 2, round(lat2 * 2) / 2, round(lon2 * 2) / 2)
    if key in SEAROUTE_CACHE:
        return SEAROUTE_CACHE[key]
    dist = None
    if HAS_SEAROUTE:
        try:
            r = sr.searoute([lon1, lat1], [lon2, lat2], units="naut")
            d = float(r.properties.get("length", 0))
            if d > 0:
                dist = round(d, 1)
        except Exception:
            dist = None
    if dist is None:
        dist = round(haversine_nm(lat1, lon1, lat2, lon2) * 1.18, 1)
    if len(SEAROUTE_CACHE) > 25000:
        SEAROUTE_CACHE.clear()
    SEAROUTE_CACHE[key] = dist
    return dist


def register_port(pid, name, country, lat, lon, radius_nm, roro, max_draft, aliases):
    pid = pid.strip().upper()
    if not pid or abs(lat) > 90 or abs(lon) > 180:
        return
    p = {
        "id": pid, "name": name.strip(), "country": country.strip().upper(),
        "lat": float(lat), "lon": float(lon), "radius_nm": float(radius_nm),
        "roro": bool(roro), "max_draft": float(max_draft or 0),
        "aliases": list(dict.fromkeys([a.strip().upper() for a in aliases if a and len(a.strip()) >= 3])),
    }
    PORTS_BY_ID[pid] = p
    for al in p["aliases"]:
        if al not in ALIAS_TO_PID or pid in {ep[0] for ep in EXTRA_PORTS}:
            ALIAS_TO_PID[al] = pid
    glat, glon = int(math.floor(lat)), int(math.floor(lon))
    for dlat in (-1, 0, 1):
        for dlon in (-1, 0, 1):
            PORT_GRID.setdefault((glat + dlat, glon + dlon), []).append(p)


def load_world_ports():
    import ports_loader
    ports_loader.load_all(register_port, EXTRA_PORTS, STATS, PORTS_BY_ID, HAS_SEAROUTE)


def find_nearest_port(lat, lon):
    cands = PORT_GRID.get((int(math.floor(lat)), int(math.floor(lon))), [])
    best = None
    best_d = 999999.0
    for p in cands:
        d = haversine_nm(lat, lon, p["lat"], p["lon"])
        if d <= p["radius_nm"] and d < best_d:
            best_d = d
            best = p
    return best


def parse_ais_destination_ports(dest_str):
    """Parses messy AIS destination strings (e.g. 'ITTRS>TRGEM', 'TRIZT>>MAPTM', 'TR GEM') into port IDs."""
    if not dest_str:
        return []
    raw = re.sub(r"[^A-Z0-9>/,\- ]", " ", dest_str.upper()).strip()
    if not raw or raw in ("FOR ORDER", "FOR ORDERS", "TO ORDER", "ORDERS", "UNKNOWN"):
        return []
    segments = [s.strip() for s in re.split(r">>|>|/|->|,|\bTO\b|\bVIA\b", raw) if s.strip()]
    resolved = []
    for seg in segments:
        compact = seg.replace(" ", "").replace("-", "")
        if compact in ALIAS_TO_PID:
            pid = ALIAS_TO_PID[compact]
            if pid not in resolved:
                resolved.append(pid)
            continue
        if seg in ALIAS_TO_PID:
            pid = ALIAS_TO_PID[seg]
            if pid not in resolved:
                resolved.append(pid)
            continue
        # Check 5-char UN/LOCODE tokens inside segment
        for tok in re.findall(r"\b[A-Z]{5}\b", compact):
            if tok in ALIAS_TO_PID:
                pid = ALIAS_TO_PID[tok]
                if pid not in resolved:
                    resolved.append(pid)
                break
        else:
            # Check space-separated 2+3 UN/LOCODE e.g. 'TR GEM'
            m = re.search(r"\b([A-Z]{2})\s+([A-Z]{3})\b", seg)
            if m and (m.group(1) + m.group(2)) in ALIAS_TO_PID:
                pid = ALIAS_TO_PID[m.group(1) + m.group(2)]
                if pid not in resolved:
                    resolved.append(pid)
    return resolved[:3]


def ship_category(code):
    try:
        c = int(code or 0)
    except Exception:
        return "other"
    if 70 <= c <= 79: return "cargo"
    if 80 <= c <= 89: return "tanker"
    if 60 <= c <= 69: return "passenger"
    if c == 30: return "fishing"
    if 50 <= c <= 59 or c in (31, 32): return "tug"
    return "other"


def classify_size(loa, category):
    if not loa or loa < 20:
        return "Unknown"
    if category in ("cargo", "tanker"):
        if loa < 110: return "Coaster (<110m)"
        if loa < 160: return "Small Handy (110-160m)"
        if loa < 185: return "Handysize (160-185m)"
        if loa < 205: return "Supramax/MR (185-205m)"
        if loa < 240: return "Panamax/LR1 (205-240m)"
        return "Capesize/ULCV (>240m)"
    return f"{int(loa)}m"


def infer_load_state(draught, max_d, min_d, loa):
    if not draught or draught <= 0:
        return "Unknown"
    if max_d and min_d and (max_d - min_d) >= 1.2:
        return "Laden" if ((draught - min_d) / (max_d - min_d)) >= 0.55 else "Ballast"
    if loa and loa >= 80:
        ratio = draught / loa
        if ratio >= 0.055: return "Likely Laden"
        if ratio <= 0.040: return "Likely Ballast"
    return f"{draught:.1f}m"


def format_ais_eta(eta_obj):
    if not isinstance(eta_obj, dict):
        return ""
    m, d = int(eta_obj.get("Month") or 0), int(eta_obj.get("Day") or 0)
    h, mn = int(eta_obj.get("Hour") or 0), int(eta_obj.get("Minute") or 0)
    if not (1 <= m <= 12 and 1 <= d <= 31):
        return ""
    return f"{m:02d}-{d:02d} {(0 if h >= 24 else h):02d}:{(0 if mn >= 60 else mn):02d}Z"


def init_db():
    with DB_LOCK:
        con = sqlite3.connect(DB_PATH)
        con.execute("PRAGMA journal_mode=WAL;")
        con.execute("""
            CREATE TABLE IF NOT EXISTS vessels (
                mmsi TEXT PRIMARY KEY, imo TEXT DEFAULT '', name TEXT DEFAULT '', callsign TEXT DEFAULT '',
                type_code INTEGER DEFAULT 0, category TEXT DEFAULT 'other', loa REAL DEFAULT 0, beam REAL DEFAULT 0,
                size_class TEXT DEFAULT '', draught REAL DEFAULT 0, max_draught REAL DEFAULT 0, min_draught REAL DEFAULT 0,
                destination TEXT DEFAULT '', dest_port_1 TEXT DEFAULT '', dest_port_2 TEXT DEFAULT '',
                ais_eta TEXT DEFAULT '', nav_status INTEGER DEFAULT 15, lat REAL, lon REAL, sog REAL DEFAULT 0,
                course REAL DEFAULT 0, current_port_id TEXT DEFAULT '', current_port_name TEXT DEFAULT '',
                stopped_since INTEGER DEFAULT 0, last_seen INTEGER DEFAULT 0
            )
        """)
        con.execute("""
            CREATE TABLE IF NOT EXISTS port_calls (
                id INTEGER PRIMARY KEY AUTOINCREMENT, mmsi TEXT, imo TEXT, ship_name TEXT,
                port_id TEXT, port_name TEXT, country TEXT, arrived_at INTEGER, departed_at INTEGER DEFAULT 0,
                draft_in REAL DEFAULT 0, draft_out REAL DEFAULT 0, action TEXT DEFAULT 'IN_PORT'
            )
        """)
        con.execute("""
            CREATE TABLE IF NOT EXISTS tracks (
                mmsi TEXT, lat REAL, lon REAL, sog REAL, draught REAL, ts INTEGER
            )
        """)
        con.execute("""
            CREATE TABLE IF NOT EXISTS vessel_specs (
                imo TEXT PRIMARY KEY, mmsi TEXT, exact_type TEXT DEFAULT '', subtype_group TEXT DEFAULT '',
                owner TEXT DEFAULT '', operator TEXT DEFAULT '', flag TEXT DEFAULT '',
                dwt TEXT DEFAULT '', year_built TEXT DEFAULT '', crane_ramp_specs TEXT DEFAULT '',
                likely_cargo TEXT DEFAULT '', recent_ports_json TEXT DEFAULT '[]',
                next_ports_json TEXT DEFAULT '[]', source_urls TEXT DEFAULT '', enriched_at INTEGER DEFAULT 0
            )
        """)
        con.execute("CREATE INDEX IF NOT EXISTS idx_pc_mmsi ON port_calls(mmsi, arrived_at DESC)")
        con.execute("CREATE INDEX IF NOT EXISTS idx_pc_port ON port_calls(port_id, arrived_at DESC)")
        con.execute("CREATE INDEX IF NOT EXISTS idx_tr_mmsi ON tracks(mmsi, ts DESC)")
        con.execute("CREATE INDEX IF NOT EXISTS idx_v_dest ON vessels(dest_port_1)")
        con.commit()
        # Reload existing vessels into RAM on restart
        con.row_factory = sqlite3.Row
        for r in con.execute("SELECT * FROM vessels").fetchall():
            VESSELS[r["mmsi"]] = dict(r)
        con.close()
    print(f"[+] Loaded {len(VESSELS)} existing vessels from {DB_PATH}")


def ingest_message(msg):
    mtype = msg.get("MessageType")
    meta = msg.get("MetaData", {})
    mmsi = str(meta.get("MMSI") or "").strip()
    if not mmsi:
        return
    now = int(time.time())
    lat = meta.get("latitude")
    lon = meta.get("longitude")
    ship_name = (meta.get("ShipName") or "").strip()

    sog = course = nav_status = imo = callsign = dest = type_code = loa = beam = draught = ais_eta = None

    if mtype == "PositionReport":
        pr = msg.get("Message", {}).get("PositionReport", {})
        lat = pr.get("Latitude", lat)
        lon = pr.get("Longitude", lon)
        sog = round(float(pr.get("Sog") or 0), 1)
        hdg = pr.get("TrueHeading")
        cog = pr.get("Cog") or 0
        course = round(float(hdg if (hdg is not None and hdg != 511) else cog), 1)
        nav_status = int(pr.get("NavigationalStatus") if pr.get("NavigationalStatus") is not None else 15)
    elif mtype == "ShipStaticData":
        sd = msg.get("Message", {}).get("ShipStaticData", {})
        if sd.get("Name"): ship_name = sd["Name"].strip()
        imo = str(sd.get("ImoNumber") or "").strip()
        if imo == "0": imo = ""
        callsign = (sd.get("CallSign") or "").strip()
        dest = (sd.get("Destination") or "").strip()
        if sd.get("Type"): type_code = int(sd["Type"])
        dim = sd.get("Dimension") or {}
        a, b, c, d = int(dim.get("A") or 0), int(dim.get("B") or 0), int(dim.get("C") or 0), int(dim.get("D") or 0)
        if a + b > 0: loa = float(a + b)
        if c + d > 0: beam = float(c + d)
        raw_d = float(sd.get("MaximumStaticDraught") or 0)
        if raw_d > 30: raw_d = raw_d / 10.0
        if raw_d > 0: draught = round(raw_d, 1)
        ais_eta = format_ais_eta(sd.get("Eta"))
    else:
        return

    if lat is None or lon is None or abs(lat) > 90 or abs(lon) > 180:
        return

    with MEM_LOCK:
        prev = VESSELS.get(mmsi)
        if prev:
            rec = prev
            if imo: rec["imo"] = imo
            if ship_name: rec["name"] = ship_name
            if callsign: rec["callsign"] = callsign
            if type_code is not None:
                rec["type_code"] = type_code
                rec["category"] = ship_category(type_code)
            if loa is not None: rec["loa"] = loa
            if beam is not None: rec["beam"] = beam
            rec["size_class"] = classify_size(rec["loa"], rec["category"])
            if draught is not None:
                rec["draught"] = draught
                rec["max_draught"] = max(rec["max_draught"] or 0, draught)
                rec["min_draught"] = draught if not rec["min_draught"] else min(rec["min_draught"], draught)
            if dest:
                rec["destination"] = dest
                parsed = parse_ais_destination_ports(dest)
                rec["dest_port_1"] = parsed[0] if len(parsed) >= 1 else ""
                rec["dest_port_2"] = parsed[1] if len(parsed) >= 2 else ""
            if ais_eta: rec["ais_eta"] = ais_eta
            if sog is not None: rec["sog"] = sog
            if course is not None: rec["course"] = course
            if nav_status is not None: rec["nav_status"] = nav_status
            rec["lat"], rec["lon"], rec["last_seen"] = lat, lon, now
            prev_pid = rec["current_port_id"]
        else:
            cat = ship_category(type_code or 0)
            parsed = parse_ais_destination_ports(dest or "")
            rec = {
                "mmsi": mmsi, "imo": imo or "", "name": ship_name or f"MMSI {mmsi}", "callsign": callsign or "",
                "type_code": type_code or 0, "category": cat, "loa": loa or 0.0, "beam": beam or 0.0,
                "size_class": classify_size(loa or 0.0, cat), "draught": draught or 0.0,
                "max_draught": draught or 0.0, "min_draught": draught or 0.0,
                "destination": dest or "", "dest_port_1": parsed[0] if len(parsed) >= 1 else "",
                "dest_port_2": parsed[1] if len(parsed) >= 2 else "", "ais_eta": ais_eta or "",
                "nav_status": nav_status if nav_status is not None else 15, "lat": lat, "lon": lon,
                "sog": sog or 0.0, "course": course or 0.0, "current_port_id": "", "current_port_name": "",
                "stopped_since": 0, "last_seen": now,
            }
            VESSELS[mmsi] = rec
            prev_pid = ""

        is_stopped = (rec["sog"] <= 0.8) or (rec["nav_status"] in (1, 5))
        rec["stopped_since"] = (rec["stopped_since"] or now) if is_stopped else 0

        port_hit = find_nearest_port(lat, lon) if is_stopped else None
        cur_pid = port_hit["id"] if port_hit else ""
        cur_pname = port_hit["name"] if port_hit else ""

        if cur_pid and cur_pid != prev_pid:
            rec["current_port_id"] = cur_pid
            rec["current_port_name"] = cur_pname
            PENDING_CALLS.append(("OPEN", (mmsi, rec["imo"], rec["name"], cur_pid, cur_pname, port_hit["country"], now, rec["draught"])))
        elif prev_pid and not cur_pid and rec["sog"] >= 2.0:
            rec["current_port_id"] = ""
            rec["current_port_name"] = ""
            PENDING_CALLS.append(("CLOSE", (mmsi, prev_pid, now, rec["draught"])))

        if now - LAST_TRACK_TS.get(mmsi, 0) >= 900:
            PENDING_TRACKS.append((mmsi, lat, lon, rec["sog"], rec["draught"], now))
            LAST_TRACK_TS[mmsi] = now

        DIRTY_MMSIS.add(mmsi)
        STATS["messages"] += 1


def db_flusher_loop():
    """Flushes dirty vessel updates, port calls, and tracks to SQLite every 5s in one fast transaction."""
    while True:
        time.sleep(5)
        with MEM_LOCK:
            if not DIRTY_MMSIS and not PENDING_CALLS and not PENDING_TRACKS:
                continue
            batch_vessels = [dict(VESSELS[m]) for m in DIRTY_MMSIS if m in VESSELS]
            DIRTY_MMSIS.clear()
            calls = list(PENDING_CALLS)
            PENDING_CALLS.clear()
            tracks = list(PENDING_TRACKS)
            PENDING_TRACKS.clear()

        with DB_LOCK:
            con = sqlite3.connect(DB_PATH)
            cur = con.cursor()
            if batch_vessels:
                cur.executemany("""
                    INSERT INTO vessels (
                        mmsi, imo, name, callsign, type_code, category, loa, beam, size_class,
                        draught, max_draught, min_draught, destination, dest_port_1, dest_port_2,
                        ais_eta, nav_status, lat, lon, sog, course, current_port_id, current_port_name,
                        stopped_since, last_seen
                    ) VALUES (
                        :mmsi, :imo, :name, :callsign, :type_code, :category, :loa, :beam, :size_class,
                        :draught, :max_draught, :min_draught, :destination, :dest_port_1, :dest_port_2,
                        :ais_eta, :nav_status, :lat, :lon, :sog, :course, :current_port_id, :current_port_name,
                        :stopped_since, :last_seen
                    )
                    ON CONFLICT(mmsi) DO UPDATE SET
                        imo=excluded.imo, name=excluded.name, callsign=excluded.callsign,
                        type_code=excluded.type_code, category=excluded.category, loa=excluded.loa,
                        beam=excluded.beam, size_class=excluded.size_class, draught=excluded.draught,
                        max_draught=excluded.max_draught, min_draught=excluded.min_draught,
                        destination=excluded.destination, dest_port_1=excluded.dest_port_1,
                        dest_port_2=excluded.dest_port_2, ais_eta=excluded.ais_eta,
                        nav_status=excluded.nav_status, lat=excluded.lat, lon=excluded.lon,
                        sog=excluded.sog, course=excluded.course, current_port_id=excluded.current_port_id,
                        current_port_name=excluded.current_port_name, stopped_since=excluded.stopped_since,
                        last_seen=excluded.last_seen
                """, batch_vessels)
            for kind, data in calls:
                if kind == "OPEN":
                    mmsi, imo, sname, pid, pname, country, ts, d_in = data
                    cur.execute(
                        "INSERT INTO port_calls (mmsi, imo, ship_name, port_id, port_name, country, arrived_at, draft_in, action) VALUES (?,?,?,?,?,?,?,?,?)",
                        (mmsi, imo, sname, pid, pname, country, ts, d_in, "IN_PORT"),
                    )
                elif kind == "CLOSE":
                    mmsi, prev_pid, ts, d_out = data
                    row = cur.execute(
                        "SELECT id, draft_in FROM port_calls WHERE mmsi=? AND port_id=? AND departed_at=0 ORDER BY id DESC LIMIT 1",
                        (mmsi, prev_pid),
                    ).fetchone()
                    if row:
                        cid, d_in = row[0], row[1] or 0
                        act = "DEPARTED"
                        if d_in > 0 and d_out > 0:
                            if d_out <= d_in - 0.4: act = "DISCHARGED (BALLAST)"
                            elif d_out >= d_in + 0.4: act = "LOADED (LADEN)"
                        cur.execute("UPDATE port_calls SET departed_at=?, draft_out=?, action=? WHERE id=?", (ts, d_out, act, cid))
            if tracks:
                cur.executemany("INSERT INTO tracks (mmsi, lat, lon, sog, draught, ts) VALUES (?,?,?,?,?,?)", tracks)
            con.commit()
            con.close()


async def stream_aisstream():
    import websockets
    url = "wss://stream.aisstream.io/v0/stream"
    sub = {
        "APIKey": AISSTREAM_KEY,
        "BoundingBoxes": BOUNDING_BOXES,
        "FilterMessageTypes": ["PositionReport", "ShipStaticData"],
    }
    last_log = 0
    while True:
        try:
            async with websockets.connect(url, open_timeout=30, ping_interval=None, ping_timeout=None, family=socket.AF_INET) as ws:
                await ws.send(json.dumps(sub))
                STATS["connected"] = True
                print("[+] Connected to aisstream.io GLOBAL live feed!")
                while True:
                    raw = await asyncio.wait_for(ws.recv(), timeout=60)
                    ingest_message(json.loads(raw))
                    now = int(time.time())
                    if now - last_log >= 15:
                        with MEM_LOCK:
                            vc = len(VESSELS)
                        print(f"[*] Global DB live: {vc} unique ships | {STATS['messages']} AIS msgs | Exa spend: ${STATS['exa_spend']:.3f}")
                        last_log = now
        except Exception as e:
            STATS["connected"] = False
            print(f"[!] AISStream reconnect in 12s ({e})")
            await asyncio.sleep(12)


def call_gemini_text(prompt):
    if not GEMINI_KEY:
        return ""
    body = {"contents": [{"parts": [{"text": prompt}]}]}
    r = requests.post(
        "https://generativelanguage.googleapis.com/v1beta/models/gemini-3.5-flash-lite:generateContent",
        headers={"x-goog-api-key": GEMINI_KEY, "Content-Type": "application/json"},
        json=body, timeout=25,
    )
    if r.status_code == 403:
        r = requests.post(
            f"https://aiplatform.googleapis.com/v1/publishers/google/models/gemini-3.5-flash-lite:generateContent?key={GEMINI_KEY}",
            headers={"Content-Type": "application/json"},
            json=body, timeout=25,
        )
    data = r.json()
    if "candidates" in data:
        return data["candidates"][0]["content"]["parts"][0]["text"]
    return ""


def enrich_vessel_by_mmsi(mmsi, force=False):
    """Permanent $0.004 Exa Lite + Gemini IMO enricher: Exact Type, Owner, Operator, DWT, Specs, Cargo & Ports."""
    with MEM_LOCK:
        v = dict(VESSELS.get(mmsi, {}))
    if not v:
        return {"error": "Vessel not found"}
    cache_key = v["imo"] if v.get("imo") else f"MMSI:{mmsi}"

    if not force:
        with DB_LOCK:
            con = sqlite3.connect(DB_PATH)
            con.row_factory = sqlite3.Row
            row = con.execute("SELECT * FROM vessel_specs WHERE imo=?", (cache_key,)).fetchone()
            con.close()
        if row:
            return dict(row)

    if not EXA_KEY or not GEMINI_KEY:
        return {"error": "Export EXA_API_KEY and GEMINI_API_KEY to enrich vessels."}

    q_id = f"IMO {v['imo']}" if v.get("imo") else f"MMSI {mmsi}"
    query = f"{v['name']} {q_id} ship type owner manager operator DWT built crane ramp recent ports"
    try:
        resp = requests.post(
            "https://api.exa.ai/search",
            headers={"Authorization": f"Bearer {EXA_KEY}", "Content-Type": "application/json"},
            json={"query": query, "type": "lite", "numResults": 5, "contents": {"text": {"maxCharacters": 2200}}},
            timeout=25,
        )
        data = resp.json()
        cost_obj = data.get("costDollars", 0.0)
        cost = float(cost_obj.get("total", 0.0)) if isinstance(cost_obj, dict) else float(cost_obj or 0.0)
        STATS["exa_spend"] += cost
        results = data.get("results", [])
    except Exception as e:
        return {"error": f"Exa lookup failed: {e}"}

    snippets = "\n\n".join([f"URL: {r.get('url')}\nTITLE: {r.get('title')}\nTEXT: {(r.get('text') or '')[:1800]}" for r in results])
    source_urls = ", ".join([r.get("url", "") for r in results[:3]])

    prompt = (
        f"Extract verified maritime vessel intelligence for {v['name']} ({q_id}, LOA {v.get('loa')}m, Beam {v.get('beam')}m, "
        f"AIS Dest: {v.get('destination')}) from the web snippets below. Return ONLY valid JSON with these exact keys:\n"
        f'{{"exact_type":"e.g. Vehicles Carrier (PCTC) / Ro-Ro Cargo / Heavy-Lift MPP / Container Ship / Bulk Carrier / Tanker",'
        f'"subtype_group":"one of: roro, mpp, bulk, container, tanker, other",'
        f'"owner":"Registered Owner or Unknown",'
        f'"operator":"Commercial Manager / Operator / Liner or Unknown",'
        f'"flag":"Flag country",'
        f'"dwt":"Deadweight tonnage e.g. 14387 DWT",'
        f'"year_built":"4-digit year or Unknown",'
        f'"crane_ramp_specs":"e.g. 240t stern ramp, 6.5m deck height OR 2x150t cranes, tween-deck OR Gearless",'
        f'"likely_cargo":"Concise likely cargo carried based on vessel type and route",'
        f'"recent_ports":["Up to 3 recent past port names mentioned in snippets, most recent last"],'
        f'"next_ports":["Up to 3 upcoming scheduled port names if liner schedule mentioned"]}}\n\n'
        f"SNIPPETS:\n{snippets}"
    )
    raw_ai = call_gemini_text(prompt)
    cleaned = re.sub(r"^```(?:json)?\s*|\s*```$", "", raw_ai.strip(), flags=re.S)
    try:
        parsed = json.loads(cleaned)
    except Exception:
        m = re.search(r"\{.*\}", cleaned, flags=re.S)
        parsed = json.loads(m.group(0)) if m else {}

    rec = {
        "imo": cache_key,
        "mmsi": mmsi,
        "exact_type": str(parsed.get("exact_type") or "Unknown"),
        "subtype_group": str(parsed.get("subtype_group") or "other").lower(),
        "owner": str(parsed.get("owner") or "Unknown"),
        "operator": str(parsed.get("operator") or "Unknown"),
        "flag": str(parsed.get("flag") or "Unknown"),
        "dwt": str(parsed.get("dwt") or "Unknown"),
        "year_built": str(parsed.get("year_built") or "Unknown"),
        "crane_ramp_specs": str(parsed.get("crane_ramp_specs") or "Unknown"),
        "likely_cargo": str(parsed.get("likely_cargo") or "Unknown"),
        "recent_ports_json": json.dumps((parsed.get("recent_ports") or [])[:3]),
        "next_ports_json": json.dumps((parsed.get("next_ports") or [])[:3]),
        "source_urls": source_urls,
        "enriched_at": int(time.time()),
    }
    with DB_LOCK:
        con = sqlite3.connect(DB_PATH)
        con.execute("""
            INSERT INTO vessel_specs (
                imo, mmsi, exact_type, subtype_group, owner, operator, flag, dwt, year_built,
                crane_ramp_specs, likely_cargo, recent_ports_json, next_ports_json, source_urls, enriched_at
            ) VALUES (
                :imo, :mmsi, :exact_type, :subtype_group, :owner, :operator, :flag, :dwt, :year_built,
                :crane_ramp_specs, :likely_cargo, :recent_ports_json, :next_ports_json, :source_urls, :enriched_at
            ) ON CONFLICT(imo) DO UPDATE SET
                exact_type=excluded.exact_type, subtype_group=excluded.subtype_group, owner=excluded.owner,
                operator=excluded.operator, flag=excluded.flag, dwt=excluded.dwt, year_built=excluded.year_built,
                crane_ramp_specs=excluded.crane_ramp_specs, likely_cargo=excluded.likely_cargo,
                recent_ports_json=excluded.recent_ports_json, next_ports_json=excluded.next_ports_json,
                source_urls=excluded.source_urls, enriched_at=excluded.enriched_at
        """, rec)
        con.commit()
        con.close()
    return rec


def get_specs_map():
    with DB_LOCK:
        con = sqlite3.connect(DB_PATH)
        con.row_factory = sqlite3.Row
        rows = con.execute("SELECT * FROM vessel_specs").fetchall()
        con.close()
    out = {}
    for r in rows:
        d = dict(r)
        out[d["imo"]] = d
        if d["mmsi"]:
            out[f"MMSI:{d['mmsi']}"] = d
    return out


def build_six_port_chain(v, db_port_calls, spec):
    """Builds Last 3 Ports -> Current -> Next 3 Ports combining live DB + AIS + Enriched schedule + loop prediction."""
    past_ports = []
    for pc in reversed(db_port_calls[:10]):
        if pc["departed_at"]:
            lbl = f"{pc['port_name']} ({pc['action']})"
            if not past_ports or past_ports[-1] != lbl:
                past_ports.append(lbl)
    if len(past_ports) < 3 and spec:
        try:
            enr_past = json.loads(spec.get("recent_ports_json") or "[]")
            for ep in enr_past:
                if ep and not any(ep.lower() in p.lower() for p in past_ports):
                    past_ports.insert(0, f"{ep} [web]")
        except Exception:
            pass
    last_3 = past_ports[-3:]

    next_ports = []
    if v.get("dest_port_1") and v["dest_port_1"] in PORTS_BY_ID:
        next_ports.append(f"{PORTS_BY_ID[v['dest_port_1']]['name']} ({v['dest_port_1']})")
    elif v.get("destination"):
        next_ports.append(v["destination"])
    if v.get("dest_port_2") and v["dest_port_2"] in PORTS_BY_ID:
        next_ports.append(f"{PORTS_BY_ID[v['dest_port_2']]['name']} ({v['dest_port_2']})")

    # Add enriched scheduled next ports if available
    if len(next_ports) < 3 and spec:
        try:
            for np in json.loads(spec.get("next_ports_json") or "[]"):
                if np and not any(np.lower() in x.lower() for x in next_ports):
                    next_ports.append(f"{np} [sched]")
        except Exception:
            pass

    # Simple Markov loop predictor from vessel's own logged port history
    if len(next_ports) < 3 and len(db_port_calls) >= 3:
        seq = [pc["port_name"] for pc in reversed(db_port_calls)]
        cur_anchor = v.get("current_port_name") or (next_ports[-1].split(" (")[0] if next_ports else "")
        followers = Counter()
        for i in range(len(seq) - 1):
            if cur_anchor and cur_anchor.lower() in seq[i].lower() and seq[i + 1] != seq[i]:
                followers[seq[i + 1]] += 1
        for pname, _ in followers.most_common(2):
            if len(next_ports) < 3 and not any(pname.lower() in x.lower() for x in next_ports):
                next_ports.append(f"{pname} [loop]")

    return last_3, next_ports[:3]


def get_port_board(port_id):
    p = PORTS_BY_ID.get(port_id)
    if not p:
        return {"error": "Port not found"}
    specs_map = get_specs_map()
    now_ts = int(time.time())
    now_dt = datetime.now(timezone.utc)

    with MEM_LOCK:
        all_v = list(VESSELS.values())

    in_port = []
    inbound = []
    aliases = set(p["aliases"])

    for v in all_v:
        spec = specs_map.get(v["imo"]) or specs_map.get(f"MMSI:{v['mmsi']}") or {}
        if v["current_port_id"] == port_id:
            dwell = round((now_ts - v["stopped_since"]) / 3600.0, 1) if v["stopped_since"] else 0.0
            in_port.append({
                "mmsi": v["mmsi"], "imo": v["imo"], "name": v["name"], "category": v["category"],
                "exact_type": spec.get("exact_type") or v["size_class"] or v["category"],
                "owner": spec.get("owner") or "—", "operator": spec.get("operator") or "—",
                "likely_cargo": spec.get("likely_cargo") or "—", "loa": v["loa"], "draught": v["draught"],
                "load_state": infer_load_state(v["draught"], v["max_draught"], v["min_draught"], v["loa"]),
                "dwell_hrs": dwell, "nav_status": NAV_STATUS_MAP.get(v["nav_status"], "Unknown"),
                "destination": v["destination"] or "—", "lat": v["lat"], "lon": v["lon"],
            })
        else:
            dest_up = (v["destination"] or "").upper()
            matched = (v["dest_port_1"] == port_id or v["dest_port_2"] == port_id) or (dest_up and any(al in dest_up for al in aliases if len(al) >= 5))
            if matched:
                dist = sea_distance_nm(v["lat"], v["lon"], p["lat"], p["lon"])
                spd = v["sog"] if v["sog"] >= 4.0 else 11.5
                eta_dt = now_dt + timedelta(days=(dist / (spd * 24.0)))
                inbound.append({
                    "mmsi": v["mmsi"], "imo": v["imo"], "name": v["name"], "category": v["category"],
                    "exact_type": spec.get("exact_type") or v["size_class"] or v["category"],
                    "owner": spec.get("owner") or "—", "operator": spec.get("operator") or "—",
                    "likely_cargo": spec.get("likely_cargo") or "—", "loa": v["loa"], "draught": v["draught"],
                    "load_state": infer_load_state(v["draught"], v["max_draught"], v["min_draught"], v["loa"]),
                    "dist_nm": dist, "sog": v["sog"], "eta": eta_dt.strftime("%Y-%m-%d %H:%M"),
                    "destination": v["destination"], "lat": v["lat"], "lon": v["lon"],
                })

    with DB_LOCK:
        con = sqlite3.connect(DB_PATH)
        con.row_factory = sqlite3.Row
        dep_rows = con.execute(
            "SELECT * FROM port_calls WHERE port_id=? AND departed_at > 0 ORDER BY departed_at DESC LIMIT 60",
            (port_id,),
        ).fetchall()
        con.close()

    departures = []
    for d in dep_rows:
        spec = specs_map.get(d["imo"]) or specs_map.get(f"MMSI:{d['mmsi']}") or {}
        departures.append({
            "mmsi": d["mmsi"], "imo": d["imo"], "name": d["ship_name"],
            "exact_type": spec.get("exact_type") or "—", "operator": spec.get("operator") or "—",
            "arrived": datetime.fromtimestamp(d["arrived_at"], timezone.utc).strftime("%b %d %H:%M"),
            "departed": datetime.fromtimestamp(d["departed_at"], timezone.utc).strftime("%b %d %H:%M"),
            "draft_in": d["draft_in"], "draft_out": d["draft_out"], "action": d["action"],
        })

    in_port.sort(key=lambda x: -x["dwell_hrs"])
    inbound.sort(key=lambda x: x["dist_nm"])
    return {"port": p, "in_port": in_port[:120], "inbound": inbound[:120], "departures": departures}


def screen_laycan(target_id, start_str, end_str, subtype_filter, min_loa, discharge_days):
    if target_id in CLUSTERS:
        t = CLUSTERS[target_id]
        t_lat, t_lon, t_name = t["lat"], t["lon"], t["name"]
        target_pids = t["port_ids"]
        aliases = set(t["aliases"])
    elif target_id in PORTS_BY_ID:
        p = PORTS_BY_ID[target_id]
        t_lat, t_lon, t_name = p["lat"], p["lon"], f"{p['name']} ({p['id']}, {p['country']})"
        target_pids = {p["id"]}
        aliases = set(p["aliases"])
    else:
        return "Unknown Target", []

    now_dt = datetime.now(timezone.utc)
    try: lc_start = datetime.strptime(start_str, "%Y-%m-%d").replace(tzinfo=timezone.utc)
    except Exception: lc_start = now_dt
    try: lc_end = datetime.strptime(end_str, "%Y-%m-%d").replace(tzinfo=timezone.utc) + timedelta(hours=23, minutes=59)
    except Exception: lc_end = now_dt + timedelta(days=30)

    specs_map = get_specs_map()
    with DB_LOCK:
        con = sqlite3.connect(DB_PATH)
        con.row_factory = sqlite3.Row
        pc_rows = con.execute("SELECT * FROM port_calls ORDER BY arrived_at DESC LIMIT 10000").fetchall()
        con.close()
    pc_by_mmsi = {}
    for r in pc_rows:
        pc_by_mmsi.setdefault(r["mmsi"], []).append(dict(r))

    with MEM_LOCK:
        all_v = list(VESSELS.values())

    # Fast pre-filter by straight-line radius (~1,600 NM) before calling searoute
    now_ts = int(time.time())
    candidates = []
    for v in all_v:
        spec = specs_map.get(v["imo"]) or specs_map.get(f"MMSI:{v['mmsi']}") or {}
        sg = spec.get("subtype_group") or ""
        cat = v["category"]

        # Smart subtype filter (works both before and after enrichment!)
        name_up = (v["name"] or "").upper()
        is_known_container = any(k in name_up for k in ("MSC ", "MAERSK", "CMA CGM", "EVER ", "YM ", "COSCO SHIPPING ", "HAPAG", "ONE ", "HMM ", "OOCL", "ZIM "))
        if subtype_filter == "roro":
            is_roro_hint = sg == "roro" or any(k in name_up for k in ("GRANDE ", "ECO ", "EUROCARGO", "NEPTUNE ", "HOEGH", "GLOVIS", "BAHRI", "SEAWAYS", "FIDELIO", "CARRIER", "HIGHWAY", "LEADER", "ACE", "VIKING", "MORNING ", "JOLLY ", "ULUSOY"))
            if not is_roro_hint:
                continue
        elif subtype_filter == "mpp":
            is_mpp_hint = sg == "mpp" or any(k in name_up for k in ("BBC ", "INDUSTRIAL ", "AAL ", "SAL ", "UHL ", "CHIPOL", "COSCOSHIPPING", "SPLIETHOFF", "BIGLIFT", "DOCK "))
            if not is_mpp_hint:
                continue
        elif subtype_filter == "roro_mpp":
            if sg in ("container", "bulk", "tanker") or is_known_container:
                continue
            if cat != "cargo":
                continue
        elif subtype_filter in ("cargo", "tanker") and cat != subtype_filter:
            continue

        loa = v["loa"] or 0
        if min_loa > 0 and loa > 0 and loa < min_loa:
            continue

        raw_dist = haversine_nm(v["lat"], v["lon"], t_lat, t_lon)
        dest_up = (v["destination"] or "").upper()
        in_target = v["current_port_id"] in target_pids
        dest_match = (v["dest_port_1"] in target_pids or v["dest_port_2"] in target_pids) or (dest_up and any(al in dest_up for al in aliases if len(al) >= 5))

        if not in_target and not dest_match and raw_dist > 1300:
            continue

        dist_nm = 0.0 if in_target else sea_distance_nm(v["lat"], v["lon"], t_lat, t_lon)
        spd = v["sog"] if v["sog"] >= 4.0 else 11.5
        steam_days = dist_nm / (spd * 24.0)
        est_arr = now_dt + timedelta(days=steam_days)
        dwell_hrs = round((now_ts - v["stopped_since"]) / 3600.0, 1) if v["stopped_since"] else 0.0
        load_state = infer_load_state(v["draught"], v["max_draught"], v["min_draught"], loa)

        score = 0
        if in_target:
            bucket = "IN_PORT_NOW"
            rem = 0 if (dwell_hrs >= 48 or "Ballast" in load_state or "ORDER" in dest_up or not dest_up) else max(1, discharge_days - dwell_hrs / 24.0)
            est_open = now_dt + timedelta(days=rem)
            score = 95 if est_open <= lc_end else 50
        elif dest_match:
            bucket = "INBOUND_TO_TARGET"
            est_open = est_arr + timedelta(days=discharge_days)
            score = 90 if (lc_start - timedelta(days=5) <= est_open <= lc_end) else (78 if est_open <= lc_end else 35)
        elif dist_nm <= 1600 and est_arr <= lc_end:
            bucket = "NEARBY_POSITIONING"
            est_open = est_arr + (timedelta(days=0) if "Ballast" in load_state else timedelta(days=discharge_days))
            score = (74 if "Ballast" in load_state else 60) if est_open <= lc_end else 30
        else:
            continue

        if score < 45:
            continue
        if v["imo"]: score += 5
        if spec: score += 4
        if sg in ("roro", "mpp") and subtype_filter in ("roro", "mpp", "roro_mpp"): score += 10

        last_3, next_3 = build_six_port_chain(v, pc_by_mmsi.get(v["mmsi"], []), spec)
        candidates.append({
            "score": score, "bucket": bucket, "mmsi": v["mmsi"], "imo": v["imo"], "name": v["name"],
            "category": cat, "exact_type": spec.get("exact_type") or v["size_class"] or cat,
            "owner": spec.get("owner") or "", "operator": spec.get("operator") or "",
            "dwt": spec.get("dwt") or "", "year_built": spec.get("year_built") or "",
            "crane_ramp_specs": spec.get("crane_ramp_specs") or "", "likely_cargo": spec.get("likely_cargo") or "",
            "enriched": bool(spec), "loa": loa, "beam": v["beam"], "draught": v["draught"],
            "load_state": load_state, "destination": v["destination"] or "—", "ais_eta": v["ais_eta"] or "—",
            "sog": v["sog"], "dist_nm": dist_nm, "est_arrival": est_arr.strftime("%Y-%m-%d"),
            "est_open_date": est_open.strftime("%Y-%m-%d"), "current_port": v["current_port_name"] or "At Sea",
            "dwell_hrs": dwell_hrs, "lat": v["lat"], "lon": v["lon"],
            "last_3_ports": last_3, "next_3_ports": next_3,
        })

    candidates.sort(key=lambda x: (-x["score"], x["dist_nm"]))
    return t_name, candidates[:150]


HTML_PAGE = r"""<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1.0" />
  <title>OpenMarine v2 — Global Port Intelligence</title>
  <link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css" />
  <style>
    * { box-sizing: border-box; margin: 0; padding: 0; font-family: system-ui, -apple-system, sans-serif; }
    body { background: #09101d; color: #e2e8f0; height: 100dvh; display: flex; flex-direction: column; overflow: hidden; }
    header { background: #0f172a; padding: 8px 12px; display: flex; justify-content: space-between; align-items: center; border-bottom: 1px solid #1e293b; gap: 8px; flex-wrap: wrap; }
    .brand { font-weight: 800; font-size: 14px; color: #38bdf8; }
    .stat { font-size: 11px; color: #94a3b8; }
    .tabs { display: flex; gap: 5px; flex-wrap: wrap; }
    .tab-btn { background: #1e293b; color: #cbd5e1; border: 1px solid #334155; padding: 6px 10px; border-radius: 6px; font-size: 12px; font-weight: 700; cursor: pointer; }
    .tab-btn.active { background: #0284c7; color: #fff; border-color: #0284c7; }
    .view { flex: 1; display: none; overflow: hidden; }
    .view.active { display: flex; flex-direction: column; }
    .controls { background: #111827; padding: 9px; border-bottom: 1px solid #1e293b; display: grid; grid-template-columns: repeat(auto-fit, minmax(130px, 1fr)); gap: 7px; position: relative; }
    label { font-size: 10px; color: #94a3b8; display: block; margin-bottom: 2px; text-transform: uppercase; letter-spacing: 0.4px; }
    select, input { width: 100%; background: #1e293b; border: 1px solid #334155; color: #fff; padding: 6px 8px; border-radius: 6px; font-size: 12px; }
    .btn { background: #0284c7; color: #fff; border: none; padding: 7px 10px; border-radius: 6px; font-weight: 700; font-size: 12px; cursor: pointer; }
    .btn-sec { background: #1e293b; border: 1px solid #334155; }
    .btn-gold { background: #b45309; }
    .scroll { flex: 1; overflow-y: auto; padding: 10px; display: flex; flex-direction: column; gap: 8px; }
    .card { background: #131c31; border: 1px solid #1e293b; border-radius: 8px; padding: 10px; }
    .row-top { display: flex; justify-content: space-between; align-items: center; gap: 6px; flex-wrap: wrap; }
    .title { font-weight: 700; font-size: 14px; color: #f8fafc; }
    .pill { font-size: 10px; font-weight: 700; padding: 2px 7px; border-radius: 99px; }
    .IN_PORT_NOW { background: #14532d; color: #86efac; }
    .INBOUND_TO_TARGET { background: #1e3a8a; color: #93c5fd; }
    .NEARBY_POSITIONING { background: #713f12; color: #fde047; }
    .meta { font-size: 12px; color: #cbd5e1; margin-top: 5px; line-height: 1.45; }
    .chain { margin-top: 6px; font-size: 11px; background: #0b1220; border: 1px solid #1e293b; padding: 6px 8px; border-radius: 6px; color: #93c5fd; line-height: 1.4; }
    .specs { margin-top: 6px; font-size: 11px; background: #0f1d2e; border-left: 3px solid #38bdf8; padding: 6px 8px; border-radius: 4px; color: #e2e8f0; }
    .actions { display: flex; gap: 6px; margin-top: 8px; flex-wrap: wrap; }
    .dropdown { position: absolute; left: 9px; right: 9px; top: 58px; background: #0f172a; border: 1px solid #38bdf8; border-radius: 6px; max-height: 220px; overflow-y: auto; z-index: 2000; display: none; }
    .dd-item { padding: 8px 10px; font-size: 12px; border-bottom: 1px solid #1e293b; cursor: pointer; }
    .dd-item:hover { background: #1e293b; }
    .subtabs { display: flex; gap: 6px; padding: 8px 10px 0; }
    #map { flex: 1; width: 100%; background: #1a2230; }
    .modal-bg { position: fixed; inset: 0; background: rgba(0,0,0,0.75); z-index: 3000; display: none; align-items: center; justify-content: center; padding: 12px; }
    .modal { background: #0f172a; border: 1px solid #334155; border-radius: 10px; max-width: 560px; width: 100%; max-height: 85dvh; overflow-y: auto; padding: 14px; }
  </style>
</head>
<body>
  <header>
    <div>
      <div class="brand">SPRNT // BLACKFRIARS MARINE INTEL</div>
      <div class="stat" id="dbstat">Loading global ports...</div>
    </div>
    <div class="tabs">
      <button class="tab-btn active" id="tab_laycan" onclick="showTab('laycan', this)">Laycan</button>
      <button class="tab-btn" id="tab_portboard" onclick="showTab('portboard', this)">Port Board</button>
      <button class="tab-btn" id="tab_enriched" onclick="showTab('enriched', this)">Enriched</button>
      <button class="tab-btn" id="tab_shipsearch" onclick="showTab('shipsearch', this)">Ship Search</button>
      <button class="tab-btn" id="tab_map" onclick="showTab('mapview', this)">Map</button>
    </div>
  </header>

  <!-- TAB 1: LAYCAN TONNAGE SCREENER -->
  <div id="laycan" class="view active">
    <div class="controls">
      <div style="grid-column: span 2; position: relative;">
        <label>Target Port or Cluster (Search 3,800+ World Ports)</label>
        <input id="lc_port_input" value="Derince & Gemlik Only (Marmara RoRo/Breakbulk)" oninput="searchPorts(this.value, 'lc_dd', selectLaycanPort)" />
        <input type="hidden" id="lc_target_id" value="CLUSTER:DERINCE_GEMLIK" />
        <div id="lc_dd" class="dropdown" style="top:48px;left:0;right:0"></div>
      </div>
      <div><label>Laycan Start</label><input type="date" id="lc_start" value="2026-12-01" /></div>
      <div><label>Laycan End</label><input type="date" id="lc_end" value="2026-12-15" /></div>
      <div>
        <label>Vessel Filter</label>
        <select id="lc_type">
          <option value="roro_mpp" selected>RoRo / MPP (No Containers)</option>
          <option value="roro">RoRo / PCTC / ConRo Only</option>
          <option value="mpp">Heavy-Lift / MPP Only</option>
          <option value="cargo">All Dry Cargo</option>
          <option value="tanker">Tanker</option>
          <option value="all">All Types</option>
        </select>
      </div>
      <div><label>Min LOA (m)</label><input type="number" id="lc_loa" value="100" /></div>
      <div><label>Discharge Days</label><input type="number" id="lc_disc" value="4" /></div>
      <div style="display:flex;align-items:flex-end;gap:5px;grid-column:span 2;">
        <button class="btn" style="flex:1" onclick="runLaycan()">Find Open Ships</button>
        <button class="btn btn-gold" onclick="batchEnrichTop()">Enrich Top 10 (~$0.04)</button>
        <button class="btn btn-sec" onclick="exportLaycanCSV()">CSV</button>
      </div>
    </div>
    <div class="scroll" id="lc_results">
      <div class="card"><div class="meta">Search any of <b>3,800+ world ports</b> (or keep <b>Derince &amp; Gemlik</b>) and tap <b>Find Open Ships</b>. Use <b>Enrich Top 10</b> to permanently pull Owner, Operator, Exact Type, Ramp/Crane Specs &amp; Likely Cargo via Exa+Gemini ($0.004/ship).</div></div>
    </div>
  </div>

  <!-- TAB 2: GLOBAL PORT BOARD (ARRIVALS / IN PORT / DEPARTURES) -->
  <div id="portboard" class="view">
    <div class="controls" style="grid-template-columns: 1fr auto;">
      <div>
        <label>Search Any Port Worldwide (Name or UN/LOCODE e.g. TRDRC, TRGEM, JOAQB, NGLOS, SIKOP)</label>
        <input id="pb_input" placeholder="Type port name or code (e.g. Derince, Gemlik, Aqaba, Lagos, Rotterdam)..." oninput="searchPorts(this.value, 'pb_dd', selectPortBoard)" />
      </div>
      <div style="display:flex;align-items:flex-end;">
        <button class="btn" onclick="loadPortBoard(currentPortId)">Refresh</button>
      </div>
      <div id="pb_dd" class="dropdown"></div>
    </div>
    <div id="pb_header" style="padding:8px 10px 0;font-size:12px;color:#94a3b8"></div>
    <div class="subtabs">
      <button class="tab-btn active" id="sub_inport" onclick="switchPBTab('in_port', this)">In Port (0)</button>
      <button class="tab-btn" id="sub_inbound" onclick="switchPBTab('inbound', this)">Inbound (0)</button>
      <button class="tab-btn" id="sub_dep" onclick="switchPBTab('departures', this)">Departures (0)</button>
    </div>
    <div class="scroll" id="pb_list">
      <div class="card"><div class="meta">Search any port above (or click a port on the map) to see live ships <b>In Port</b>, <b>Inbound</b>, and <b>Departing</b>.</div></div>
    </div>
  </div>

  <!-- TAB 3: ENRICHED FLEET REGISTRY -->
  <div id="enriched" class="view">
    <div class="controls" style="grid-template-columns: 1fr 140px auto auto;">
      <div>
        <label>Filter Enriched Vessels (Name, IMO, Owner, Operator, Cargo)</label>
        <input id="enr_q" placeholder="Filter by owner, operator, ship, cargo..." oninput="loadEnriched()" />
      </div>
      <div>
        <label>Subtype</label>
        <select id="enr_sub" onchange="loadEnriched()">
          <option value="all" selected>All Subtypes</option>
          <option value="roro">RoRo / PCTC</option>
          <option value="mpp">Heavy-Lift / MPP</option>
          <option value="bulk">Bulk Carrier</option>
          <option value="container">Container</option>
          <option value="tanker">Tanker</option>
          <option value="other">Other</option>
        </select>
      </div>
      <div style="display:flex;align-items:flex-end;">
        <button class="btn" onclick="loadEnriched()">Refresh</button>
      </div>
      <div style="display:flex;align-items:flex-end;">
        <button class="btn btn-sec" onclick="exportEnrichedCSV()">CSV</button>
      </div>
    </div>
    <div class="scroll" id="enr_list">
      <div class="card"><div class="meta">Loading enriched fleet registry...</div></div>
    </div>
  </div>

  <!-- TAB 4: GLOBAL SHIP SEARCH -->
  <div id="shipsearch" class="view">
    <div class="controls" style="grid-template-columns: 1fr auto;">
      <div>
        <label>Search Any Ship (Name, IMO, MMSI, Callsign, Owner, Operator, or Destination)</label>
        <input id="ss_q" placeholder="e.g. ECO MALTA, 9513658, GRIMALDI, BBC, NEPTUNE, TRGEM..." oninput="runShipSearch()" />
      </div>
      <div style="display:flex;align-items:flex-end;">
        <button class="btn" onclick="runShipSearch()">Search</button>
      </div>
    </div>
    <div class="scroll" id="ss_list">
      <div class="card"><div class="meta">Type any <b>Ship Name, IMO, MMSI, Owner, or Operator</b> to pull up its full dossier, 6-port voyage chain, and live map position.</div></div>
    </div>
  </div>

  <!-- TAB 3: GLOBAL MAP -->
  <div id="mapview" class="view">
    <div id="map"></div>
  </div>

  <!-- VESSEL DOSSIER MODAL -->
  <div class="modal-bg" id="modalBg" onclick="if(event.target===this) closeModal()">
    <div class="modal" id="modalContent"></div>
  </div>

  <script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
  <script>
    const COLORS = { cargo: '#22c55e', tanker: '#ef4444', passenger: '#3b82f6', fishing: '#f97316', tug: '#06b6d4', other: '#94a3b8' };
    let map, mapReady = false, markers = {}, trackLine = null;
    let lastLaycanList = [];
    let currentPortId = 'TRGEM', pbData = null, pbSub = 'in_port';

    function showTab(id, btn) {
      document.querySelectorAll('.view').forEach(v => v.classList.remove('active'));
      document.querySelectorAll('header .tab-btn').forEach(b => b.classList.remove('active'));
      document.getElementById(id).classList.add('active');
      if (btn) btn.classList.add('active');
      if (id === 'mapview') { initMap(); setTimeout(() => { map.invalidateSize(); refreshMap(); }, 150); }
      if (id === 'portboard' && !pbData) loadPortBoard(currentPortId);
      if (id === 'enriched') loadEnriched();
    }

    async function searchPorts(q, ddId, onPick) {
      const dd = document.getElementById(ddId);
      if (!q || q.trim().length < 2) { dd.style.display = 'none'; return; }
      const r = await fetch('/api/ports?q=' + encodeURIComponent(q.trim()));
      const d = await r.json();
      if (!d.ports.length) { dd.style.display = 'none'; return; }
      dd.innerHTML = d.ports.map(p => `<div class="dd-item" data-id="${p.id}" data-name="${p.name}"><b>${p.name}</b> <span style="color:#38bdf8">(${p.id})</span> — ${p.country} ${p.roro ? '• RoRo' : ''}</div>`).join('');
      dd.style.display = 'block';
      dd.querySelectorAll('.dd-item').forEach(el => {
        el.onclick = () => { dd.style.display = 'none'; onPick(el.dataset.id, el.dataset.name); };
      });
    }

    function selectLaycanPort(id, name) {
      document.getElementById('lc_target_id').value = id;
      document.getElementById('lc_port_input').value = `${name} (${id})`;
    }

    function selectPortBoard(id, name) {
      currentPortId = id;
      document.getElementById('pb_input').value = `${name} (${id})`;
      loadPortBoard(id);
    }

    async function loadPortBoard(pid) {
      const list = document.getElementById('pb_list');
      list.innerHTML = '<div class="card"><div class="meta">Loading Port Board...</div></div>';
      const r = await fetch('/api/port_board?port_id=' + encodeURIComponent(pid));
      pbData = await r.json();
      if (pbData.error) { list.innerHTML = `<div class="card"><div class="meta">${pbData.error}</div></div>`; return; }
      const p = pbData.port;
      document.getElementById('pb_header').innerHTML = `<b>${p.name} (${p.id}, ${p.country})</b> • Max Draft: ${p.max_draft || 'N/A'}m • RoRo: ${p.roro ? 'Yes' : 'Unlisted'}`;
      document.getElementById('sub_inport').textContent = `In Port (${pbData.in_port.length})`;
      document.getElementById('sub_inbound').textContent = `Inbound (${pbData.inbound.length})`;
      document.getElementById('sub_dep').textContent = `Departures (${pbData.departures.length})`;
      renderPBList();
    }

    function switchPBTab(sub, btn) {
      pbSub = sub;
      document.querySelectorAll('.subtabs .tab-btn').forEach(b => b.classList.remove('active'));
      if (btn) btn.classList.add('active');
      renderPBList();
    }

    function renderPBList() {
      const list = document.getElementById('pb_list');
      if (!pbData) return;
      const items = pbData[pbSub] || [];
      if (!items.length) {
        list.innerHTML = `<div class="card"><div class="meta">No vessels logged in <b>${pbSub}</b> yet for this port. (In-Port &amp; Inbound populate live; Departures accumulate as ships leave.)</div></div>`;
        return;
      }
      if (pbSub === 'departures') {
        list.innerHTML = items.map(d => `
          <div class="card">
            <div class="row-top"><span class="title">${d.name} ${d.imo ? '(IMO '+d.imo+')' : ''}</span><span class="pill IN_PORT_NOW">${d.action}</span></div>
            <div class="meta"><b>Type:</b> ${d.exact_type} | <b>Operator:</b> ${d.operator}<br/><b>Arrived:</b> ${d.arrived} → <b>Departed:</b> ${d.departed} | <b>Draft:</b> ${d.draft_in}m → ${d.draft_out}m</div>
            <div class="actions"><button class="btn btn-sec" onclick="openDossier('${d.mmsi}')">Dossier &amp; 6-Port Chain</button></div>
          </div>`).join('');
        return;
      }
      list.innerHTML = items.map(v => `
        <div class="card">
          <div class="row-top"><span class="title">${v.name} ${v.imo ? '(IMO '+v.imo+')' : ''}</span><span class="pill ${pbSub==='in_port'?'IN_PORT_NOW':'INBOUND_TO_TARGET'}">${pbSub==='in_port' ? (v.dwell_hrs + 'h stopped') : (v.dist_nm + ' NM')}</span></div>
          <div class="meta">
            <b>Type:</b> ${v.exact_type} (${v.loa || '?'}m) | <b>Draft:</b> ${v.draught || '?'}m (${v.load_state})<br/>
            ${pbSub==='inbound' ? `<b>Sea ETA:</b> ${v.eta} (${v.sog} kn) | ` : ''}<b>Dest:</b> ${v.destination}<br/>
            <b>Owner/Op:</b> ${v.owner} / ${v.operator} | <b>Cargo:</b> ${v.likely_cargo}
          </div>
          <div class="actions">
            <button class="btn" onclick="openDossier('${v.mmsi}')">Dossier &amp; Enrich</button>
            <button class="btn btn-sec" onclick="flyToShip(${v.lat}, ${v.lon}, '${v.mmsi}')">Map</button>
          </div>
        </div>`).join('');
    }

    function lcQuery() {
      return new URLSearchParams({
        target: document.getElementById('lc_target_id').value,
        start: document.getElementById('lc_start').value,
        end: document.getElementById('lc_end').value,
        type: document.getElementById('lc_type').value,
        min_loa: document.getElementById('lc_loa').value || '0',
        disc_days: document.getElementById('lc_disc').value || '4',
      }).toString();
    }

    function exportLaycanCSV() { window.location = '/api/laycan_csv?' + lcQuery(); }

    async function runLaycan() {
      const box = document.getElementById('lc_results');
      box.innerHTML = '<div class="card"><div class="meta">Computing real sea-route ETAs across global database...</div></div>';
      const r = await fetch('/api/laycan?' + lcQuery());
      const d = await r.json();
      lastLaycanList = d.candidates || [];
      if (!lastLaycanList.length) {
        box.innerHTML = `<div class="card"><div class="meta">No matches yet for <b>${d.target_name}</b>. Let AISStream run 60s for static LOA/destinations, or broaden Vessel Filter.</div></div>`;
        return;
      }
      box.innerHTML = `<div class="stat" style="padding:2px 4px"><b>${lastLaycanList.length}</b> candidates for <b>${d.target_name}</b></div>` +
        lastLaycanList.map(c => {
          const past = c.last_3_ports.length ? c.last_3_ports.join(' → ') : 'Logging...';
          const nxt = c.next_3_ports.length ? c.next_3_ports.join(' → ') : '—';
          const specHtml = c.enriched
            ? `<div class="specs"><b>${c.exact_type}</b> (${c.dwt}, Built ${c.year_built})<br/><b>Owner:</b> ${c.owner} | <b>Operator:</b> ${c.operator}<br/><b>Gear/Ramp:</b> ${c.crane_ramp_specs}<br/><b>Likely Cargo:</b> ${c.likely_cargo}</div>`
            : '';
          return `
            <div class="card">
              <div class="row-top">
                <span class="title">${c.name} ${c.imo ? '(IMO ' + c.imo + ')' : ''}</span>
                <span class="pill ${c.bucket}">${c.bucket.replace(/_/g, ' ')} • ${c.score}</span>
              </div>
              <div class="meta">
                <b>Type/Size:</b> ${c.exact_type} (${c.loa || '?'}m × ${c.beam || '?'}m) | <b>Draft:</b> ${c.draught || '?'}m (${c.load_state})<br/>
                <b>Now:</b> ${c.current_port} (${c.dist_nm} NM by sea, ${c.sog} kn) | <b style="color:#38bdf8">Est. Open: ${c.est_open_date}</b>
              </div>
              <div class="chain"><b>Past 3:</b> ${past}<br/><b>Next 3:</b> ${nxt}</div>
              ${specHtml}
              <div class="actions">
                <button class="btn" onclick="openDossier('${c.mmsi}')">Full Dossier</button>
                <button class="btn btn-gold" onclick="enrichOne('${c.mmsi}', this)">${c.enriched ? 'Re-Enrich' : 'Enrich IMO ($0.004)'}</button>
                <button class="btn btn-sec" onclick="flyToShip(${c.lat}, ${c.lon}, '${c.mmsi}')">Map &amp; Track</button>
              </div>
            </div>`;
        }).join('');
    }

    async function enrichOne(mmsi, btn) {
      if (btn) { btn.textContent = 'Enriching...'; btn.disabled = true; }
      await fetch('/api/enrich?mmsi=' + encodeURIComponent(mmsi));
      runLaycan();
    }

    async function batchEnrichTop() {
      const toDo = lastLaycanList.filter(c => !c.enriched).slice(0, 10);
      if (!toDo.length) { alert('Run Find Open Ships first (or top 10 are already enriched!).'); return; }
      if (!confirm(`Enrich ${toDo.length} un-enriched vessels via Exa Lite + Gemini (~$${(toDo.length*0.004).toFixed(3)} total)?`)) return;
      const box = document.getElementById('lc_results');
      for (let i = 0; i < toDo.length; i++) {
        box.insertAdjacentHTML('afterbegin', `<div class="stat">Enriching [${i+1}/${toDo.length}] ${toDo[i].name}...</div>`);
        await fetch('/api/enrich?mmsi=' + encodeURIComponent(toDo[i].mmsi));
      }
      runLaycan();
    }

    async function openDossier(mmsi) {
      const bg = document.getElementById('modalBg');
      const mc = document.getElementById('modalContent');
      bg.style.display = 'flex';
      mc.innerHTML = '<div class="meta">Loading vessel dossier...</div>';
      const r = await fetch('/api/vessel?mmsi=' + encodeURIComponent(mmsi));
      const d = await r.json();
      if (d.error) { mc.innerHTML = `<div class="meta">${d.error}</div>`; return; }
      const v = d.vessel, s = d.specs || {};
      mc.innerHTML = `
        <div class="row-top"><span class="title">${v.name} ${v.imo ? '(IMO '+v.imo+')' : ''}</span><button class="btn btn-sec" onclick="closeModal()">Close</button></div>
        <div class="meta" style="margin-top:8px">
          <b>MMSI:</b> ${v.mmsi} | <b>Callsign:</b> ${v.callsign || '—'} | <b>Flag:</b> ${s.flag || '—'}<br/>
          <b>Dimensions:</b> ${v.loa || '?'}m × ${v.beam || '?'}m | <b>Draft:</b> ${v.draught || '?'}m (${d.load_state})<br/>
          <b>Status:</b> ${d.nav_status} @ ${v.sog} kn | <b>Port:</b> ${v.current_port_name || 'At Sea'}<br/>
          <b>AIS Dest:</b> ${v.destination || '—'} (ETA: ${v.ais_eta || '—'})
        </div>
        <div class="chain">
          <b>Last 3 Ports:</b> ${d.last_3_ports.length ? d.last_3_ports.join(' → ') : 'None logged yet'}<br/>
          <b>Next 3 Ports:</b> ${d.next_3_ports.length ? d.next_3_ports.join(' → ') : '—'}
        </div>
        <div class="specs" style="margin-top:8px">
          <b>Exact Type:</b> ${s.exact_type || 'Not enriched yet'}<br/>
          <b>Owner:</b> ${s.owner || '—'}<br/>
          <b>Operator / Manager:</b> ${s.operator || '—'}<br/>
          <b>DWT / Built:</b> ${s.dwt || '—'} / ${s.year_built || '—'}<br/>
          <b>Crane / Ramp / Deck Specs:</b> ${s.crane_ramp_specs || '—'}<br/>
          <b>Likely Cargo:</b> ${s.likely_cargo || '—'}
        </div>
        <div class="actions">
          <button class="btn btn-gold" onclick="enrichDossier('${v.mmsi}')">${s.exact_type ? 'Refresh Enrichment ($0.004)' : 'Enrich Owner / Type / Cargo ($0.004)'}</button>
          <button class="btn btn-sec" onclick="closeModal(); flyToShip(${v.lat}, ${v.lon}, '${v.mmsi}')">Show Track on Map</button>
        </div>
      `;
    }

    async function enrichDossier(mmsi) {
      document.getElementById('modalContent').insertAdjacentHTML('beforeend', '<div class="stat" style="margin-top:8px">Querying Exa Lite + Gemini...</div>');
      await fetch('/api/enrich?mmsi=' + encodeURIComponent(mmsi) + '&force=1');
      openDossier(mmsi);
    }

    function closeModal() { document.getElementById('modalBg').style.display = 'none'; }

    function initMap() {
      if (mapReady) return;
      map = L.map('map', { minZoom: 2, worldCopyJump: true }).setView([38, 28], 5);
      const darkBase = L.layerGroup([
        L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/Canvas/World_Dark_Gray_Base/MapServer/tile/{z}/{y}/{x}', { maxNativeZoom: 16, maxZoom: 19 }),
        L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/Canvas/World_Dark_Gray_Reference/MapServer/tile/{z}/{y}/{x}', { maxNativeZoom: 16, maxZoom: 19, opacity: 0.85 })
      ]).addTo(map);
      const satBase = L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}', { maxNativeZoom: 18, maxZoom: 19 });
      const seamarks = L.tileLayer('https://tiles.openseamap.org/seamark/{z}/{x}/{y}.png', { maxZoom: 18, opacity: 0.9 }).addTo(map);
      L.control.layers({ 'Dark Maritime': darkBase, 'Satellite': satBase }, { 'OpenSeaMap': seamarks }).addTo(map);
      map.on('moveend', refreshMap);
      mapReady = true;
      refreshMap();
    }

    async function flyToShip(lat, lon, mmsi) {
      showTab('mapview', document.getElementById('tab_map'));
      setTimeout(async () => {
        map.setView([lat, lon], 9);
        refreshMap();
        if (mmsi) {
          const r = await fetch('/api/track?mmsi=' + encodeURIComponent(mmsi));
          const d = await r.json();
          if (trackLine) map.removeLayer(trackLine);
          if (d.points && d.points.length > 1) {
            trackLine = L.polyline(d.points, { color: '#38bdf8', weight: 2.5, dashArray: '5,5' }).addTo(map);
          }
        }
      }, 200);
    }

    function shipIcon(color, course) {
      return L.divIcon({
        className: '', iconSize: [14, 14], iconAnchor: [7, 7],
        html: `<svg width="14" height="14" viewBox="0 0 14 14" style="transform:rotate(${course}deg)"><polygon points="7,0 12,13 7,10 2,13" fill="${color}" stroke="#0f172a" stroke-width="1"/></svg>`
      });
    }

    async function refreshMap() {
      if (!mapReady) return;
      const b = map.getBounds();
      const r = await fetch(`/api/ships?s=${b.getSouth()}&w=${b.getWest()}&n=${b.getNorth()}&e=${b.getEast()}`);
      const d = await r.json();
      const seen = new Set();
      for (const s of d.ships) {
        seen.add(s.mmsi);
        const icon = shipIcon(COLORS[s.category] || COLORS.other, s.course || 0);
        const pop = `<div style="color:#0f172a;min-width:185px"><b>${s.name}</b><br/>IMO: ${s.imo || '—'} | ${s.loa || '?'}m | Draft: ${s.draught || '?'}m<br/>Dest: ${s.destination || '—'} | ${s.sog} kn<br/><button class="btn" style="margin-top:6px;width:100%" onclick="openDossier('${s.mmsi}')">Open Dossier &amp; Owner</button></div>`;
        if (markers[s.mmsi]) { markers[s.mmsi].setLatLng([s.lat, s.lon]).setIcon(icon); }
        else { markers[s.mmsi] = L.marker([s.lat, s.lon], { icon }).addTo(map).bindPopup(pop); }
      }
      for (const id of Object.keys(markers)) { if (!seen.has(id)) { map.removeLayer(markers[id]); delete markers[id]; } }
    }


    async function loadEnriched() {
      const box = document.getElementById('enr_list');
      const q = document.getElementById('enr_q').value.trim();
      const sub = document.getElementById('enr_sub').value;
      const r = await fetch(`/api/enriched?subtype=${encodeURIComponent(sub)}&q=${encodeURIComponent(q)}`);
      const d = await r.json();
      const items = d.vessels || [];
      if (!items.length) {
        box.innerHTML = '<div class="card"><div class="meta">No enriched vessels match yet. Enrich ships from <b>Laycan</b> or <b>Ship Search</b> to build your permanent Sprnt fleet registry.</div></div>';
        return;
      }
      box.innerHTML = `<div class="stat" style="padding:2px 4px">Showing <b>${items.length}</b> permanently enriched vessels</div>` +
        items.map(v => {
          const past = v.last_3_ports.length ? v.last_3_ports.join(' → ') : '—';
          const nxt = v.next_3_ports.length ? v.next_3_ports.join(' → ') : '—';
          const mapBtn = (v.lat !== null && v.lon !== null)
            ? `<button class="btn btn-sec" onclick="flyToShip(${v.lat}, ${v.lon}, '${v.mmsi}')">Map &amp; Track</button>`
            : '';
          return `
            <div class="card">
              <div class="row-top">
                <span class="title">${v.name} ${v.imo ? '(IMO ' + v.imo + ')' : ''}</span>
                <span class="pill INBOUND_TO_TARGET">${v.exact_type}</span>
              </div>
              <div class="specs">
                <b>Owner:</b> ${v.owner} &nbsp;|&nbsp; <b>Operator:</b> ${v.operator}<br/>
                <b>DWT / Built / Flag:</b> ${v.dwt} / ${v.year_built} / ${v.flag}<br/>
                <b>Gear / Ramp / Deck:</b> ${v.crane_ramp_specs}<br/>
                <b>Likely Cargo:</b> ${v.likely_cargo}
              </div>
              <div class="meta">
                <b>Live:</b> ${v.current_port} (${v.sog} kn, Draft ${v.draught || '?'}m, LOA ${v.loa || '?'}m) &nbsp;|&nbsp; <b>Dest:</b> ${v.destination}
              </div>
              <div class="chain"><b>Past 3:</b> ${past}<br/><b>Next 3:</b> ${nxt}</div>
              <div class="actions">
                <button class="btn" onclick="openDossier('${v.mmsi}')">Full Dossier</button>
                ${mapBtn}
              </div>
            </div>`;
        }).join('');
    }

    function exportEnrichedCSV() {
      const q = document.getElementById('enr_q').value.trim();
      const sub = document.getElementById('enr_sub').value;
      window.location = `/api/enriched_csv?subtype=${encodeURIComponent(sub)}&q=${encodeURIComponent(q)}`;
    }

    let ssTimer = null;
    function runShipSearch() {
      clearTimeout(ssTimer);
      ssTimer = setTimeout(async () => {
        const q = document.getElementById('ss_q').value.trim();
        const box = document.getElementById('ss_list');
        if (q.length < 2) {
          box.innerHTML = '<div class="card"><div class="meta">Type at least 2 characters (Ship Name, IMO, MMSI, Owner, or Operator)...</div></div>';
          return;
        }
        const r = await fetch('/api/search_vessels?q=' + encodeURIComponent(q));
        const d = await r.json();
        const items = d.vessels || [];
        if (!items.length) {
          box.innerHTML = `<div class="card"><div class="meta">No vessels found matching <b>${q}</b> in your live DB yet.</div></div>`;
          return;
        }
        box.innerHTML = `<div class="stat" style="padding:2px 4px">Found <b>${items.length}</b> matching vessels</div>` +
          items.map(v => `
            <div class="card">
              <div class="row-top">
                <span class="title">${v.name} ${v.imo ? '(IMO ' + v.imo + ')' : ''}</span>
                <span class="pill ${v.enriched ? 'IN_PORT_NOW' : 'NEARBY_POSITIONING'}">${v.enriched ? 'ENRICHED' : v.category}</span>
              </div>
              <div class="meta">
                <b>Type:</b> ${v.exact_type} (${v.loa || '?'}m × ${v.beam || '?'}m, Draft ${v.draught || '?'}m)<br/>
                <b>Position:</b> ${v.current_port} (${v.sog} kn) &nbsp;|&nbsp; <b>Dest:</b> ${v.destination}<br/>
                <b>Owner / Op:</b> ${v.owner} / ${v.operator} &nbsp;|&nbsp; <b>Cargo:</b> ${v.likely_cargo}
              </div>
              <div class="actions">
                <button class="btn" onclick="openDossier('${v.mmsi}')">Dossier &amp; Enrich</button>
                <button class="btn btn-sec" onclick="flyToShip(${v.lat}, ${v.lon}, '${v.mmsi}')">Show Position &amp; Track</button>
              </div>
            </div>`).join('');
      }, 220);
    }

    async function pollStats() {
      try {
        const r = await fetch('/api/stats');
        const s = await r.json();
        document.getElementById('dbstat').textContent = `${s.connected ? 'LIVE' : 'CONNECTING'} • ${s.vessels} ships • ${s.ports} ports • ${s.enriched} enriched ($${s.exa_spend.toFixed(3)})`;
        document.getElementById('tab_enriched').textContent = `Enriched (${s.enriched})`;
      } catch (e) {}
    }
    pollStats();
    setInterval(pollStats, 5000);
  </script>
</body>
</html>
"""


class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args): return

    def send_json(self, obj, code=200):
        body = json.dumps(obj).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        parsed = urlparse(self.path)
        qs = parse_qs(parsed.query)

        if parsed.path == "/":
            raw = HTML_PAGE.encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(raw)))
            self.end_headers()
            self.wfile.write(raw)
            return

        if parsed.path == "/api/stats":
            with MEM_LOCK: vc = len(VESSELS)
            with DB_LOCK:
                con = sqlite3.connect(DB_PATH)
                enr = con.execute("SELECT COUNT(*) FROM vessel_specs").fetchone()[0]
                con.close()
            self.send_json({"connected": STATS["connected"], "vessels": vc, "ports": STATS["ports_loaded"], "enriched": enr, "exa_spend": STATS["exa_spend"]})
            return

        if parsed.path == "/api/ports":
            q = (qs.get("q", [""])[0]).strip().upper()
            out = []
            for cid, c in CLUSTERS.items():
                if q in c["name"].upper() or q in cid:
                    out.append({"id": cid, "name": c["name"], "country": c["country"], "roro": True})
            for pid, p in PORTS_BY_ID.items():
                if q in pid or q in p["name"].upper() or any(q in al for al in p["aliases"]):
                    out.append({"id": pid, "name": p["name"], "country": p["country"], "roro": p["roro"]})
                    if len(out) >= 25: break
            self.send_json({"ports": out})
            return

        if parsed.path == "/api/port_board":
            pid = qs.get("port_id", ["TRGEM"])[0].upper()
            self.send_json(get_port_board(pid))
            return

        if parsed.path == "/api/ships":
            s, w = float(qs.get("s", [-90])[0]), float(qs.get("w", [-180])[0])
            n, e = float(qs.get("n", [90])[0]), float(qs.get("e", [180])[0])
            with MEM_LOCK:
                items = [v for v in VESSELS.values() if s <= v["lat"] <= n and w <= v["lon"] <= e]
            items.sort(key=lambda x: -x["last_seen"])
            self.send_json({"ships": items[:500]})
            return

        if parsed.path == "/api/vessel":
            mmsi = qs.get("mmsi", [""])[0].strip()
            with MEM_LOCK: v = dict(VESSELS.get(mmsi, {}))
            if not v:
                self.send_json({"error": "Vessel not found"}); return
            specs_map = get_specs_map()
            spec = specs_map.get(v["imo"]) or specs_map.get(f"MMSI:{mmsi}") or {}
            with DB_LOCK:
                con = sqlite3.connect(DB_PATH)
                con.row_factory = sqlite3.Row
                pcs = [dict(r) for r in con.execute("SELECT * FROM port_calls WHERE mmsi=? ORDER BY arrived_at DESC LIMIT 20", (mmsi,)).fetchall()]
                con.close()
            last_3, next_3 = build_six_port_chain(v, pcs, spec)
            self.send_json({
                "vessel": v, "specs": spec, "last_3_ports": last_3, "next_3_ports": next_3,
                "load_state": infer_load_state(v["draught"], v["max_draught"], v["min_draught"], v["loa"]),
                "nav_status": NAV_STATUS_MAP.get(v["nav_status"], "Unknown"),
            })
            return

        if parsed.path == "/api/track":
            mmsi = qs.get("mmsi", [""])[0].strip()
            with DB_LOCK:
                con = sqlite3.connect(DB_PATH)
                pts = con.execute("SELECT lat, lon FROM tracks WHERE mmsi=? ORDER BY ts ASC LIMIT 300", (mmsi,)).fetchall()
                con.close()
            self.send_json({"points": [[p[0], p[1]] for p in pts]})
            return

        if parsed.path in ("/api/enriched", "/api/enriched_csv"):
            sub = qs.get("subtype", ["all"])[0]
            q = qs.get("q", [""])[0]
            items = fleet_views.get_enriched_fleet(DB_PATH, VESSELS, MEM_LOCK, DB_LOCK, build_six_port_chain, subtype=sub, q=q)
            if parsed.path == "/api/enriched":
                self.send_json({"vessels": items})
                return
            buf = io.StringIO()
            fields = ["name", "imo", "mmsi", "exact_type", "subtype_group", "owner", "operator", "flag", "dwt",
                      "year_built", "crane_ramp_specs", "likely_cargo", "loa", "beam", "draught", "sog",
                      "current_port", "destination", "lat", "lon", "last_3_ports", "next_3_ports", "enriched_at"]
            w = csv.DictWriter(buf, fieldnames=fields, extrasaction="ignore")
            w.writeheader()
            for it in items:
                row = dict(it)
                row["last_3_ports"] = " -> ".join(it["last_3_ports"])
                row["next_3_ports"] = " -> ".join(it["next_3_ports"])
                w.writerow(row)
            raw = buf.getvalue().encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/csv")
            self.send_header("Content-Disposition", 'attachment; filename="sprnt_enriched_fleet.csv"')
            self.send_header("Content-Length", str(len(raw)))
            self.end_headers()
            self.wfile.write(raw)
            return

        if parsed.path == "/api/search_vessels":
            q = qs.get("q", [""])[0]
            items = fleet_views.search_all_vessels(VESSELS, get_specs_map(), MEM_LOCK, q=q)
            self.send_json({"vessels": items})
            return

        if parsed.path == "/api/enrich":
            mmsi = qs.get("mmsi", [""])[0].strip()
            force = qs.get("force", ["0"])[0] == "1"
            self.send_json(enrich_vessel_by_mmsi(mmsi, force=force))
            return

        if parsed.path in ("/api/laycan", "/api/laycan_csv"):
            target = qs.get("target", ["CLUSTER:DERINCE_GEMLIK"])[0]
            start = qs.get("start", ["2026-12-01"])[0]
            end = qs.get("end", ["2026-12-15"])[0]
            vtype = qs.get("type", ["roro_mpp"])[0]
            min_loa = float(qs.get("min_loa", ["100"])[0] or 0)
            disc = float(qs.get("disc_days", ["4"])[0] or 4)
            t_name, cands = screen_laycan(target, start, end, vtype, min_loa, disc)
            if parsed.path == "/api/laycan":
                self.send_json({"target_name": t_name, "candidates": cands})
                return
            buf = io.StringIO()
            fields = ["score", "bucket", "name", "imo", "mmsi", "exact_type", "owner", "operator", "dwt",
                      "year_built", "crane_ramp_specs", "likely_cargo", "loa", "beam", "draught", "load_state",
                      "current_port", "dist_nm", "sog", "destination", "est_arrival", "est_open_date",
                      "last_3_ports", "next_3_ports"]
            w = csv.DictWriter(buf, fieldnames=fields, extrasaction="ignore")
            w.writeheader()
            for c in cands:
                row = dict(c)
                row["last_3_ports"] = " -> ".join(c["last_3_ports"])
                row["next_3_ports"] = " -> ".join(c["next_3_ports"])
                w.writerow(row)
            raw = buf.getvalue().encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/csv")
            self.send_header("Content-Disposition", f'attachment; filename="openmarine_v2_{start}.csv"')
            self.send_header("Content-Length", str(len(raw)))
            self.end_headers()
            self.wfile.write(raw)
            return

        self.send_response(404)
        self.end_headers()


if __name__ == "__main__":
    load_world_ports()
    init_db()
    threading.Thread(target=db_flusher_loop, daemon=True).start()
    threading.Thread(target=lambda: asyncio.run(stream_aisstream()), daemon=True).start()
    print(f"[*] OpenMarine v2 running on http://127.0.0.1:{PORT}")
    ThreadingHTTPServer(("0.0.0.0", PORT), Handler).serve_forever()
