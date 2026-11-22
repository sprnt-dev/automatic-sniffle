import sqlite3
from datetime import datetime, timezone


def get_enriched_fleet(db_path, vessels_dict, mem_lock, db_lock, build_chain_fn, subtype="", q=""):
    subtype = (subtype or "").strip().lower()
    q = (q or "").strip().lower()

    with db_lock:
        con = sqlite3.connect(db_path)
        con.row_factory = sqlite3.Row
        specs = [dict(r) for r in con.execute("SELECT * FROM vessel_specs ORDER BY enriched_at DESC").fetchall()]
        pc_rows = [dict(r) for r in con.execute("SELECT * FROM port_calls ORDER BY arrived_at DESC LIMIT 10000").fetchall()]
        con.close()

    pc_by_mmsi = {}
    for r in pc_rows:
        pc_by_mmsi.setdefault(r["mmsi"], []).append(r)

    with mem_lock:
        live_by_mmsi = {k: dict(v) for k, v in vessels_dict.items()}
        live_by_imo = {v["imo"]: dict(v) for v in vessels_dict.values() if v.get("imo")}

    out = []
    for s in specs:
        if subtype and subtype != "all" and (s.get("subtype_group") or "").lower() != subtype:
            continue
        v = live_by_mmsi.get(s.get("mmsi") or "") or live_by_imo.get(s.get("imo") or "") or {}
        name = v.get("name") or s.get("imo") or s.get("mmsi") or "Unknown"
        hay = " ".join([
            str(name), str(s.get("imo") or ""), str(s.get("mmsi") or ""),
            str(s.get("exact_type") or ""), str(s.get("owner") or ""),
            str(s.get("operator") or ""), str(s.get("likely_cargo") or ""),
            str(s.get("flag") or ""), str(v.get("destination") or ""),
        ]).lower()
        if q and q not in hay:
            continue

        last_3, next_3 = build_chain_fn(v, pc_by_mmsi.get(s.get("mmsi") or "", []), s)
        enr_str = datetime.fromtimestamp(s["enriched_at"], timezone.utc).strftime("%Y-%m-%d %H:%M") if s.get("enriched_at") else "—"
        out.append({
            "mmsi": v.get("mmsi") or s.get("mmsi") or "",
            "imo": v.get("imo") or ("" if str(s.get("imo", "")).startswith("MMSI:") else s.get("imo", "")),
            "name": name,
            "exact_type": s.get("exact_type") or "Unknown",
            "subtype_group": s.get("subtype_group") or "other",
            "owner": s.get("owner") or "Unknown",
            "operator": s.get("operator") or "Unknown",
            "flag": s.get("flag") or "Unknown",
            "dwt": s.get("dwt") or "Unknown",
            "year_built": s.get("year_built") or "Unknown",
            "crane_ramp_specs": s.get("crane_ramp_specs") or "Unknown",
            "likely_cargo": s.get("likely_cargo") or "Unknown",
            "loa": v.get("loa") or 0,
            "beam": v.get("beam") or 0,
            "draught": v.get("draught") or 0,
            "sog": v.get("sog") or 0,
            "destination": v.get("destination") or "—",
            "current_port": v.get("current_port_name") or ("At Sea" if v else "Offline / Cached"),
            "lat": v.get("lat"),
            "lon": v.get("lon"),
            "last_3_ports": last_3,
            "next_3_ports": next_3,
            "enriched_at": enr_str,
        })
    return out


def search_all_vessels(vessels_dict, specs_map, mem_lock, q="", limit=80):
    q = (q or "").strip().lower()
    if not q:
        return []
    with mem_lock:
        all_v = [dict(v) for v in vessels_dict.values()]

    matches = []
    for v in all_v:
        spec = specs_map.get(v.get("imo") or "") or specs_map.get(f"MMSI:{v['mmsi']}") or {}
        hay = " ".join([
            str(v.get("name") or ""), str(v.get("imo") or ""), str(v.get("mmsi") or ""),
            str(v.get("callsign") or ""), str(v.get("destination") or ""),
            str(v.get("current_port_name") or ""), str(spec.get("exact_type") or ""),
            str(spec.get("owner") or ""), str(spec.get("operator") or ""),
            str(spec.get("likely_cargo") or ""),
        ]).lower()
        if q not in hay:
            continue

        rank = 0
        if str(v.get("imo") or "").lower() == q or str(v.get("mmsi") or "").lower() == q:
            rank += 100
        if str(v.get("name") or "").lower().startswith(q):
            rank += 50
        if spec:
            rank += 20

        matches.append({
            "rank": rank,
            "last_seen": v.get("last_seen") or 0,
            "mmsi": v["mmsi"],
            "imo": v.get("imo") or "",
            "name": v.get("name") or f"MMSI {v['mmsi']}",
            "category": v.get("category") or "other",
            "exact_type": spec.get("exact_type") or v.get("size_class") or v.get("category") or "Unknown",
            "owner": spec.get("owner") or "—",
            "operator": spec.get("operator") or "—",
            "likely_cargo": spec.get("likely_cargo") or "—",
            "enriched": bool(spec),
            "loa": v.get("loa") or 0,
            "beam": v.get("beam") or 0,
            "draught": v.get("draught") or 0,
            "sog": v.get("sog") or 0,
            "destination": v.get("destination") or "—",
            "current_port": v.get("current_port_name") or "At Sea",
            "lat": v.get("lat"),
            "lon": v.get("lon"),
        })

    matches.sort(key=lambda x: (-x["rank"], -x["last_seen"]))
    return matches[:limit]
