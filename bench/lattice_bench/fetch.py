"""Picks and downloads the benchmark instances.

    python -m lattice_bench.fetch [--count 100]
    python -m lattice_bench.fetch --satlib

From the SAT Competition 2023 main track (via GBD, the Global Benchmark Database), the instances
with fewer than 300,000 clauses, then a seeded random sample of them. Instances are stored
compressed (.cnf.xz, as served) in bench/data/cnf/, with bench/data/instances.json listing hash,
family, known result and original file name.

With --satlib: SATLIB's uf250-1065 and uuf250-1065 archives (random 3-SAT, 100 instances each),
extracted into bench/data/satlib/sat and bench/data/satlib/unsat.
"""
from __future__ import annotations

import argparse
import io
import json
import random
import sqlite3
import tarfile
import time
import urllib.parse
import urllib.request
from pathlib import Path

DATA = Path(__file__).resolve().parents[1] / "data"
GBD = "https://benchmark-database.de"
QUERY = "track=main_2023 and clauses<300000"
SATLIB = "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT"


def fetch_satlib():
    for kind, name in [("sat", "uf250-1065"), ("unsat", "uuf250-1065")]:
        dest = DATA / "satlib" / kind
        dest.mkdir(parents=True, exist_ok=True)
        with tarfile.open(fileobj=io.BytesIO(get(f"{SATLIB}/{name}.tar.gz")), mode="r:gz") as tar:
            members = [m for m in tar.getmembers() if m.isfile() and m.name.endswith(".cnf")]
            tar.extractall(dest, members=members, filter="data")
        print(f"{name}: {len(members)} files in {dest}")


def get(url: str, tries: int = 5) -> bytes:
    for k in range(tries):
        try:
            with urllib.request.urlopen(url, timeout=300) as r:
                return r.read()
        except OSError:
            if k == tries - 1:
                raise
            time.sleep(5 * (k + 1))
    return b""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=100)
    ap.add_argument("--seed", type=int, default=2023)
    ap.add_argument("--satlib", action="store_true", help="fetch the SATLIB uf250/uuf250 sets instead")
    a = ap.parse_args()
    if a.satlib:
        return fetch_satlib()
    DATA.mkdir(parents=True, exist_ok=True)
    meta_path = DATA / "meta.db"
    if not meta_path.exists():
        meta_path.write_bytes(get(f"{GBD}/getdatabase/meta"))
    q = urllib.parse.quote(QUERY)
    hashes = sorted(line.rsplit("/", 1)[-1].strip() for line in get(f"{GBD}/getinstances?context=cnf&query={q}").decode().splitlines() if line.strip())
    db = sqlite3.connect(meta_path)
    meta = {}
    for h in hashes:
        row = db.execute("select family, result, filename from features where hash = ?", (h,)).fetchone()
        meta[h] = {"hash": h, "family": row[0] if row else None, "result": row[1] if row else None, "filename": row[2] if row else None}
    print(f"{len(hashes)} instances match '{QUERY}'")
    pick = sorted(random.Random(a.seed).sample(hashes, min(a.count, len(hashes))))
    (DATA / "cnf").mkdir(exist_ok=True)
    out = []
    for i, h in enumerate(pick):
        path = DATA / "cnf" / f"{h}.cnf.xz"
        if not path.exists():
            path.write_bytes(get(f"{GBD}/file/{h}"))
        m = meta[h] | {"bytes": path.stat().st_size}
        out.append(m)
        print(f"  {i + 1}/{len(pick)} {h} {m['family']} {m['result']} {m['bytes'] // 1024} KB", flush=True)
    (DATA / "instances.json").write_text(json.dumps({"source": f"{GBD}, query '{QUERY}'", "seed": a.seed, "matching": len(hashes), "instances": out}, indent=1))
    fam = {}
    for m in out:
        fam[m["family"]] = fam.get(m["family"], 0) + 1
    print("families:", len(fam), "results:", {r: sum(m["result"] == r for m in out) for r in {m["result"] for m in out}})


if __name__ == "__main__":
    main()
