"""Runs the solvers on the benchmark instances.

    python -m lattice_bench.run [--solvers lattice,minisat22,cadical195] [--timeout 300] [--jobs 6]

Each (instance, solver) pair runs in its own process with the time limit. Results are appended
to results/runs.jsonl as they finish (so an interrupted run resumes where it stopped).

Every answer is checked:
* SAT: the model is checked against the formula (here, independently of the solver);
* UNSAT from Lattice: its DRAT proof is verified by lattice-check, then deleted.
"""
from __future__ import annotations

import argparse
import json
import lzma
import re
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "bench" / "data"
RESULTS = ROOT / "results"
TMP = DATA / "tmp"
CHECK_LIMIT = 3600  # seconds for verifying one proof


def exe(*candidates: str) -> str:
    for c in candidates:
        p = ROOT / c
        if p.exists():
            return str(p)
    raise FileNotFoundError(f"build first: none of {candidates}")


LATTICE = exe("build/Release/lattice.exe", "build/lattice")
CHECKER = exe("checker/target/release/lattice-check.exe", "checker/target/release/lattice-check")


SATLIB: dict[str, Path] = {}


def satlib_instances() -> list[dict]:
    """SATLIB uf250-1065 (satisfiable) and uuf250-1065 (unsatisfiable): random 3-SAT, 250
    variables, 1,065 clauses, at the satisfiability threshold."""
    out = []
    for kind in ["sat", "unsat"]:
        for p in sorted((DATA / "satlib" / kind).rglob("*.cnf")):
            SATLIB[p.stem] = p
            out.append({"hash": p.stem, "family": "uf250" if kind == "sat" else "uuf250", "result": kind, "bytes": p.stat().st_size})
    return out


def cnf_path(h: str) -> Path:
    if h in SATLIB:
        return SATLIB[h]
    p = TMP / f"{h}.cnf"
    if not p.exists():
        TMP.mkdir(parents=True, exist_ok=True)
        part = p.with_suffix(".part")
        part.write_bytes(lzma.decompress((DATA / "cnf" / f"{h}.cnf.xz").read_bytes()))
        part.replace(p)
    return p


def read_clauses(path: Path) -> list[list[int]]:
    out, cur = [], []
    with open(path, "rb") as f:
        for line in f:
            if line[:1] == b"%":  # SATLIB end marker; a stray "0" follows it
                break
            if line[:1] in (b"c", b"p"):
                continue
            for tok in line.split():
                x = int(tok)
                if x == 0:
                    out.append(cur)
                    cur = []
                else:
                    cur.append(x)
    if cur:
        out.append(cur)
    return out


def model_ok(path: Path, values: set[int]) -> bool:
    return all(any(l in values for l in c) for c in read_clauses(path))


def run_lattice(h: str, timeout: float, extra: list[str], tag: str) -> dict:
    path = cnf_path(h)
    proof = TMP / f"{h}.{tag}.drat"
    t0 = time.perf_counter()
    try:
        p = subprocess.run([LATTICE, "--timeout", str(timeout), "--proof", str(proof), *extra, str(path)],
                           capture_output=True, text=True, timeout=timeout + 120)
        out = p.stdout
    except subprocess.TimeoutExpired:
        proof.unlink(missing_ok=True)
        return {"status": "unknown", "seconds": timeout, "note": "killed"}
    wall = time.perf_counter() - t0
    m = re.search(r"^s (\w+)", out, re.M)
    status = {"SATISFIABLE": "sat", "UNSATISFIABLE": "unsat"}.get(m.group(1) if m else "", "unknown")
    stats = json.loads(out.split("c stats ", 1)[1]) if "c stats " in out else {}
    r = {"status": status, "seconds": stats.get("solve_s", wall), "stats": stats}
    if status == "sat":
        vals = {int(x) for line in out.splitlines() if line.startswith("v ") for x in line[2:].split() if x != "0"}
        r["model_ok"] = model_ok(path, vals)
    elif status == "unsat":
        r["proof_mb"] = round(proof.stat().st_size / 2**20, 1)
        t1 = time.perf_counter()
        try:
            c = subprocess.run([CHECKER, str(path), str(proof)], capture_output=True, text=True, timeout=CHECK_LIMIT)
            r["proof"] = "verified" if "s VERIFIED" in c.stdout else "rejected"
            if r["proof"] == "rejected":
                r["proof_message"] = c.stdout[:500]
        except subprocess.TimeoutExpired:
            r["proof"] = "check timed out"
        r["check_seconds"] = round(time.perf_counter() - t1, 2)
    proof.unlink(missing_ok=True)
    return r


def run_pysat(h: str, name: str, timeout: float) -> dict:
    path = cnf_path(h)
    try:
        p = subprocess.run([sys.executable, "-m", "lattice_bench.pysat_child", name, str(path), str(timeout)],
                           capture_output=True, text=True, timeout=timeout + 300, cwd=ROOT / "bench")
    except subprocess.TimeoutExpired:
        return {"status": "unknown", "seconds": timeout, "note": "killed"}
    try:
        return json.loads(p.stdout.strip().splitlines()[-1])
    except (IndexError, json.JSONDecodeError):
        # The child died without printing a result: keep its exit code and the end of stderr.
        return {"status": "error", "seconds": timeout, "note": f"exit {p.returncode}: {p.stderr.strip()[-300:]}"}


SOLVERS = {
    "lattice": lambda h, t: run_lattice(h, t, [], "lattice"),
    "lattice-noelim": lambda h, t: run_lattice(h, t, ["--no-elim"], "noelim"),
    "lattice-luby": lambda h, t: run_lattice(h, t, ["--restarts", "luby"], "luby"),
    "lattice-glucose": lambda h, t: run_lattice(h, t, ["--restarts", "glucose"], "glucose"),
    "minisat22": lambda h, t: run_pysat(h, "minisat22", t),
    "cadical195": lambda h, t: run_pysat(h, "cadical195", t),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--solvers", default="lattice,minisat22,cadical195")
    ap.add_argument("--timeout", type=float, default=300)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--out", default=None)
    ap.add_argument("--suite", choices=["competition", "satlib"], default="competition")
    a = ap.parse_args()
    if a.suite == "satlib":
        insts = satlib_instances()
        a.out = a.out or "runs_satlib.jsonl"
    else:
        insts = json.loads((DATA / "instances.json").read_text())["instances"]
        a.out = a.out or "runs.jsonl"
    RESULTS.mkdir(exist_ok=True)
    out_path = RESULTS / a.out
    done = set()
    if out_path.exists():
        for line in out_path.read_text().splitlines():
            r = json.loads(line)
            done.add((r["hash"], r["solver"]))
    jobs = [(m, s) for m in insts for s in a.solvers.split(",") if (m["hash"], s) not in done]
    # Longest-looking work first (bigger files), so the pool does not end on one slow job.
    jobs.sort(key=lambda j: -j[0]["bytes"])
    # Decompress everything first (one thread), so parallel jobs never race on a file.
    for m in insts:
        cnf_path(m["hash"])
    lock = threading.Lock()
    t0 = time.time()
    count = [0]

    def one(job):
        m, s = job
        try:
            r = SOLVERS[s](m["hash"], a.timeout)
        except Exception as e:  # noqa: BLE001 - record it, keep the other runs going
            r = {"status": "error", "seconds": a.timeout, "note": repr(e)[:300]}
        row = {"hash": m["hash"], "family": m["family"], "expected": m["result"], "solver": s, "timeout": a.timeout} | r
        if row["status"] in ("sat", "unsat") and m["result"] in ("sat", "unsat") and row["status"] != m["result"]:
            row["wrong"] = True
        with lock:
            with open(out_path, "a") as f:
                f.write(json.dumps(row) + "\n")
            count[0] += 1
            extra = f" proof {row.get('proof')} ({row.get('check_seconds')} s)" if "proof" in row else ""
            print(f"[{count[0]}/{len(jobs)} {time.time() - t0:.0f}s] {s:16} {m['family'][:24]:24} {row['status']:8} {row['seconds']:7.1f}s{extra}"
                  + (" WRONG" if row.get("wrong") else "") + (" BAD MODEL" if row.get("model_ok") is False else ""), flush=True)

    with ThreadPoolExecutor(a.jobs) as pool:
        list(pool.map(one, jobs))


if __name__ == "__main__":
    main()
