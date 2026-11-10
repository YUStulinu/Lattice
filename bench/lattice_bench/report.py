"""Summarises the benchmark runs: solved counts, PAR-2, cactus plots, per-family results, and the
checking of every answer.

    python -m lattice_bench.report

Reads results/runs.jsonl (and runs_satlib.jsonl, runs_ablation.jsonl - SATLIB ablation - if present); writes results/summary.json and
docs/cactus.png, docs/scatter.png.
"""
from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
RESULTS, DOCS = ROOT / "results", ROOT / "docs"
NAMES = {"lattice": "Lattice", "minisat22": "MiniSat 2.2", "cadical195": "CaDiCaL 1.9.5",
         "lattice-noelim": "Lattice, no elimination", "lattice-luby": "Lattice, Luby only", "lattice-glucose": "Lattice, Glucose only"}


def load(name: str) -> list[dict]:
    p = RESULTS / name
    return [json.loads(line) for line in p.read_text().splitlines()] if p.exists() else []


def summarise(rows: list[dict]) -> dict:
    by = defaultdict(list)
    for r in rows:
        by[r["solver"]].append(r)
    out = {}
    for s, rs in by.items():
        t = rs[0]["timeout"]
        solved = [r for r in rs if r["status"] in ("sat", "unsat")]
        par2 = sum(r["seconds"] if r["status"] in ("sat", "unsat") else 2 * t for r in rs) / len(rs)
        e = {"runs": len(rs), "solved": len(solved), "sat": sum(r["status"] == "sat" for r in rs),
             "unsat": sum(r["status"] == "unsat" for r in rs), "par2": round(par2, 1),
             "wrong": sum(bool(r.get("wrong")) for r in rs), "bad_models": sum(r.get("model_ok") is False for r in rs),
             "errors": sum(r["status"] == "error" for r in rs)}
        proofs = [r for r in rs if "proof" in r]
        if proofs:
            ratios = [r["check_seconds"] / max(r["seconds"], 0.01) for r in proofs if r["proof"] == "verified"]
            e["proofs"] = {"checked": len(proofs), "verified": sum(r["proof"] == "verified" for r in proofs),
                           "rejected": sum(r["proof"] == "rejected" for r in proofs),
                           "check_timed_out": sum(r["proof"] == "check timed out" for r in proofs),
                           "check_over_solve_median": round(float(np.median(ratios)), 2) if ratios else None,
                           "check_seconds_max": max(r["check_seconds"] for r in proofs),
                           "proof_mb_median": float(np.median([r["proof_mb"] for r in proofs])),
                           "proof_mb_max": max(r["proof_mb"] for r in proofs)}
        out[s] = e
    return out


def per_family(rows: list[dict], solvers: list[str]) -> dict:
    fam = defaultdict(lambda: defaultdict(int))
    count = defaultdict(set)
    for r in rows:
        count[r["family"]].add(r["hash"])
        if r["status"] in ("sat", "unsat"):
            fam[r["family"]][r["solver"]] += 1
    return {f: {"instances": len(count[f])} | {s: fam[f][s] for s in solvers} for f in sorted(count, key=lambda f: -len(count[f]))}


def cactus(ax, rows: list[dict], solvers: list[str], title: str):
    for s in solvers:
        ts = sorted(r["seconds"] for r in rows if r["solver"] == s and r["status"] in ("sat", "unsat"))
        ax.step(range(1, len(ts) + 1), ts, where="post", label=f"{NAMES.get(s, s)} ({len(ts)})", lw=1.8)
    ax.set(xlabel="instances solved", ylabel="time per instance (s), sorted", yscale="log", title=title)
    ax.grid(alpha=0.3, which="both")
    ax.legend(fontsize=8, loc="upper left")


def scatter(ax, rows: list[dict], other: str, t: float):
    by = defaultdict(dict)
    for r in rows:
        by[r["hash"]][r["solver"]] = r
    pts = defaultdict(lambda: ([], []))
    for h, d in by.items():
        if "lattice" not in d or other not in d:
            continue
        f = lambda r: r["seconds"] if r["status"] in ("sat", "unsat") else 2 * t  # noqa: E731
        kind = "crashed" if d[other]["status"] == "error" else "SAT" if "sat" in (d["lattice"]["status"], d[other]["status"]) else "UNSAT or unsolved"
        pts[kind][0].append(max(f(d[other]), 0.01))
        pts[kind][1].append(max(f(d["lattice"]), 0.01))
    style = {"SAT": dict(c="C2", marker="o"), "UNSAT or unsolved": dict(c="C3", marker="o"), "crashed": dict(c="k", marker="x")}
    for kind, (xs, ys) in pts.items():
        label = f"{NAMES[other]} crashed" if kind == "crashed" else kind
        ax.scatter(xs, ys, s=18, alpha=0.8, label=f"{label} ({len(xs)})", **style[kind])
    ax.legend(fontsize=8, loc="lower right")
    lim = [0.01, 2 * t * 1.3]
    ax.plot(lim, lim, color="gray", lw=0.8)
    for v in [t]:
        ax.axhline(v, color="gray", ls=":", lw=0.7)
        ax.axvline(v, color="gray", ls=":", lw=0.7)
    ax.set(xscale="log", yscale="log", xlim=lim, ylim=lim, xlabel=f"{NAMES[other]} (s)", ylabel="Lattice (s)",
           title=f"Lattice against {NAMES[other]} (timeouts at 2x)")
    ax.grid(alpha=0.25, which="both")


def main():
    main_rows = load("runs.jsonl")
    satlib_rows = load("runs_satlib.jsonl")
    ablation_rows = load("runs_ablation.jsonl")
    solvers = [s for s in ["lattice", "minisat22", "cadical195"] if any(r["solver"] == s for r in main_rows)]
    summary = {"competition": summarise(main_rows), "families": per_family(main_rows, solvers)}
    if satlib_rows:
        summary["satlib"] = summarise(satlib_rows)
    if ablation_rows:
        summary["ablation_satlib"] = summarise(ablation_rows + [r for r in satlib_rows if r["solver"] == "lattice"])
    # Instances only Lattice solved / only the others solved.
    by = defaultdict(dict)
    for r in main_rows:
        by[r["hash"]][r["solver"]] = r["status"] in ("sat", "unsat")
    summary["unique"] = {s: sum(1 for d in by.values() if d.get(s) and not any(v for k, v in d.items() if k != s)) for s in solvers}
    summary["lattice_vs"] = {o: {"both": sum(1 for d in by.values() if d.get("lattice") and d.get(o)),
                                 "lattice_only": sum(1 for d in by.values() if d.get("lattice") and not d.get(o)),
                                 "other_only": sum(1 for d in by.values() if d.get(o) and not d.get("lattice"))} for o in solvers if o != "lattice"}
    RESULTS.mkdir(exist_ok=True)
    (RESULTS / "summary.json").write_text(json.dumps(summary, indent=1))
    print(json.dumps(summary, indent=1))
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    DOCS.mkdir(exist_ok=True)
    n = 2 if satlib_rows else 1
    fig, axes = plt.subplots(1, n, figsize=(6.2 * n, 4.4), squeeze=False)
    cactus(axes[0, 0], main_rows, solvers, f"SAT Competition 2023 sample ({len(by)} instances, 300 s)")
    if satlib_rows:
        cactus(axes[0, 1], satlib_rows, solvers, "SATLIB uf250 + uuf250 (200 instances)")
    fig.tight_layout()
    fig.savefig(DOCS / "cactus.png", dpi=130)
    plt.close(fig)
    others = [s for s in solvers if s != "lattice"]
    fig, axes = plt.subplots(1, len(others), figsize=(5.4 * len(others), 4.8), squeeze=False)
    for k, o in enumerate(others):
        scatter(axes[0, k], main_rows, o, main_rows[0]["timeout"])
    fig.tight_layout()
    fig.savefig(DOCS / "scatter.png", dpi=130)
    plt.close(fig)


if __name__ == "__main__":
    main()
