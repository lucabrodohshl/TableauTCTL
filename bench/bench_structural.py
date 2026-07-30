#!/usr/bin/env python3
"""Run the 10-family / 5000-formula structural sweep.

    ./bench/bench_structural.py --solver build/tctl_sat --jobs 8

Reuses runner.run_one for the per-instance protocol (timeout, memory budget,
verdict/stats parsing) and parallelises across instances, which run_all does
not.  Results land in bench/results/structural.jsonl; a per-family summary is
printed at the end and written next to the results.
"""

from __future__ import annotations

import argparse
import json
import statistics
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import families_structural as fam   # noqa: E402
import runner                        # noqa: E402

HERE = Path(__file__).resolve().parent


def summarise(records: list[dict]) -> str:
    lines = ["family      n    SAT  UNSAT  T/O  ERR  mismat"
             "  med_ms    p95_ms    max_ms"]
    order = [f.__name__.removeprefix("f_") for f in fam.FAMILIES]
    for name in order:
        rs = [r for r in records if r["family"] == name]
        if not rs:
            continue
        sat = sum(r["verdict"] == "SATISFIABLE" for r in rs)
        uns = sum(r["verdict"] == "UNSATISFIABLE" for r in rs)
        tmo = sum(r["verdict"] in ("TIMEOUT", "MEMOUT") for r in rs)
        err = sum(r["verdict"] == "ERROR" for r in rs)
        bad = sum(1 for r in rs if r.get("agrees") is False)
        ts = sorted(r["time_s"] * 1000 for r in rs)
        med = statistics.median(ts)
        p95 = ts[int(0.95 * (len(ts) - 1))]
        lines.append(f"{name:10s} {len(rs):4d}  {sat:5d}  {uns:5d} {tmo:4d} "
                     f"{err:4d}  {bad:6d} {med:8.1f} {p95:9.1f} {ts[-1]:9.1f}")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--solver", type=Path, default=Path("build/tctl_sat"))
    ap.add_argument("--results", type=Path,
                    default=HERE / "results" / "structural.jsonl")
    ap.add_argument("--timeout", type=int, default=10)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--mem-limit-mb", type=int, default=2048)
    ap.add_argument("--limit", type=int, default=0,
                    help="run only the first N instances (smoke test)")
    args = ap.parse_args()

    solver = args.solver.resolve()
    if not solver.exists():
        print(f"solver not found: {solver}", file=sys.stderr)
        return 1

    insts = fam.all_instances()
    if args.limit:
        insts = insts[: args.limit]
    print(f"{len(insts)} instances, {args.jobs} jobs, "
          f"timeout {args.timeout}s", flush=True)

    records: list[dict] = []
    args.results.parent.mkdir(parents=True, exist_ok=True)
    done = 0
    with args.results.open("w") as fh, \
         ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futs = {pool.submit(runner.run_one, solver, inst, args.timeout,
                            1, args.mem_limit_mb): inst for inst in insts}
        for fut in as_completed(futs):
            rec = fut.result()
            records.append(rec)
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
            done += 1
            flag = ""
            if rec.get("unsound"):
                flag = "  <-- UNSOUND"
            elif rec.get("incomplete"):
                flag = "  <-- incomplete"
            if flag or rec["verdict"] in ("TIMEOUT", "MEMOUT", "ERROR") \
                    or done % 250 == 0:
                print(f"[{done:4d}/{len(insts)}] {rec['name']:16s} "
                      f"{rec['verdict']:14s} {rec['time_s']:7.3f}s{flag}",
                      flush=True)

    summary = summarise(records)
    print("\n" + summary)
    (args.results.with_suffix(".summary.txt")).write_text(summary + "\n")
    unsound = [r["name"] for r in records if r.get("unsound")]
    incomplete = [r["name"] for r in records if r.get("incomplete")]
    if unsound:
        print(f"\nUNSOUND ({len(unsound)}): {', '.join(unsound[:20])}")
    if incomplete:
        print(f"\nincomplete ({len(incomplete)}): {', '.join(incomplete[:20])}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
