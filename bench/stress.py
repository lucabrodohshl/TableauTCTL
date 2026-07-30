#!/usr/bin/env python3
"""Run the adversarial suite under v1 and v2 and report where v2 fails.

Failure means any of: the two versions disagree; a verdict contradicts a
by-construction expectation; the solver crashes; v2 times out where v1 did not;
or v2 is materially slower than v1. Speed-ups are reported too, but this script
exists for the four failure modes.

    ./bench/stress.py --solver build/tctl_sat --jobs 8 --timeout 30
"""

from __future__ import annotations

import argparse
import json
import os
import re
import statistics
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import families_stress as fam   # noqa: E402

NODES_RE = re.compile(r"nodes=(\d+)")
# The engine's own environment overrides must not leak in: the point is to
# measure what --version selects.
CLEAN_ENV = {k: v for k, v in os.environ.items() if not k.startswith("TCTL_")}


def run_one(solver: Path, inst, timeout: int, v1_timeout: int = 0) -> dict:
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as fh:
        fh.write(inst.formula + "\n")
        path = fh.name
    rec = {"name": inst.name, "family": inst.family, "params": inst.params,
           "expected": inst.expected, "formula": inst.formula}
    try:
        for ver in ("v1", "v2"):
            # v1 gets a shorter budget on purpose.  The suite exists to measure
            # v2, and v1 exhausting its budget is a result, not something to
            # wait out: the first run spent most of its wall clock on v1
            # timeouts and never reached the last family.
            budget = v1_timeout if (ver == "v1" and v1_timeout) else timeout
            t0 = time.perf_counter()
            try:
                r = subprocess.run(
                    [str(solver), "--version", ver, "--stats", path],
                    capture_output=True, text=True, timeout=budget,
                    env=CLEAN_ENV)
                el = time.perf_counter() - t0
                if r.returncode < 0 or r.returncode > 1:
                    rec[ver] = "CRASH"
                elif "UNSATIS" in r.stdout:
                    rec[ver] = "UNSAT"
                elif "SATIS" in r.stdout:
                    rec[ver] = "SAT"
                else:
                    rec[ver] = "ERROR"
                m = NODES_RE.search(r.stdout)
                rec[ver + "_nodes"] = int(m.group(1)) if m else None
                rec[ver + "_rc"] = r.returncode
            except subprocess.TimeoutExpired:
                el = float(budget)
                rec[ver] = "TIMEOUT"
                rec[ver + "_nodes"] = None
            rec[ver + "_t"] = el
    finally:
        os.unlink(path)

    rec["v2_only"] = rec["v1"] == "TIMEOUT" and rec["v2"] in ("SAT", "UNSAT")
    rec["disagree"] = (rec["v1"] != rec["v2"]) and not rec["v2_only"]
    rec["wrong"] = bool(inst.expected) and rec["v2"] in ("SAT", "UNSAT") \
        and rec["v2"] != inst.expected
    rec["crash"] = "CRASH" in (rec["v1"], rec["v2"]) or "ERROR" in (rec["v1"], rec["v2"])
    rec["new_timeout"] = rec["v2"] == "TIMEOUT" and rec["v1"] != "TIMEOUT"
    # Slower only counts above the noise floor: these runs are milliseconds and
    # dominated by process start-up.
    rec["slower"] = (rec["v2_t"] > 3 * rec["v1_t"] and rec["v2_t"] > 0.25)
    return rec


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--solver", type=Path, default=Path("build/tctl_sat"))
    ap.add_argument("--out", type=Path,
                    default=Path("bench/results/stress.jsonl"))
    ap.add_argument("--timeout", type=int, default=30)
    ap.add_argument("--v1-timeout", type=int, default=3,
                    help="separate, shorter budget for v1 (0 = same as v2)")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--limit", type=int, default=0)
    args = ap.parse_args()

    insts = fam.all_instances()
    if args.limit:
        insts = insts[: args.limit]
    print(f"{len(insts)} instances x 2 versions, timeout {args.timeout}s",
          flush=True)

    recs = []
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w") as fh, ThreadPoolExecutor(args.jobs) as pool:
        futs = [pool.submit(run_one, args.solver.resolve(), i, args.timeout,
                            args.v1_timeout) for i in insts]
        for n, f in enumerate(as_completed(futs), 1):
            rec = f.result()
            recs.append(rec)
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
            tags = [k for k in ("disagree", "wrong", "crash", "new_timeout",
                                "slower") if rec.get(k)]
            if tags:
                print(f"  [{rec['name']}] {'+'.join(tags)}  "
                      f"v1={rec['v1']}/{rec['v1_t']:.2f}s "
                      f"v2={rec['v2']}/{rec['v2_t']:.2f}s", flush=True)
            elif n % 300 == 0:
                print(f"  {n}/{len(insts)}", flush=True)

    # ── report ──────────────────────────────────────────────────────────
    print(f"\n{'family':12s} {'n':>4} {'v1 tmo':>7} {'v2 tmo':>7} "
          f"{'disagree':>9} {'wrong':>6} {'crash':>6} {'slower':>7} "
          f"{'med x':>7} {'max x':>7}")
    order = [f.__name__.removeprefix("f_") for f in fam.FAMILIES]
    tot = {k: 0 for k in ("disagree", "wrong", "crash", "new_timeout", "slower")}
    for name in order:
        rs = [r for r in recs if r["family"] == name]
        if not rs:
            continue
        for k in tot:
            tot[k] += sum(1 for r in rs if r.get(k))
        ratios = [r["v1_t"] / r["v2_t"] for r in rs
                  if r["v2_t"] > 0 and r["v1"] == r["v2"] != "TIMEOUT"]
        med = statistics.median(ratios) if ratios else float("nan")
        mx = max(ratios) if ratios else float("nan")
        print(f"{name:12s} {len(rs):>4} "
              f"{sum(1 for r in rs if r['v1']=='TIMEOUT'):>7} "
              f"{sum(1 for r in rs if r['v2']=='TIMEOUT'):>7} "
              f"{sum(1 for r in rs if r['disagree']):>9} "
              f"{sum(1 for r in rs if r['wrong']):>6} "
              f"{sum(1 for r in rs if r['crash']):>6} "
              f"{sum(1 for r in rs if r['slower']):>7} "
              f"{med:>7.2f} {mx:>7.1f}")

    print("\nFAILURES")
    for k, v in tot.items():
        print(f"  {k:12s} {v}")
    for k in ("wrong", "disagree", "crash", "new_timeout", "slower"):
        bad = [r for r in recs if r.get(k)]
        for r in bad[:8]:
            print(f"  {k}: {r['name']:16s} exp={r['expected']} "
                  f"v1={r['v1']} v2={r['v2']}  {r['formula'][:70]}")
    return 1 if (tot["wrong"] or tot["disagree"] or tot["crash"]) else 0


if __name__ == "__main__":
    sys.exit(main())
