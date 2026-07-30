#!/usr/bin/env python3
"""Extract a witness for every satisfiable instance and check it structurally.

Runs `--model` over the instances of the structural sweep that came back
SATISFIABLE, and records for each one whether the extractor crashed, whether
`validate()` flagged the automaton, and how big it is.  This is the harness the
--model fix is measured against; it does not model-check the witness, it checks
that one is produced and is well formed.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import families_structural as fam   # noqa: E402

SIZE_RE = re.compile(r"Witness: (\d+) locations, (\d+) transitions, (\d+) clocks")
PROB_RE = re.compile(r"witness problem: (.*)")


def check_one(solver: Path, inst, timeout_s: int, workdir: Path) -> dict:
    d = tempfile.mkdtemp(dir=workdir)
    with open(os.path.join(d, "f.txt"), "w") as fh:
        fh.write(inst.formula + "\n")
    rec = {"name": inst.name, "family": inst.family, "formula": inst.formula}
    try:
        r = subprocess.run([str(solver), "--model", "--output", d,
                            os.path.join(d, "f.txt")],
                           capture_output=True, text=True, timeout=timeout_s,
                           cwd=d)
        rec["exit"] = r.returncode
        rec["crashed"] = r.returncode < 0 or r.returncode > 1
        m = SIZE_RE.search(r.stdout)
        if m:
            rec["locations"] = int(m.group(1))
            rec["transitions"] = int(m.group(2))
            rec["clocks"] = int(m.group(3))
        rec["invalid"] = "[INVALID]" in r.stdout
        rec["problems"] = PROB_RE.findall(r.stdout + r.stderr)
        rec["no_witness"] = "no witness available" in r.stderr
    except subprocess.TimeoutExpired:
        rec["exit"] = None
        rec["crashed"] = False
        rec["timeout"] = True
    finally:
        for f in Path(d).glob("*"):
            try:
                f.unlink()
            except OSError:
                pass
        try:
            os.rmdir(d)
        except OSError:
            pass
    return rec


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--solver", type=Path, default=Path("build/tctl_sat"))
    ap.add_argument("--results", type=Path,
                    default=Path("bench/results/structural.jsonl"))
    ap.add_argument("--out", type=Path,
                    default=Path("bench/results/witness_check.jsonl"))
    ap.add_argument("--timeout", type=int, default=20)
    ap.add_argument("--jobs", type=int, default=8)
    args = ap.parse_args()

    sat = set()
    with args.results.open() as fh:
        for line in fh:
            r = json.loads(line)
            if r["verdict"] == "SATISFIABLE":
                sat.add(r["name"])
    insts = [i for i in fam.all_instances() if i.name in sat]
    print(f"{len(insts)} satisfiable instances to extract", flush=True)

    recs = []
    with tempfile.TemporaryDirectory() as wd, \
         ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futs = [pool.submit(check_one, args.solver.resolve(), i,
                            args.timeout, Path(wd)) for i in insts]
        for n, fut in enumerate(as_completed(futs), 1):
            recs.append(fut.result())
            if n % 500 == 0:
                print(f"  {n}/{len(insts)}", flush=True)

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w") as fh:
        for r in recs:
            fh.write(json.dumps(r) + "\n")

    crashed = [r for r in recs if r.get("crashed")]
    invalid = [r for r in recs if r.get("invalid")]
    missing = [r for r in recs if r.get("no_witness")]
    tmo = [r for r in recs if r.get("timeout")]
    print(f"\nextracted   : {len(recs)}")
    print(f"crashed     : {len(crashed)}")
    print(f"INVALID     : {len(invalid)}")
    print(f"no witness  : {len(missing)}")
    print(f"timeout     : {len(tmo)}")
    for label, rs in (("crash", crashed), ("invalid", invalid)):
        for r in rs[:10]:
            print(f"  {label}: {r['name']:16s} {r.get('problems')} "
                  f"{r['formula'][:60]}")
    sizes = [r["locations"] for r in recs if "locations" in r]
    if sizes:
        sizes.sort()
        print(f"\nlocations   : median {sizes[len(sizes)//2]}, "
              f"p95 {sizes[int(0.95*(len(sizes)-1))]}, max {sizes[-1]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
