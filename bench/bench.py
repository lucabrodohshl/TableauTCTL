#!/usr/bin/env python3
"""TCTL satisfiability benchmark -- single entry point.

    ./bench/bench.py run       --solver build/tctl_sat
    ./bench/bench.py analyze
    ./bench/bench.py all       --solver build/tctl_sat --timeout 300

Results land in bench/results/results.jsonl; figures and tables are written
where the paper expects them, so a rebuild of the paper picks them up.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import families            # noqa: E402
import runner              # noqa: E402
import analyze as analysis  # noqa: E402

HERE = Path(__file__).resolve().parent
DEFAULT_RESULTS = HERE / "results" / "results.jsonl"
# Generated artefacts land here, not in the paper tree: the paper still carries
# hand-written tables from an earlier study, and silently overwriting them would
# lose work that no longer has a generator.  Copy across deliberately.
OUT = HERE / "out"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("action", choices=["list", "run", "analyze", "all"])
    ap.add_argument("--solver", type=Path, default=Path("build/tctl_sat"))
    ap.add_argument("--results", type=Path, default=DEFAULT_RESULTS)
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--repeats", type=int, default=1)
    ap.add_argument("--rq", default=None, help="restrict to RQ1|RQ2|RQ3")
    ap.add_argument("--figs", type=Path, default=OUT / "figs")
    ap.add_argument("--tables", type=Path, default=OUT / "tables")
    args = ap.parse_args()

    insts = families.all_instances()
    if args.rq:
        insts = [i for i in insts if i.rq == args.rq.upper()]

    if args.action == "list":
        for i in insts:
            print(f"{i.rq}  {i.name:34s} {i.formula[:90]}")
        print(f"\n{len(insts)} instances")
        return 0

    if args.action in ("run", "all"):
        if not args.solver.exists():
            print(f"solver not found: {args.solver}", file=sys.stderr)
            return 2
        print(f"running {len(insts)} instances "
              f"(timeout {args.timeout}s, repeats {args.repeats})\n")
        runner.run_all(args.solver, insts, args.results,
                       timeout_s=args.timeout, repeats=args.repeats)
        print(f"\nwrote {args.results}")

    if args.action in ("analyze", "all"):
        if not args.results.exists():
            print(f"no results at {args.results}; run first", file=sys.stderr)
            return 2
        analysis.analyze(args.results, args.figs, args.tables)
        print(f"\nfigures -> {args.figs}\ntables  -> {args.tables}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
