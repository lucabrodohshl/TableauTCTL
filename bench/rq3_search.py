#!/usr/bin/env python3
"""Search for incompleteness instances.

Generate random TCTL shapes, keep only those some witness structure provably
satisfies (see :mod:`oracle`), and ask the solver.  Because the procedure is
sound, an UNSATISFIABLE verdict on such a formula can only be incompleteness.
"""

from __future__ import annotations

import argparse
import json
import random
import subprocess
import sys
import tempfile
import os
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import shapes            # noqa: E402
from oracle import Witness   # noqa: E402


def ask(solver: Path, formula: str, timeout: int = 20):
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as fh:
        fh.write(formula + "\n")
        path = fh.name
    try:
        pr = subprocess.run([str(solver), path], capture_output=True,
                            text=True, timeout=timeout)
        for line in pr.stdout.splitlines():
            if ":" in line:
                v = line.split(":", 1)[1].strip()
                if v in ("SATISFIABLE", "UNSATISFIABLE"):
                    return v, ("not guaranteed COMPLETE" in pr.stderr)
        return "ERROR", False
    except subprocess.TimeoutExpired:
        return "TIMEOUT", False
    finally:
        os.unlink(path)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--solver", type=Path, default=Path("build/tctl_sat"))
    ap.add_argument("--samples", type=int, default=4000)
    ap.add_argument("--max-depth", type=int, default=4)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--timeout", type=int, default=20)
    ap.add_argument("--out", type=Path, default=Path("bench/results/rq3_search.jsonl"))
    ap.add_argument("--hard", action="store_true",
                    help="keep only formulas needing a non-trivial model: not "
                         "satisfied by the all-true structure, at least one "
                         "punctual window, modal depth >= 2")
    ap.add_argument("--min-punctual", type=int, default=0)
    ap.add_argument("--min-depth", type=int, default=0)
    ap.add_argument("--branching", action="store_true",
                    help="use two-location witnesses, where E and A differ; "
                         "restricts shapes to EF/AG (see oracle.BranchWitness)")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    modals = None
    if args.branching:
        ws = shapes.branch_witnesses()
        trivial = None
        modals = ["EF", "AG"]
    else:
        ws = shapes.witnesses()
        trivial = next(w for w in ws if w.label == "all-true")
        if args.hard:
            ws = [w for w in ws if w.label != "all-true"]
    args.out.parent.mkdir(parents=True, exist_ok=True)

    tested = 0
    seen = set()
    stats = Counter()
    misses = []

    with args.out.open("w") as fh:
        for _ in range(args.samples):
            depth = rng.randint(1, args.max_depth)
            p_punct = rng.choice([0.0, 0.3, 0.6, 1.0])
            node = shapes.gen(rng, depth, p_punct, modals=modals)
            text = shapes.render(node)
            if text in seen:
                continue
            if args.hard:
                # A formula the all-true structure satisfies has a model that
                # discharges every obligation the instant it is raised, so the
                # punctual machinery is never exercised.  Those say nothing
                # about completeness and are filtered out.
                if trivial is not None and trivial.holds_at_zero(node):
                    stats["trivially-sat"] += 1
                    continue
                if shapes.punctual_count(node) < max(1, args.min_punctual):
                    stats["not-punctual"] += 1
                    continue
                if shapes.modal_depth(node) < max(2, args.min_depth):
                    stats["too-shallow"] += 1
                    continue
            # keep only formulas a witness provably satisfies
            wit = next((w for w in ws if w.holds_at_zero(node)), None)
            if wit is None:
                stats["no-witness"] += 1
                continue
            seen.add(text)
            verdict, warned = ask(args.solver, text, args.timeout)
            tested += 1
            npunct = shapes.punctual_count(node)
            rec = {
                "formula": text, "witness": wit.label, "verdict": verdict,
                "depth": shapes.modal_depth(node), "punctual": npunct,
                "size": shapes.size(node), "warned": warned,
            }
            fh.write(json.dumps(rec) + "\n")
            stats[verdict] += 1
            if verdict == "UNSATISFIABLE":
                misses.append(rec)
                print(f"  MISS (witness={wit.label}, depth={rec['depth']}, "
                      f"punct={npunct}): {text[:96]}", flush=True)

    print(f"\ntested {tested} satisfiable-by-construction formulas")
    for k, v in sorted(stats.items()):
        print(f"  {k:16s} {v}")
    if misses:
        print(f"\nINCOMPLETENESS: {len(misses)} instances "
              f"({100*len(misses)/max(tested,1):.2f}%)")
        pc = Counter(m["punctual"] > 0 for m in misses)
        print(f"  with a punctual window: {pc[True]}   without: {pc[False]}")
        print(f"  by depth: {dict(Counter(m['depth'] for m in misses))}")
    else:
        print("\nno incompleteness instance found")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
