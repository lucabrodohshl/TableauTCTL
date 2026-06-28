#!/usr/bin/env python3
# ============================================================================
# bench_generate.py - Emit the synthetic TCTL benchmark to formula files
# ============================================================================
#
# Writes ONE formula per file (so the runner can attribute a per-instance
# timeout and verdict unambiguously) plus a machine-readable manifest.csv that
# records the designed ground-truth verdict for every instance, and a
# human-readable per-family .txt dump for quick inspection / `tctl_sat fam.txt`.
#
# Layout (under --outdir, default scripts/outputs):
#   formulas/<FAMILY>/<variant>__<param>.tctl     one formula, solver syntax
#   formulas/<FAMILY>.txt                          all formulas of a family
#   manifest.csv                                   instance index + ground truth
#
# Usage:
#   python3 bench_generate.py                      # full benchmark
#   python3 bench_generate.py --quick              # tiny smoke set
#   python3 bench_generate.py --outdir /tmp/bench  # custom location
# ============================================================================

from __future__ import annotations

import argparse
import csv
import importlib
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_OUTDIR = os.path.join(HERE, "outputs")

# In quick mode we shrink every family to a handful of small parameters so the
# whole pipeline can be exercised in seconds.
_QUICK = {
    "depth": [1, 2, 3, 4],
    "M": [2, 4, 8, 16],
    "k": [1, 2, 3, 4],
}


def _params_for(v, quick: bool):
    if not quick:
        return v.params
    return _QUICK.get(v.param_name, v.params[:4])


def main() -> int:
    ap = argparse.ArgumentParser(description="Generate the synthetic TCTL benchmark.")
    ap.add_argument("--outdir", default=DEFAULT_OUTDIR,
                    help="output root (default: scripts/outputs)")
    ap.add_argument("--families-module", default="bench_families",
                    help="python module providing REGISTRY/validate/max_constant "
                         "(default: bench_families; use perf_families for the perf eval)")
    ap.add_argument("--quick", action="store_true",
                    help="emit a tiny smoke set instead of the full benchmark")
    ap.add_argument("--only", default=None,
                    help="comma-separated family codes to emit (e.g. DCN,DCM)")
    args = ap.parse_args()

    fam = importlib.import_module(args.families_module)
    print(f"[generate] families module: {args.families_module} "
          f"({len(fam.REGISTRY)} registry entries)")

    only = set(args.only.split(",")) if args.only else None

    formulas_dir = os.path.join(args.outdir, "formulas")
    os.makedirs(formulas_dir, exist_ok=True)

    manifest_rows = []
    family_dumps: dict[str, list[str]] = {}
    n_files = 0
    n_invalid = 0

    for v in fam.REGISTRY:
        if only and v.family not in only:
            continue
        fam_dir = os.path.join(formulas_dir, v.family)
        os.makedirs(fam_dir, exist_ok=True)
        for p in _params_for(v, args.quick):
            formula = v.gen(p)
            try:
                fam.validate(formula)
            except fam.ValidationError as e:
                n_invalid += 1
                print(f"[generate] INVALID, skipping {v.variant} {v.param_name}={p}: {e}",
                      file=sys.stderr)
                continue

            inst_id = f"{v.variant}__{v.param_name}{p}"
            rel_path = os.path.join("formulas", v.family, f"{inst_id}.txt")
            abs_path = os.path.join(args.outdir, rel_path)
            with open(abs_path, "w") as f:
                f.write(f"# {v.family}/{v.variant}  {v.param_name}={p}  "
                        f"expected={v.expected}\n")
                f.write(formula + "\n")
            n_files += 1

            manifest_rows.append({
                "instance_id": inst_id,
                "family": v.family,
                "family_label": v.family_label,
                "variant": v.variant,
                "variant_label": v.variant_label,
                "param_name": v.param_name,
                "param": p,
                "log_x": int(v.log_x),
                "x_label": v.x_label,
                "expected_verdict": v.expected,
                "max_constant": fam.max_constant(formula),
                "formula_len": len(formula),
                "mechanism": v.mechanism,
                "file": rel_path,
                "formula": formula,
            })
            family_dumps.setdefault(v.family, []).append(
                f"# {v.variant}  {v.param_name}={p}  expected={v.expected}\n{formula}")

    # Per-family human-readable dumps.
    for famcode, lines in family_dumps.items():
        with open(os.path.join(formulas_dir, f"{famcode}.txt"), "w") as f:
            f.write(f"# Family {famcode} - all generated formulas (one per line)\n")
            f.write("\n".join(lines) + "\n")

    # Manifest.
    manifest_path = os.path.join(args.outdir, "manifest.csv")
    cols = ["instance_id", "family", "family_label", "variant", "variant_label",
            "param_name", "param", "log_x", "x_label", "expected_verdict",
            "max_constant", "formula_len", "mechanism", "file", "formula"]
    with open(manifest_path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for r in manifest_rows:
            w.writerow(r)

    print(f"[generate] wrote {n_files} formula files "
          f"({len(manifest_rows)} instances, {n_invalid} invalid) under {formulas_dir}")
    print(f"[generate] manifest: {manifest_path}")
    return 1 if n_invalid else 0


if __name__ == "__main__":
    sys.exit(main())
