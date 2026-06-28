#!/usr/bin/env python3
# ============================================================================
# bench_run.py - Run a configurable TCTL solver over the generated benchmark
# ============================================================================
#
# Reads manifest.csv (produced by bench_generate.py), invokes the solver on
# every instance with a per-instance timeout, parses the verdict + engine
# statistics, validates the verdict against the designed ground truth, and
# writes a tidy results.csv.  Robust to timeouts, crashes and parse errors.
#
# SOLVER COMMAND MODEL
# --------------------
# The full command executed per instance is, in order:
#
#     <solver tokens> [<inner timeout tokens>] <binary> <stats flag> <input>
#
#   --solver   : prefix tokens, shell-split. Empty for a local binary, or e.g.
#                "docker exec <CONTAINER_ID>" for the Docker build.
#   --binary   : path to tctl_sat (default: tctl_sat on PATH; Docker default
#                target is /work/Implementation/tctl_sat).
#   --stats-flag : flag that turns on per-formula statistics (default --stats;
#                  the CLI option is `--stats`, printed as "  Stats: nodes=...").
#   inner timeout: when enabled (default), a coreutils `timeout` wrapper is
#                  inserted AFTER the solver prefix so the kill happens inside
#                  the container.  A Python-level subprocess timeout is always
#                  applied as a backstop so this script never hangs.
#
# PATH TRANSLATION (Docker): formula files are written on the host but the
# solver may see them under a different mount.  --path-from/--path-to rewrite
# the host prefix to the in-container prefix.  Defaults assume the repo's
# Implementation dir is mounted at /work/Implementation (matching the default
# binary path); pass --local to disable translation entirely.
#
# Examples
# --------
#   # Local binary built on this machine:
#   python3 bench_run.py --binary ../tctl_sat --local
#
#   # Docker build (another agent rebuilds the Linux binary in a container):
#   python3 bench_run.py \
#       --solver "docker exec my_container" \
#       --binary /work/Implementation/tctl_sat \
#       --path-to /work/Implementation \
#       --timeout 60
# ============================================================================

from __future__ import annotations

import argparse
import csv
import os
import re
import shlex
import statistics
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
IMPL_DIR = os.path.abspath(os.path.join(HERE, ".."))   # .../Implementation
DEFAULT_OUTDIR = os.path.join(HERE, "outputs")

# CLI prints "<line>: SATISFIABLE | UNSATISFIABLE | TIMEOUT".
_VERDICT_RE = re.compile(r"^\s*\d+:\s*(SATISFIABLE|UNSATISFIABLE|TIMEOUT)\b", re.M)
# Stats line: "  Stats: nodes=.. open=.. closed=.. max_depth=.. memo_hits=.."
#             " loop_checks=.. distinct_zones=.. peak_mem_kb=.. avg_mem_per_node=.."
_STATS_KV_RE = re.compile(r"(\w+)=(\d+)")

_VERDICT_MAP = {
    "SATISFIABLE": "SAT",
    "UNSATISFIABLE": "UNSAT",
    "TIMEOUT": "TIMEOUT",
}

# Engine stat key -> output column name.
_STAT_COLS = {
    "nodes": "nodes",
    "open": "nodes_open",
    "closed": "nodes_closed",
    "max_depth": "max_depth",
    "memo_hits": "memo_hits",
    "loop_checks": "loop_checks",
    "distinct_zones": "distinct_zones",
    "peak_mem_kb": "peak_mem_kb",
    "avg_mem_per_node": "avg_mem_per_node",
}

RESULT_COLS = [
    "instance_id", "family", "family_label", "variant", "variant_label",
    "param_name", "param", "log_x", "x_label", "mechanism",
    "expected_verdict", "verdict", "verdict_match",
    "time_s", "time_min", "time_max", "time_iqr", "n_reps", "stats_consistent",
    "timeout_s", "max_constant", "formula_len",
    "nodes", "nodes_open", "nodes_closed", "max_depth", "memo_hits",
    "loop_checks", "distinct_zones", "peak_mem_kb", "avg_mem_per_node",
    "returncode", "solver_cmd", "formula",
]

# Search-space metrics that MUST be identical across repetitions (the tableau is
# a deterministic single-threaded DFS over a memoised graph -> these are exact
# functions of the formula).  We assert equality as a sanity check.
_DET_KEYS = ("nodes", "nodes_open", "nodes_closed", "max_depth",
             "memo_hits", "loop_checks", "distinct_zones", "peak_mem_kb")


def run_once(cmd, timeout, grace):
    """Run the solver command once. Return (elapsed, verdict, stats, rc)."""
    t0 = time.perf_counter()
    verdict = None
    stats = {}
    rc = None
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              timeout=timeout + grace)
        rc = proc.returncode
        verdict, stats = parse_solver_output(proc.stdout)
        elapsed = time.perf_counter() - t0
        if verdict is None:
            # coreutils timeout exits 124 (or 137 on SIGKILL).
            verdict = "TIMEOUT" if rc in (124, 137) else "ERROR"
    except subprocess.TimeoutExpired:
        elapsed = time.perf_counter() - t0
        verdict = "TIMEOUT"
        rc = -1
    return elapsed, verdict, stats, rc


def parse_solver_output(stdout: str):
    """Return (verdict, stats_dict).  verdict in SAT/UNSAT/TIMEOUT or None."""
    verdict = None
    m = _VERDICT_RE.search(stdout)
    if m:
        verdict = _VERDICT_MAP.get(m.group(1))

    stats = {}
    for line in stdout.splitlines():
        if "Stats:" in line:
            after = line.split("Stats:", 1)[1]
            for k, val in _STATS_KV_RE.findall(after):
                if k in _STAT_COLS:
                    stats[_STAT_COLS[k]] = int(val)
            break
    return verdict, stats


def translate_path(host_path: str, path_from: str, path_to: str) -> str:
    """Rewrite a host path prefix to the in-container prefix (Docker)."""
    if not path_from or not path_to:
        return host_path
    hp = os.path.abspath(host_path)
    pf = os.path.abspath(path_from)
    if hp.startswith(pf):
        rel = os.path.relpath(hp, pf)
        return path_to.rstrip("/") + "/" + rel.replace(os.sep, "/")
    return host_path


def build_command(solver_tokens, binary, stats_flag, timeout_tokens, input_path):
    cmd = list(solver_tokens)
    cmd += list(timeout_tokens)
    cmd.append(binary)
    if stats_flag:
        cmd.append(stats_flag)
    cmd.append(input_path)
    return cmd


def main() -> int:
    ap = argparse.ArgumentParser(description="Run the TCTL solver over the benchmark.")
    ap.add_argument("--outdir", default=DEFAULT_OUTDIR,
                    help="benchmark root containing manifest.csv (default scripts/outputs)")
    ap.add_argument("--manifest", default=None,
                    help="manifest path (default <outdir>/manifest.csv)")
    ap.add_argument("--results", default=None,
                    help="results CSV path (default <outdir>/results/results.csv)")
    ap.add_argument("--solver", default="",
                    help='solver prefix, shell-split, e.g. "docker exec <CID>" (default: none)')
    ap.add_argument("--binary", default="tctl_sat",
                    help="path to tctl_sat (default: tctl_sat on PATH)")
    ap.add_argument("--stats-flag", default="--stats",
                    help="solver flag enabling per-formula stats (default --stats)")
    ap.add_argument("--timeout", type=float, default=60.0,
                    help="per-instance timeout in seconds (default 60)")
    ap.add_argument("--reps", type=int, default=1,
                    help="timed repetitions per instance; report MEDIAN time_s "
                         "(also min/max/IQR). Search-space metrics taken from the "
                         "first run and asserted identical across reps. (default 1)")
    ap.add_argument("--warmup", type=int, default=1,
                    help="discarded warm-up runs before timing (default 1). A "
                         "timeout in ANY run short-circuits (no further reps).")
    ap.add_argument("--fast-threshold", dest="fast_threshold", type=float, default=5.0,
                    help="adaptive repetitions: an instance whose first (warm-up) "
                         "run exceeds this many seconds is timed ONCE (wall-clock "
                         "noise is negligible relative to its runtime); faster "
                         "instances get the full --reps median. Set 0 to disable "
                         "(always do --reps). Default 5.0.")
    ap.add_argument("--grace", type=float, default=10.0,
                    help="extra seconds before the Python-level hard kill (default 10)")
    ap.add_argument("--inner-timeout", dest="inner_timeout", action="store_true", default=True,
                    help="wrap the solver with coreutils `timeout` (default: on)")
    ap.add_argument("--no-inner-timeout", dest="inner_timeout", action="store_false",
                    help="disable the in-container `timeout` wrapper")
    ap.add_argument("--timeout-bin", default="timeout",
                    help="name/path of the coreutils timeout binary (default: timeout)")
    ap.add_argument("--local", action="store_true",
                    help="disable host->container path translation (local runs)")
    ap.add_argument("--path-from", default=IMPL_DIR,
                    help="host path prefix to rewrite (default: the Implementation dir)")
    ap.add_argument("--path-to", default="/work/Implementation",
                    help="container path prefix (default: /work/Implementation)")
    ap.add_argument("--only", default=None,
                    help="comma-separated family codes to run (e.g. DCN,ZEN)")
    ap.add_argument("--limit", type=int, default=0,
                    help="run at most N instances (0 = all; for smoke tests)")
    ap.add_argument("--dry-run", action="store_true",
                    help="print the commands that would run, then exit")
    args = ap.parse_args()

    manifest_path = args.manifest or os.path.join(args.outdir, "manifest.csv")
    if not os.path.exists(manifest_path):
        print(f"[run] manifest not found: {manifest_path}\n"
              f"      run bench_generate.py first.", file=sys.stderr)
        return 2

    results_path = args.results or os.path.join(args.outdir, "results", "results.csv")
    os.makedirs(os.path.dirname(results_path), exist_ok=True)

    with open(manifest_path, newline="") as f:
        rows = list(csv.DictReader(f))
    only = set(args.only.split(",")) if args.only else None
    if only:
        rows = [r for r in rows if r["family"] in only]
    if args.limit > 0:
        rows = rows[: args.limit]

    solver_tokens = shlex.split(args.solver)
    inner_timeout_tokens = []
    if args.inner_timeout:
        # `timeout -k 5 <T>` kills, then SIGKILLs 5s later if still alive.
        inner_timeout_tokens = [args.timeout_bin, "-k", "5", str(int(args.timeout))]

    print(f"[run] {len(rows)} instances | solver='{args.solver or '(local)'}' "
          f"binary='{args.binary}' timeout={args.timeout}s "
          f"inner_timeout={'on' if args.inner_timeout else 'off'}")

    warmup = max(0, args.warmup)
    reps = max(1, args.reps)
    print(f"[run] {len(rows)} instances | reps={reps} (+{warmup} warmup) | "
          f"timeout={args.timeout}s | adaptive: instances >{args.fast_threshold}s timed once | "
          f"median wall-clock, deterministic stats from run 1")

    results = []
    n_to = n_err = n_mismatch = n_det = 0

    for i, r in enumerate(rows, 1):
        host_input = os.path.join(args.outdir, r["file"])
        solver_input = host_input if args.local else translate_path(
            host_input, args.path_from, args.path_to)
        cmd = build_command(solver_tokens, args.binary, args.stats_flag,
                            inner_timeout_tokens, solver_input)

        if args.dry_run:
            print(" ".join(shlex.quote(c) for c in cmd))
            continue

        times = []            # timed (non-warmup) wall-clocks of decided runs
        canon_stats = {}      # deterministic metrics from the FIRST decided run
        verdict = None
        rc = None
        elapsed = 0.0
        stats_consistent = "yes"
        try:
            # First run: a probe that doubles as the warm-up for fast instances.
            elapsed, verdict, stats, rc = run_once(cmd, args.timeout, args.grace)
            if verdict not in ("TIMEOUT", "ERROR"):
                canon_stats = stats
                if args.fast_threshold > 0 and elapsed > args.fast_threshold:
                    # Slow instance: ONE timed run suffices -- wall-clock noise is
                    # negligible relative to the runtime, and the deterministic
                    # search metrics (nodes/zones, on which we rely) are exact.
                    # Avoids (warmup+reps)*timeout on near-wall instances.
                    times.append(elapsed)
                else:
                    # Fast instance: that probe was the warm-up; take `reps` timed
                    # runs and report their median.
                    for _ in range(reps):
                        elapsed, verdict, stats, rc = run_once(
                            cmd, args.timeout, args.grace)
                        if verdict in ("TIMEOUT", "ERROR"):
                            break          # short-circuit (never wastes R*timeout)
                        if any(stats.get(k) != canon_stats.get(k) for k in _DET_KEYS):
                            stats_consistent = "no"
                        times.append(elapsed)
        except FileNotFoundError as e:
            print(f"[run] cannot launch solver: {e}", file=sys.stderr)
            return 3

        # Aggregate wall-clock over the timed repetitions.
        if times:
            med = statistics.median(times)
            tmin, tmax = min(times), max(times)
            if len(times) >= 2:
                q1, _, q3 = statistics.quantiles(times, n=4)
                iqr = q3 - q1
            else:
                iqr = 0.0
            n_done = len(times)
        else:
            # Timeout/error before any timed rep completed.
            med = tmin = tmax = elapsed
            iqr = 0.0
            n_done = 0

        if stats_consistent == "no":
            n_det += 1
            print(f"[run] WARNING: non-deterministic search metrics across reps "
                  f"for {r['instance_id']}", file=sys.stderr)

        expected = r["expected_verdict"]
        if verdict in ("SAT", "UNSAT"):
            match = "yes" if verdict == expected else "no"
            if match == "no":
                n_mismatch += 1
        elif verdict == "TIMEOUT":
            match = "timeout"
            n_to += 1
        else:
            match = "error"
            n_err += 1

        out = {c: "" for c in RESULT_COLS}
        out.update({
            "instance_id": r["instance_id"], "family": r["family"],
            "family_label": r["family_label"], "variant": r["variant"],
            "variant_label": r["variant_label"], "param_name": r["param_name"],
            "param": r["param"], "log_x": r["log_x"], "x_label": r["x_label"],
            "mechanism": r["mechanism"], "expected_verdict": expected,
            "verdict": verdict, "verdict_match": match,
            "time_s": f"{med:.6f}", "time_min": f"{tmin:.6f}",
            "time_max": f"{tmax:.6f}", "time_iqr": f"{iqr:.6f}",
            "n_reps": n_done, "stats_consistent": stats_consistent,
            "timeout_s": args.timeout,
            "max_constant": r["max_constant"], "formula_len": r["formula_len"],
            "returncode": rc, "solver_cmd": args.solver or "(local)",
            "formula": r["formula"],
        })
        for col in _STAT_COLS.values():
            if col in canon_stats:
                out[col] = canon_stats[col]
        results.append(out)

        flag = "" if match in ("yes",) else f"  <-- {match.upper()}"
        print(f"  [{i}/{len(rows)}] {r['variant']} {r['param_name']}={r['param']}: "
              f"{verdict} (median {med:.3f}s, n={n_done}){flag}")

    if args.dry_run:
        return 0

    with open(results_path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=RESULT_COLS)
        w.writeheader()
        for row in results:
            w.writerow(row)

    print(f"\n[run] wrote {len(results)} rows -> {results_path}")
    print(f"[run] timeouts={n_to} errors={n_err} verdict_mismatches={n_mismatch} "
          f"det_metric_mismatches={n_det}")
    if n_mismatch:
        print("[run] WARNING: solver disagreed with the designed ground truth on "
              f"{n_mismatch} instance(s); inspect verdict_match=='no' rows.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
