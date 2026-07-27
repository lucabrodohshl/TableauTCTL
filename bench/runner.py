"""Execute benchmark instances and record one JSON record per run.

The runner owns every interaction with the solver: building its command line,
enforcing the timeout, parsing its output, and repeating a measurement.  It
never interprets a result -- that is :mod:`analyze`'s job -- so a run can be
re-analysed without re-running it.
"""

from __future__ import annotations

import json
import os
import re
import statistics
import subprocess
import sys
import tempfile
import threading
import time
from dataclasses import asdict
from pathlib import Path
from typing import Iterable, List, Optional

from families import Instance

VERDICT_RE = re.compile(r"^\s*\d+:\s*(SATISFIABLE|UNSATISFIABLE|TIMEOUT)", re.M)
STATS_RE = re.compile(r"nodes=(\d+).*?distinct_zones=(\d+).*?peak_mem_kb=(\d+)", re.S)
# The solver warns on stderr when an input leaves the fragment where
# completeness is guaranteed; RQ3 reports how well that warning predicts a miss.
WARN_RE = re.compile(r"punctual interval .* not guaranteed COMPLETE", re.S)


def _run_capture(cmd: List[str], timeout_s: int):
    """Run `cmd`, returning (stdout, stderr, peak_rss_kb).

    The engine does not populate its own memory counter, so peak resident size
    is taken from the operating system.  os.wait4 reports rusage for one
    process, which is what makes the figure per-instance; RUSAGE_CHILDREN is a
    running maximum over every child and could not give that.  Output goes to
    temporary files rather than pipes because Popen.communicate() reaps the
    child, leaving wait4 nothing to report on.
    """
    import resource  # noqa: F401  (documents the dependency)

    with tempfile.TemporaryFile() as fo, tempfile.TemporaryFile() as fe:
        proc = subprocess.Popen(cmd, stdout=fo, stderr=fe)
        timer = threading.Timer(timeout_s, proc.kill)
        timer.start()
        try:
            _, status, ru = os.wait4(proc.pid, 0)
        finally:
            timer.cancel()
        proc.returncode = os.waitstatus_to_exitcode(status) \
            if os.WIFEXITED(status) else -os.WTERMSIG(status)
        fo.seek(0); out = fo.read().decode("utf-8", "replace")
        fe.seek(0); err = fe.read().decode("utf-8", "replace")

    # macOS reports ru_maxrss in bytes, Linux in kilobytes.
    rss_kb = ru.ru_maxrss // 1024 if sys.platform == "darwin" else ru.ru_maxrss
    if proc.returncode < 0:                     # killed by the timer
        raise subprocess.TimeoutExpired(cmd, timeout_s)
    return out, err, (rss_kb or None)


def run_one(solver: Path, inst: Instance, timeout_s: int,
            repeats: int = 1) -> dict:
    """Run one instance, returning a record ready for JSONL."""
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as fh:
        fh.write(inst.formula + "\n")
        path = fh.name
    try:
        times: List[float] = []
        verdict, nodes, zones, mem_kb, warned = "ERROR", None, None, None, False
        for _ in range(max(1, repeats)):
            t0 = time.perf_counter()
            try:
                out, err, rss_kb = _run_capture([str(solver), "--stats", path],
                                                timeout_s)
                elapsed = time.perf_counter() - t0
            except subprocess.TimeoutExpired:
                elapsed = float(timeout_s)
                out, err = "", ""
                verdict = "TIMEOUT"
                times.append(elapsed)
                break
            times.append(elapsed)
            m = VERDICT_RE.search(out)
            verdict = m.group(1) if m else "ERROR"
            warned = warned or bool(WARN_RE.search(err))
            sm = STATS_RE.search(out + err)
            if sm:
                nodes, zones = int(sm.group(1)), int(sm.group(2))
            if rss_kb:
                mem_kb = max(mem_kb or 0, rss_kb)
        rec = {
            **{k: v for k, v in asdict(inst).items()},
            "verdict": verdict,
            "time_s": statistics.median(times),
            "time_min_s": min(times),
            "repeats": len(times),
            "nodes": nodes,
            "distinct_zones": zones,
            "peak_mem_kb": mem_kb,
            "warned_incomplete": warned,
        }
        # A sound procedure never reports SAT for an UNSAT formula, so a
        # disagreement with a by-construction expectation is either an
        # incompleteness instance (expected SAT, got UNSAT) or a soundness bug.
        if inst.expected and verdict in ("SATISFIABLE", "UNSATISFIABLE"):
            got = "SAT" if verdict == "SATISFIABLE" else "UNSAT"
            rec["agrees"] = (got == inst.expected)
            rec["incomplete"] = (inst.expected == "SAT" and got == "UNSAT")
            rec["unsound"] = (inst.expected == "UNSAT" and got == "SAT")
        return rec
    finally:
        os.unlink(path)


def run_all(solver: Path, instances: Iterable[Instance], out: Path,
            timeout_s: int = 300, repeats: int = 1,
            progress: bool = True) -> int:
    instances = list(instances)
    out.parent.mkdir(parents=True, exist_ok=True)
    n = 0
    with out.open("w") as fh:
        for i, inst in enumerate(instances, 1):
            rec = run_one(solver, inst, timeout_s, repeats)
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
            n += 1
            if progress:
                flag = ""
                if rec.get("unsound"):
                    flag = "  <-- UNSOUND"
                elif rec.get("incomplete"):
                    flag = "  <-- incomplete"
                print(f"[{i:4d}/{len(instances)}] {inst.name:34s} "
                      f"{rec['verdict']:14s} {rec['time_s']:7.3f}s{flag}",
                      flush=True)
    return n
