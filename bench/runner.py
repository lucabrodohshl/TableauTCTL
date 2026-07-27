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


def _run_capture(cmd: List[str], timeout_s: int, mem_limit_mb: int = 0):
    """Run `cmd` under a wall-clock and a memory budget.

    Returns ``(stdout, stderr, peak_rss_kb, outcome)`` where ``outcome`` is
    ``""``, ``"TIMEOUT"`` or ``"MEMOUT"``.

    macOS refuses every ``setrlimit`` that would cap memory --- ``RLIMIT_AS``,
    ``RLIMIT_DATA`` and ``RLIMIT_RSS`` all fail, and ``ulimit -v`` is rejected by
    the kernel --- so the budget is enforced from the parent instead: a watchdog
    samples the child's resident size and kills it on breach.  That is portable
    and, unlike a soft limit the allocator may route around, actually binding.

    Peak resident size comes from ``os.wait4``, which reports rusage for this one
    process; ``RUSAGE_CHILDREN`` is a running maximum over every child and could
    not give a per-instance figure.  Output goes to temporary files rather than
    pipes because ``Popen.communicate()`` reaps the child, leaving wait4 nothing
    to report on.
    """
    import psutil

    outcome = {"reason": ""}
    with tempfile.TemporaryFile() as fo, tempfile.TemporaryFile() as fe:
        proc = subprocess.Popen(cmd, stdout=fo, stderr=fe)

        def on_timeout():
            outcome["reason"] = outcome["reason"] or "TIMEOUT"
            proc.kill()

        timer = threading.Timer(timeout_s, on_timeout)
        timer.start()

        watchdog_stop = threading.Event()

        def watch():
            limit = mem_limit_mb * 1024 * 1024
            try:
                ps = psutil.Process(proc.pid)
            except psutil.Error:
                return
            while not watchdog_stop.wait(0.1):
                try:
                    if ps.memory_info().rss > limit:
                        outcome["reason"] = outcome["reason"] or "MEMOUT"
                        proc.kill()
                        return
                except psutil.Error:
                    return                      # the child is gone

        watcher = None
        if mem_limit_mb > 0:
            watcher = threading.Thread(target=watch, daemon=True)
            watcher.start()

        try:
            _, status, ru = os.wait4(proc.pid, 0)
        finally:
            timer.cancel()
            watchdog_stop.set()
            if watcher is not None:
                watcher.join(timeout=1.0)

        proc.returncode = os.waitstatus_to_exitcode(status) \
            if os.WIFEXITED(status) else -os.WTERMSIG(status)
        fo.seek(0); out = fo.read().decode("utf-8", "replace")
        fe.seek(0); err = fe.read().decode("utf-8", "replace")

    # macOS reports ru_maxrss in bytes, Linux in kilobytes.
    rss_kb = ru.ru_maxrss // 1024 if sys.platform == "darwin" else ru.ru_maxrss
    return out, err, (rss_kb or None), outcome["reason"]


def run_one(solver: Path, inst: Instance, timeout_s: int,
            repeats: int = 1, mem_limit_mb: int = 0) -> dict:
    """Run one instance, returning a record ready for JSONL."""
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as fh:
        fh.write(inst.formula + "\n")
        path = fh.name
    try:
        times: List[float] = []
        verdict, nodes, zones, mem_kb, warned = "ERROR", None, None, None, False
        for _ in range(max(1, repeats)):
            t0 = time.perf_counter()
            out, err, rss_kb, stopped = _run_capture(
                [str(solver), "--stats", path], timeout_s, mem_limit_mb)
            elapsed = time.perf_counter() - t0
            if stopped:
                verdict = stopped                # TIMEOUT or MEMOUT
                if rss_kb:
                    mem_kb = max(mem_kb or 0, rss_kb)
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
            progress: bool = True, mem_limit_mb: int = 0) -> int:
    instances = list(instances)
    out.parent.mkdir(parents=True, exist_ok=True)
    n = 0
    with out.open("w") as fh:
        for i, inst in enumerate(instances, 1):
            rec = run_one(solver, inst, timeout_s, repeats, mem_limit_mb)
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
