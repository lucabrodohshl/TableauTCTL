#!/usr/bin/env python3
"""Run a command under an RSS watchdog and report its peak resident size.

    memcap.py <limit_kb> <timeout_s> <cmd> [args...]

Darwin implements none of RLIMIT_AS / RLIMIT_DATA / RLIMIT_RSS, so a hard cap is
not available on macOS without a VM.  This samples the child's resident set and
SIGKILLs it once it exceeds <limit_kb>, which bounds memory to within one
sampling interval.

The timeout is enforced here rather than by the caller: killing this wrapper from
outside would orphan the solver it spawned, since SIGKILL cannot be caught.

Exit codes: the child's own code normally, 101 if it was killed for memory,
124 if it ran past the timeout.

The child's ``  Stats: ...`` line is rewritten to carry ``peak_mem_kb=<n>``, so
the surrounding harness records the peak the watchdog observed.  The solver does
not populate that field itself.
"""
import os
import re
import signal
import subprocess
import sys
import time

INTERVAL = 0.15  # seconds between RSS samples


def rss_kb(pid):
    try:
        out = subprocess.run(["ps", "-o", "rss=", "-p", str(pid)],
                             capture_output=True, text=True, timeout=5)
        line = out.stdout.strip()
        return int(line) if line else 0
    except Exception:
        return 0


def main():
    if len(sys.argv) < 4:
        print("usage: memcap.py <limit_kb> <timeout_s> <cmd> [args...]",
              file=sys.stderr)
        return 2
    limit = int(sys.argv[1])
    budget = float(sys.argv[2])
    cmd = sys.argv[3:]

    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, start_new_session=True)
    t0 = time.time()
    peak = 0
    killed = False
    timed_out = False
    while proc.poll() is None:
        cur = rss_kb(proc.pid)
        if cur > peak:
            peak = cur
        if limit and cur > limit:
            killed = True
        elif budget and time.time() - t0 > budget:
            timed_out = True
        if killed or timed_out:
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                try:
                    os.kill(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            break
        time.sleep(INTERVAL)

    out, err = proc.communicate()

    if timed_out:
        sys.stdout.write(out or "")
        sys.stdout.write(f"  TIMEOUT after {budget:.0f}s peak_mem_kb={peak}\n")
        sys.stderr.write(err or "")
        return 124

    if killed:
        sys.stdout.write(out or "")
        sys.stdout.write(f"  MEMOUT: peak_mem_kb={peak} exceeded {limit}\n")
        sys.stderr.write(err or "")
        return 101

    # Fold the observed peak into the solver's own stats line.
    if out and "Stats:" in out:
        out = re.sub(r"(^\s*Stats:.*)$",
                     lambda m: m.group(1) + f" peak_mem_kb={peak}",
                     out, count=1, flags=re.M)
    elif out is not None:
        out = out + f"  Stats: peak_mem_kb={peak}\n"
    sys.stdout.write(out or "")
    sys.stderr.write(err or "")
    return proc.returncode


if __name__ == "__main__":
    sys.exit(main())
