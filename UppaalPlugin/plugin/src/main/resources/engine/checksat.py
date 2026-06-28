#!/usr/bin/env python3
# ============================================================================
# checksat.py — end-to-end "Check Satisfiability" driver
# ============================================================================
#
# Glue the plugin calls: translate each UPPAAL query (uppaal2tctl) and run the
# tctl_sat solver, returning per-query verdicts and, on SAT, a UPPAAL-XML
# witness path.  This is the single entry point a GUI/plugin shells out to.
#
#   checksat.py --model m.xml --queries q.q [--witness-dir DIR] [--json]
#
# Solver location is configurable (local binary by default; a prefix such as
# "docker exec <name>" runs it in a container, used for testing here):
#   --binary  PATH        path to tctl_sat   (default: tctl_sat on PATH)
#   --solver  "PREFIX"    shell-split prefix tokens (default: none)
# ============================================================================

from __future__ import annotations

import argparse
import os
import re
import shlex
import subprocess
import sys
import tempfile
import uuid

import uppaal2tctl as u2t


_VERDICT_RE = re.compile(r"^\s*\d+:\s*(SATISFIABLE|UNSATISFIABLE|TIMEOUT)", re.M)
_TAXML_RE = re.compile(r"TA XML\s*:\s*(\S+)")


def _is_docker(tokens):
    return len(tokens) >= 2 and tokens[0] == "docker" and tokens[1] == "exec"


def _docker_name(tokens):
    # docker exec [-i] NAME ...
    rest = tokens[2:]
    rest = [t for t in rest if not t.startswith("-")]
    return rest[0] if rest else None


def solve(formula, real_vars, solver_tokens, binary, timeout, want_witness):
    """Run tctl_sat on `formula`. Return (verdict, witness_xml_text|None)."""
    rv = ["--real-vars", ",".join(real_vars)] if real_vars else []
    stem = "cs_" + uuid.uuid4().hex[:8]

    if _is_docker(solver_tokens):
        name = _docker_name(solver_tokens)
        cpath = f"/tmp/{stem}.txt"
        subprocess.run(["docker", "exec", "-i", name, "sh", "-c", f"cat > {cpath}"],
                       input=formula, text=True, check=True)
        base = ["docker", "exec", name, binary] + rv + ["--stats"]
        verdict = _verdict(_run(base + [cpath], timeout))
        witness = None
        if want_witness and verdict == "SAT":
            wdir = f"/tmp/{stem}_w"
            out = _run(["docker", "exec", name, "sh", "-c",
                        f"mkdir -p {wdir} && cd {wdir} && " +
                        " ".join([binary] + rv + ["--model", cpath])], timeout)
            witness = _fetch_witness_docker(name, out, wdir)
        return verdict, witness

    # local binary
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
        f.write(formula)
        path = f.name
    try:
        base = list(solver_tokens) + [binary] + rv + ["--stats"]
        verdict = _verdict(_run(base + [path], timeout))
        witness = None
        if want_witness and verdict == "SAT":
            # Run inside a fresh dir (cwd) rather than via --output, which
            # appends a timestamp when the dir already exists; the solver writes
            # line_<n>/<stem>.xml there.
            wdir = tempfile.mkdtemp(prefix=stem + "_")
            out = _run(list(solver_tokens) + [binary] + rv +
                       ["--model", path], timeout, cwd=wdir)
            witness = _fetch_witness_local(out, wdir)
        return verdict, witness
    finally:
        os.unlink(path)


def _run(cmd, timeout, cwd=None):
    try:
        p = subprocess.run(cmd, capture_output=True, text=True,
                           timeout=timeout, cwd=cwd)
        return p.stdout
    except subprocess.TimeoutExpired:
        return "1: TIMEOUT"


def _verdict(stdout):
    m = _VERDICT_RE.search(stdout)
    if not m:
        return "ERROR"
    return {"SATISFIABLE": "SAT", "UNSATISFIABLE": "UNSAT",
            "TIMEOUT": "TIMEOUT"}[m.group(1)]


def _fetch_witness_local(stdout, wdir):
    m = _TAXML_RE.search(stdout)
    cand = m.group(1) if m else None
    if cand and not os.path.isabs(cand):
        cand = os.path.join(wdir, cand)
    if not (cand and os.path.exists(cand)):
        xmls = [os.path.join(r, fn) for r, _, fs in os.walk(wdir)
                for fn in fs if fn.endswith(".xml")]
        cand = xmls[0] if xmls else None
    if cand and os.path.exists(cand):
        with open(cand) as f:
            return f.read()
    return None


def _fetch_witness_docker(name, stdout, wdir):
    # find an .xml under wdir in the container and cat it
    out = _run(["docker", "exec", name, "sh", "-c",
                f"find {wdir} -name '*.xml' | head -1"], 30).strip()
    path = out.splitlines()[0] if out else ""
    if not path:
        return None
    p = subprocess.run(["docker", "exec", name, "cat", path],
                       capture_output=True, text=True)
    return p.stdout or None


def check(model_path, queries, solver, binary, timeout, witness_dir):
    model = u2t.parse_model(model_path) if model_path else None
    solver_tokens = shlex.split(solver) if solver else []
    results = []
    for q in queries:
        tr = u2t.translate(q, model)
        if not tr.ok:
            results.append({"query": q, "verdict": "REJECTED",
                            "reason": tr.reason})
            continue
        verdict, witness = solve(tr.formula, tr.real_vars, solver_tokens,
                                 binary, timeout, want_witness=bool(witness_dir))
        rec = {"query": q, "verdict": verdict, "formula": tr.formula,
               "real_vars": tr.real_vars, "warnings": tr.warnings}
        if witness and witness_dir:
            os.makedirs(witness_dir, exist_ok=True)
            safe = re.sub(r"\W+", "_", q)[:40].strip("_") or "witness"
            wpath = os.path.join(witness_dir, f"{safe}.xml")
            with open(wpath, "w") as f:
                f.write(witness)
            rec["witness"] = wpath
        results.append(rec)
    return results


def _read_queries(qpath):
    out = []
    with open(qpath) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith(("//", "#")):
                out.append(line)
    return out


def main():
    ap = argparse.ArgumentParser(description="Check satisfiability of UPPAAL queries.")
    ap.add_argument("--model")
    ap.add_argument("--query")
    ap.add_argument("--queries")
    ap.add_argument("--binary", default="tctl_sat")
    ap.add_argument("--solver", default="")
    ap.add_argument("--timeout", type=float, default=300.0)
    ap.add_argument("--witness-dir", help="write a UPPAAL .xml witness per SAT query")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--porcelain", action="store_true",
                    help="machine-readable: verdict<TAB>query<TAB>witness<TAB>reason")
    args = ap.parse_args()

    queries = []
    if args.query:
        queries.append(args.query)
    if args.queries:
        queries.extend(_read_queries(args.queries))
    if not queries:
        print("no query given", file=sys.stderr)
        return 2

    results = check(args.model, queries, args.solver, args.binary,
                    args.timeout, args.witness_dir)

    if args.json:
        import json
        print(json.dumps(results, indent=2))
        return 0
    if args.porcelain:
        for r in results:
            print("\t".join([r["verdict"], r["query"],
                             r.get("witness", ""), r.get("reason", "")]))
        return 0
    for r in results:
        line = f"[{r['verdict']:8s}] {r['query']}"
        if r.get("witness"):
            line += f"   witness: {r['witness']}"
        if r["verdict"] == "REJECTED":
            line += f"   ({r['reason']})"
        print(line)
        for w in r.get("warnings", []):
            print(f"             warning: {w}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
