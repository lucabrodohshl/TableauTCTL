#!/usr/bin/env python3
"""Verify benchmark.tex claims against CSV data."""
import csv, os, sys

BASE = os.path.join(os.path.dirname(__file__), "..",
                    "benchmark_result_20260301_172217")

def read_csv(name):
    rows = []
    with open(os.path.join(BASE, name)) as f:
        for row in csv.DictReader(f):
            rows.append(row)
    return rows

# === I3 alternation formula structure ===
print("=== I3 alternation formulas (n=1..5) ===")
for row in read_csv("curves_alternation.csv"):
    if row["variant"] == "I3_alternating" and int(row["param_value"]) <= 5:
        print(f"  n={row['param_value']}: {row['formula']}")

# === B2 special case M=1 ===
print("\n=== B2 at M=1 ===")
for row in read_csv("curves_bounds_M.csv"):
    if row["variant"] == "B2_deadline_unsat" and int(row["param_value"]) == 1:
        print(f"  M=1: {row['formula']}  verdict={row['verdict']}")

# === B4 at M=1,2 ===
print("\n=== B4 at small M ===")
for row in read_csv("curves_bounds_M.csv"):
    if row["variant"] == "B4_chain_windows" and int(row["param_value"]) <= 4:
        print(f"  M={row['param_value']}: {row['formula'][:90]}  nodes={row['nodes_generated']}")

# === B node invariance ===
print("\n=== B variant node counts across M ===")
from collections import defaultdict
b_nodes = defaultdict(list)
for row in read_csv("curves_bounds_M.csv"):
    b_nodes[row["variant"]].append((int(row["param_value"]), int(row["nodes_generated"]), int(row["distinct_zones"])))
for var in sorted(b_nodes):
    nodes_set = set(n for _, n, _ in b_nodes[var])
    zones_set = set(z for _, _, z in b_nodes[var])
    print(f"  {var}: nodes={sorted(nodes_set)}, zones={sorted(zones_set)}")

# === H scaling ===
print("\n=== H scaling (nodes vs n) ===")
for row in read_csv("curves_chain.csv"):
    if int(row["param_value"]) in [1,2,4,7,10,14]:
        print(f"  {row['variant']} n={row['param_value']}: nodes={row['nodes_generated']} zones={row['distinct_zones']} t={row['elapsed_s']}")

# === G scaling ===
print("\n=== G1/G2/G3 nodes at k=1..10 ===")
g = defaultdict(list)
for row in read_csv("curves_clocks.csv"):
    g[row["variant"]].append((int(row["param_value"]), int(row["nodes_generated"]), int(row["distinct_zones"])))
for var in sorted(g):
    print(f"  {var}:")
    for k, n, z in sorted(g[var]):
        print(f"    k={k}: nodes={n}, zones={z}")

# === F scaling ===
print("\n=== F node counts ===")
f_data = defaultdict(list)
for row in read_csv("curves_zeno.csv"):
    f_data[row["variant"]].append((int(row["param_value"]), int(row["nodes_generated"]), int(row["distinct_zones"]), row["verdict"]))
for var in sorted(f_data):
    nodes = [n for _, n, _, _ in f_data[var]]
    verdicts = set(v for _, _, _, v in f_data[var])
    print(f"  {var}: verdicts={verdicts}, node range={min(nodes)}-{max(nodes)}")

# === I all variants at max n ===
print("\n=== I variants at n=14 ===")
for row in read_csv("curves_alternation.csv"):
    if int(row["param_value"]) == 14:
        print(f"  {row['variant']}: nodes={row['nodes_generated']} zones={row['distinct_zones']} t={row['elapsed_s']} verdict={row['verdict']}")

# === C max values ===
print("\n=== C max stats ===")
c_data = defaultdict(list)
for row in read_csv("curves_obligations.csv"):
    c_data[row["variant"]].append((int(row["param_value"]), float(row["elapsed_s"]), int(row["nodes_generated"])))
for var in sorted(c_data):
    max_t = max(t for _, t, _ in c_data[var])
    max_n = max(n for _, _, n in c_data[var])
    max_k = max(k for k, _, _ in c_data[var])
    print(f"  {var}: max_k={max_k}, max_t={max_t:.3f}s, max_nodes={max_n}")
