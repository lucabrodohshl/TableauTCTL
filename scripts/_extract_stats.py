#!/usr/bin/env python3
import pandas as pd, numpy as np, os, sys

d = sys.argv[1] if len(sys.argv)>1 else 'benchmark_result_20260301_172217'
csvs = {
    'depth': 'curves_depth.csv',
    'bounds_M': 'curves_bounds_M.csv',
    'obligations': 'curves_obligations.csv',
    'until_release': 'curves_until_release_mixed.csv',
    'zeno': 'curves_zeno.csv',
    'clocks': 'curves_clocks.csv',
    'chain': 'curves_chain.csv',
    'alternation': 'curves_alternation.csv',
}

frames = []
for k, v in csvs.items():
    p = os.path.join(d, v)
    if os.path.exists(p):
        df = pd.read_csv(p)
        df.columns = df.columns.str.strip()
        for c in df.select_dtypes(include=['object','string']).columns:
            df[c] = df[c].str.strip().str.strip('"')
        frames.append(df)

all_df = pd.concat(frames, ignore_index=True)
for c in ['elapsed_s','nodes_generated','distinct_zones','loop_checks','param_value','M','k','peak_memory_kb','avg_memory_kb']:
    if c in all_df.columns:
        all_df[c] = pd.to_numeric(all_df[c], errors='coerce')

print('=== OVERALL ===')
print(f'Total instances: {len(all_df)}')
print(f'Families: {all_df["family"].nunique()}')
print(f'Variants: {all_df["variant"].nunique()}')
sat = all_df[all_df['verdict']=='SAT']
unsat = all_df[all_df['verdict']=='UNSAT']
print(f'SAT: {len(sat)}, UNSAT: {len(unsat)}')
print(f'Overall mean elapsed: {all_df["elapsed_s"].mean():.6f}')
print(f'Overall median elapsed: {all_df["elapsed_s"].median():.6f}')
print(f'Overall max elapsed: {all_df["elapsed_s"].max():.6f}')
print(f'Total nodes: {int(all_df["nodes_generated"].sum())}')
print(f'Total zones: {int(all_df["distinct_zones"].sum())}')
ratio = all_df["distinct_zones"].sum() / max(all_df["nodes_generated"].sum(),1)
print(f'Global z/n ratio: {ratio:.4f}')
print(f'Solved (<30s): {(all_df["elapsed_s"]<30).sum()} / {len(all_df)}')
print()

# Per-family summary
print('=== PER FAMILY ===')
for fam in sorted(all_df['family'].unique()):
    sub = all_df[all_df['family']==fam]
    s = sub[sub['verdict']=='SAT']
    u = sub[sub['verdict']=='UNSAT']
    print(f'{fam}: n={len(sub)}, SAT={len(s)}, UNSAT={len(u)}, '
          f'mean_t={sub["elapsed_s"].mean():.6f}, max_t={sub["elapsed_s"].max():.6f}, '
          f'mean_nodes={sub["nodes_generated"].mean():.1f}, max_nodes={int(sub["nodes_generated"].max())}, '
          f'mean_zones={sub["distinct_zones"].mean():.1f}')
print()

# SAT vs UNSAT stats
print('=== SAT vs UNSAT ===')
print(f'SAT mean_t={sat["elapsed_s"].mean():.6f} med={sat["elapsed_s"].median():.6f} max={sat["elapsed_s"].max():.6f}')
print(f'UNSAT mean_t={unsat["elapsed_s"].mean():.6f} med={unsat["elapsed_s"].median():.6f} max={unsat["elapsed_s"].max():.6f}')
print(f'SAT mean_nodes={sat["nodes_generated"].mean():.1f}')
print(f'UNSAT mean_nodes={unsat["nodes_generated"].mean():.1f}')
print()

# Memory check
has_mem = 'peak_memory_kb' in all_df.columns
print(f'Memory columns present: {has_mem}')
if has_mem:
    print(f'Mean peak_memory_kb: {all_df["peak_memory_kb"].mean():.1f}')
    print(f'Max peak_memory_kb: {all_df["peak_memory_kb"].max():.1f}')
print()

# Family A detail
print('=== FAMILY A DETAIL ===')
a = all_df[all_df['family']=='A_depth']
for v in sorted(a['variant'].unique()):
    sub = a[a['variant']==v].sort_values('param_value')
    print(f'{v}: max_pv={int(sub["param_value"].max())}, max_t={sub["elapsed_s"].max():.6f}, max_nodes={int(sub["nodes_generated"].max())}')

# Family B detail - check node invariance 
print('\n=== FAMILY B NODE INVARIANCE ===')
b = all_df[all_df['family']=='B_bounds_M']
for v in sorted(b['variant'].unique()):
    sub = b[b['variant']==v]
    print(f'{v}: node_min={int(sub["nodes_generated"].min())}, node_max={int(sub["nodes_generated"].max())}, '
          f'zone_min={int(sub["distinct_zones"].min())}, zone_max={int(sub["distinct_zones"].max())}')

# Family H detail
print('\n=== FAMILY H DETAIL ===')
h = all_df[all_df['family']=='H_chain']
for v in sorted(h['variant'].unique()):
    sub = h[h['variant']==v].sort_values('param_value')
    vals = list(zip(sub['param_value'].astype(int), sub['nodes_generated'].astype(int), sub['elapsed_s']))
    for pv, nd, t in vals:
        print(f'  {v} n={pv}: nodes={nd}, t={t:.6f}')

# Family I detail
print('\n=== FAMILY I DETAIL ===')
i_df = all_df[all_df['family']=='I_alternation']
for v in sorted(i_df['variant'].unique()):
    sub = i_df[i_df['variant']==v].sort_values('param_value')
    print(f'{v}: max_pv={int(sub["param_value"].max())}, max_t={sub["elapsed_s"].max():.6f}, max_nodes={int(sub["nodes_generated"].max())}')
