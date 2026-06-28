#!/usr/bin/env python3
# ============================================================================
# perf_plot.py - Figures F1-F4 + Tables T1-T2 for the TCTL PERFORMANCE eval
# ============================================================================
#
# Reads outputs_perf/results/results.csv (from bench_run.py --reps 5) and emits
# EXACTLY the deliverables of PERF_EVAL_PLAN.md section 4:
#
#   plots/{pdf,png}/F1_depth.*    RQ1 headline: SAT/UNSAT asymmetry on depth
#   plots/{pdf,png}/F2_drivers.*  RQ1 driver comparison (depth/clocks/M/size + zones)
#   plots/{pdf,png}/F3_uppaal.*   RQ2 UPPAAL-query scalability (size & bound)
#   plots/{pdf,png}/F4_cactus.*   Contrast cactus: practical (RQ2) vs adversarial (RQ1)
#   tables/T1_rq1_drivers.tex     RQ1 driver ranking & fitted scaling laws
#   tables/T2_rq2_envelope.tex    RQ2 practical envelope
#   tables/T1_rq1_drivers.csv     machine-readable RQ1 fits
#   tables/T2_rq2_envelope.csv    machine-readable RQ2 envelope
#
# This is a PERFORMANCE eval: the designed verdict only colours/splits SAT vs
# UNSAT curves; there is NO verdict-validation table (the correctness suite did
# that).  Plotting idioms and fit helpers mirror bench_plot.py.
# ============================================================================

from __future__ import annotations

import argparse
import os
import sys

import numpy as np
import pandas as pd

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402

try:
    from scipy import stats as _scipy_stats  # noqa: F401
    _HAS_SCIPY = True
except Exception:
    _HAS_SCIPY = False

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_OUTDIR = os.path.join(HERE, "outputs_perf")

# Wong colour-blind-safe palette + a diverging SAT/UNSAT map (matches bench_plot).
CB = ["#0072B2", "#D55E00", "#009E73", "#E69F00", "#56B4E9", "#CC79A7", "#F0E442", "#000000"]
VERDICT_COLOR = {"SAT": "#2166AC", "UNSAT": "#B2182B", "TIMEOUT": "#888888", "ERROR": "#000000"}
MARKERS = ["o", "s", "^", "D", "v", "P", "X", "*"]
FORMATS = ["pdf", "png"]
SOLVED = ("SAT", "UNSAT")

# Family taxonomy (PERF_EVAL_PLAN.md).
RQ1_FAMILIES = ["DEPTH", "OBL", "MAXCONST", "SIZE"]
RQ1_ADVERSARIAL = ["DEPTH", "OBL"]           # the nested walls (cactus RQ1 group)
RQ2_FAMILIES = ["U1", "U2", "U3", "U4", "U5"]

# RQ2 shape metadata: family -> (legend label, LaTeX TCTL form for T2).
RQ2_SHAPES = {
    "U1": ("Reachability (EF)",        r"$\mathrm{EF}_{[0,b]}\,\Phi$"),
    "U2": ("Safety (AG)",              r"$\mathrm{AG}_{[0,b]}\,\Phi$"),
    "U3": ("Bounded liveness (AF)",    r"$\mathrm{AF}_{[1,b]}\,\Phi$"),
    "U4": ("Leads-to (AG$\\to$AF)",    r"$\mathrm{AG}(p\!\to\!\mathrm{AF}_{[1,b]}q)$"),
    "U5": ("E[\\,] (EG)",              r"$\mathrm{EG}_{[0,\infty)}\,\Phi$"),
}


def _apply_style():
    plt.rcParams.update({
        "font.family": "serif",
        "font.serif": ["DejaVu Serif", "Times New Roman", "CMU Serif"],
        "font.size": 10,
        "axes.titlesize": 11,
        "axes.labelsize": 10,
        "xtick.labelsize": 9,
        "ytick.labelsize": 9,
        "legend.fontsize": 8,
        "lines.linewidth": 1.6,
        "lines.markersize": 5,
        "axes.grid": True,
        "grid.alpha": 0.35,
        "grid.linestyle": "--",
        "figure.dpi": 120,
        "savefig.dpi": 300,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.04,
    })


def _save(fig, plotdir, stem):
    for fmt in FORMATS:
        d = os.path.join(plotdir, fmt)
        os.makedirs(d, exist_ok=True)
        fig.savefig(os.path.join(d, f"{stem}.{fmt}"), format=fmt)
    plt.close(fig)


# ---- fit helpers (mirrored from bench_plot.py) -----------------------------

def _loglog_fit(x, y):
    """(slope, intercept, r2, n) of log10(y) ~ log10(x); None if <3 points."""
    x = np.asarray(x, float)
    y = np.asarray(y, float)
    mask = (x > 0) & (y > 0) & np.isfinite(x) & np.isfinite(y)
    if mask.sum() < 3:
        return None
    lx, ly = np.log10(x[mask]), np.log10(y[mask])
    if _HAS_SCIPY:
        sl, ic, r, _, _ = _scipy_stats.linregress(lx, ly)
        return sl, ic, r * r, int(mask.sum())
    sl, ic = np.polyfit(lx, ly, 1)
    yhat = sl * lx + ic
    ss_res = np.sum((ly - yhat) ** 2)
    ss_tot = np.sum((ly - ly.mean()) ** 2)
    r2 = 1 - ss_res / ss_tot if ss_tot > 0 else float("nan")
    return sl, ic, r2, int(mask.sum())


def _semilog_fit(x, y):
    """(slope, intercept, r2, n) of log10(y) ~ x (exponential growth)."""
    x = np.asarray(x, float)
    y = np.asarray(y, float)
    mask = (y > 0) & np.isfinite(x) & np.isfinite(y)
    if mask.sum() < 3:
        return None
    lx, ly = x[mask], np.log10(y[mask])
    sl, ic = np.polyfit(lx, ly, 1)
    yhat = sl * lx + ic
    ss_res = np.sum((ly - yhat) ** 2)
    ss_tot = np.sum((ly - ly.mean()) ** 2)
    r2 = 1 - ss_res / ss_tot if ss_tot > 0 else float("nan")
    return sl, ic, r2, int(mask.sum())


def load(results_path):
    df = pd.read_csv(results_path)
    df.columns = df.columns.str.strip()
    for c in df.select_dtypes(include=["object"]).columns:
        df[c] = df[c].astype(str).str.strip()
    for c in ["param", "time_s", "time_min", "time_max", "time_iqr", "timeout_s",
              "max_constant", "nodes", "distinct_zones", "loop_checks", "max_depth",
              "peak_mem_kb", "log_x", "n_reps"]:
        if c in df.columns:
            df[c] = pd.to_numeric(df[c], errors="coerce")
    return df


def _ceiling(df):
    c = df["timeout_s"].dropna().max() if "timeout_s" in df.columns else np.nan
    if not np.isfinite(c):
        c = (df["time_s"].max() * 1.5 + 1) if len(df) else 60.0
    return float(c)


def _split(sub):
    """Return (solved_df sorted by param, timeout_df)."""
    sub = sub.sort_values("param")
    solved = sub[sub["verdict"].isin(SOLVED)]
    to = sub[~sub["verdict"].isin(SOLVED)]
    return solved, to


# ============================================================================
# F1 - RQ1 headline: SAT/UNSAT asymmetry on nesting depth.
# ============================================================================

def fig_f1_depth(df, plotdir):
    fam = df[df["family"] == "DEPTH"].copy()
    if fam.empty:
        print("[plot] F1 skipped: no DEPTH rows")
        return
    ceiling = _ceiling(fam)
    fig, (axt, axn) = plt.subplots(1, 2, figsize=(10.0, 4.2))

    order = [("DEPTH_sat", "SAT"), ("DEPTH_unsat", "UNSAT")]
    for var, exp in order:
        sub = fam[fam["variant"] == var]
        if sub.empty:
            continue
        color = VERDICT_COLOR[exp]
        marker = "o" if exp == "SAT" else "s"
        solved, to = _split(sub)
        # runtime panel
        axt.plot(solved["param"], solved["time_s"].clip(lower=1e-6),
                 marker=marker, color=color, label=f"{exp}", alpha=0.9)
        if len(to):
            axt.scatter(to["param"], [ceiling] * len(to), marker="x",
                        color=color, s=70, zorder=5)
        # nodes panel
        axn.plot(solved["param"], solved["nodes"].clip(lower=1),
                 marker=marker, color=color, label=f"{exp}", alpha=0.9)
        if len(to) and to["nodes"].notna().any():
            axn.scatter(to["param"], to["nodes"].clip(lower=1), marker="x",
                        color=color, s=70, zorder=5)
        # annotate fitted law (semilog: log10 t = alpha d + beta)
        ft = _semilog_fit(solved["param"], solved["time_s"])
        fn = _semilog_fit(solved["param"], solved["nodes"])
        if ft:
            axt.annotate(rf"{exp}: $\log_{{10}}t={ft[0]:.2f}\,d{ft[1]:+.2f}$"
                         rf"  ($R^2$={ft[2]:.2f})",
                         xy=(0.04, 0.94 if exp == "UNSAT" else 0.86),
                         xycoords="axes fraction", color=color, fontsize=8)
        if fn:
            axn.annotate(rf"{exp}: $\log_{{10}}n={fn[0]:.2f}\,d{fn[1]:+.2f}$"
                         rf"  ($R^2$={fn[2]:.2f})",
                         xy=(0.04, 0.94 if exp == "UNSAT" else 0.86),
                         xycoords="axes fraction", color=color, fontsize=8)

    axt.axhline(ceiling, ls=":", color="0.5", lw=1)
    axt.set_yscale("log"); axn.set_yscale("log")
    axt.set_xlabel(r"nesting depth $d$"); axt.set_ylabel("median wall-clock time (s)")
    axn.set_xlabel(r"nesting depth $d$"); axn.set_ylabel("tableau nodes")
    axt.set_title("runtime"); axn.set_title("search size")
    axt.legend(title="verdict", frameon=True, edgecolor="0.7")
    axn.legend(title="verdict", frameon=True, edgecolor="0.7")
    fig.suptitle("F1  -  DEPTH: SAT/UNSAT asymmetry on the nested timed double-check",
                 fontsize=12)
    fig.tight_layout(rect=(0, 0, 1, 0.95))
    _save(fig, plotdir, "F1_depth")
    print("[plot]   F1_depth")


# ============================================================================
# F2 - RQ1 driver comparison (which axes explode, which are absorbed).
# ============================================================================

def _panel_time(ax, df, fam, log_x, title, xlabel, overlay=None):
    sub = df[df["family"] == fam]
    drew = False
    for var in sorted(sub["variant"].unique()):
        s = sub[sub["variant"] == var]
        exp = s["expected_verdict"].iloc[0]
        color = VERDICT_COLOR.get(exp, CB[0])
        marker = "o" if exp == "SAT" else "s"
        solved, to = _split(s)
        if len(solved):
            ax.plot(solved["param"], solved["time_s"].clip(lower=1e-6),
                    marker=marker, color=color, label=exp, alpha=0.9)
            drew = True
        if len(to):
            ax.scatter(to["param"], [_ceiling(df)] * len(to), marker="x",
                       color=color, s=55, zorder=5)
    if overlay is not None:
        os_ = df[df["family"] == overlay]
        for var in sorted(os_["variant"].unique()):
            s = os_[os_["variant"] == var]
            solved, _ = _split(s)
            if len(solved):
                ax.plot(solved["param"], solved["time_s"].clip(lower=1e-6),
                        marker="^", color=CB[2], ls="--",
                        label=f"{overlay} (size)", alpha=0.9)
                drew = True
    ax.set_yscale("log")
    if log_x:
        ax.set_xscale("log", base=2)
    ax.set_xlabel(xlabel); ax.set_ylabel("median time (s)")
    ax.set_title(title)
    if drew:
        ax.legend(frameon=True, edgecolor="0.7", fontsize=7)
    return drew


def fig_f2_drivers(df, plotdir):
    rq1 = df[df["family"].isin(RQ1_FAMILIES)]
    if rq1.empty:
        print("[plot] F2 skipped: no RQ1 rows")
        return
    fig, axes = plt.subplots(2, 2, figsize=(7.5, 5.0))
    (a, b), (c, d) = axes

    _panel_time(a, df, "DEPTH", False, "(a) depth $d$  [F1]", r"nesting depth $d$")
    _panel_time(b, df, "OBL", False, "(b) clocks $k$  [F2]", r"# obligations $k$")
    _panel_time(c, df, "MAXCONST", True, "(c) max-constant $M$  [F3] + size $m$ [F4]",
                r"max constant $M$ / size $m$", overlay="SIZE")

    # Share y-limits across the three time panels for comparability.
    ylo = min(ax.get_ylim()[0] for ax in (a, b, c))
    yhi = max(ax.get_ylim()[1] for ax in (a, b, c))
    for ax in (a, b, c):
        ax.set_ylim(ylo, yhi)

    # Companion search-space panel: distinct_zones vs k (F2).
    obl = df[df["family"] == "OBL"]
    drew = False
    for var in sorted(obl["variant"].unique()):
        s = obl[obl["variant"] == var]
        exp = s["expected_verdict"].iloc[0]
        solved, _ = _split(s)
        if len(solved) and solved["distinct_zones"].notna().any():
            d.plot(solved["param"], solved["distinct_zones"].clip(lower=1),
                   marker="o" if exp == "SAT" else "s",
                   color=VERDICT_COLOR.get(exp, CB[0]), label=exp, alpha=0.9)
            drew = True
    d.set_yscale("log")
    d.set_xlabel(r"# obligations $k$"); d.set_ylabel("distinct zones (DBM)")
    d.set_title("(d) zone growth: distinct\\_zones vs $k$  [F2]")
    if drew:
        d.legend(frameon=True, edgecolor="0.7", fontsize=7)

    #fig.suptitle("F2  -  RQ1 drivers: depth & clocks are walls; $M$ and size are absorbed",             fontsize=12)
    fig.tight_layout(rect=(0, 0, 1, 0.96))
    _save(fig, plotdir, "F2_drivers")
    print("[plot]   F2_drivers")


# ============================================================================
# F3 - RQ2 UPPAAL-query scalability (size and bound).
# ============================================================================

def fig_f3_uppaal(df, plotdir, time_ylim=None):
    rq2 = df[df["family"].isin(RQ2_FAMILIES)]
    if rq2.empty:
        print("[plot] F3 skipped: no RQ2 rows")
        return
    fig, (axm, axb) = plt.subplots(1, 2, figsize=(10.5, 4.4))
    ceiling = _ceiling(df)

    shape_color = {f: CB[i % len(CB)] for i, f in enumerate(RQ2_FAMILIES)}

    # Left: time vs query size m (SAT size sweeps).
    for fam in RQ2_FAMILIES:
        sub = df[(df["family"] == fam) & (df["param_name"] == "m")
                 & (df["expected_verdict"] == "SAT")]
        solved, to = _split(sub)
        col = shape_color[fam]
        if len(solved):
            axm.plot(solved["param"], solved["time_s"].clip(lower=1e-6),
                     marker="o", color=col, label=RQ2_SHAPES[fam][0], alpha=0.9)
        if len(to):
            axm.scatter(to["param"], [ceiling] * len(to), marker="x", color=col, s=55)

    # Right: time vs time-bound b (SAT solid, UNSAT dashed).
    for fam in RQ2_FAMILIES:
        col = shape_color[fam]
        for exp, ls in (("SAT", "-"), ("UNSAT", "--")):
            sub = df[(df["family"] == fam) & (df["param_name"] == "b")
                     & (df["expected_verdict"] == exp)]
            solved, to = _split(sub)
            if len(solved):
                axb.plot(solved["param"], solved["time_s"].clip(lower=1e-6),
                         marker="o" if exp == "SAT" else "s", ls=ls, color=col,
                         alpha=0.9)
            if len(to):
                axb.scatter(to["param"], [ceiling] * len(to), marker="x", color=col, s=55)

    for ax in (axm, axb):
        ax.set_yscale("log"); ax.set_xscale("log", base=2)
        ax.set_ylabel("median wall-clock time (s)")
    axm.set_xlabel(r"query size $m$  ($b=4$ fixed)")
    axb.set_xlabel(r"time-bound $b$  ($m=4$ fixed)")
    axm.set_title("scaling in query size"); axb.set_title("scaling in time-bound")
    if time_ylim:
        axm.set_ylim(*time_ylim); axb.set_ylim(*time_ylim)

    # Legends: shapes (colour) on the left; SAT/UNSAT linestyle on the right.
    axm.legend(title="UPPAAL shape", frameon=True, edgecolor="0.7", fontsize=7, ncol=1)
    style_handles = [Line2D([0], [0], color="0.3", ls="-", marker="o", label="SAT"),
                     Line2D([0], [0], color="0.3", ls="--", marker="s", label="UNSAT")]
    axb.legend(handles=style_handles, title="verdict", frameon=True,
               edgecolor="0.7", fontsize=8)
    fig.suptitle("F3  -  RQ2: flat UPPAAL-shaped queries stay sub-second in size and bound",
                 fontsize=12)
    fig.tight_layout(rect=(0, 0, 1, 0.95))
    _save(fig, plotdir, "F3_uppaal")
    print("[plot]   F3_uppaal")


# ============================================================================
# F4 - Contrast cactus: practical (RQ2) vs adversarial nested (RQ1 F1/F2).
# ============================================================================

def fig_f4_cactus(df, plotdir):
    fig, ax = plt.subplots(figsize=(6.6, 4.6))
    ceiling = _ceiling(df)

    groups = [
        ("RQ2 flat UPPAAL (U1-U5)", df[df["family"].isin(RQ2_FAMILIES)], CB[0], "o"),
        ("RQ1 adversarial nested (F1 depth, F2 clocks)",
         df[df["family"].isin(RQ1_ADVERSARIAL)], CB[1], "s"),
    ]
    for label, sub, color, marker in groups:
        if sub.empty:
            continue
        solved = sub[sub["verdict"].isin(SOLVED)].sort_values("time_s")
        n_to = int((~sub["verdict"].isin(SOLVED)).sum())
        t = solved["time_s"].clip(lower=1e-6).values
        xs = np.arange(1, len(t) + 1)
        ax.plot(xs, t, marker=marker, ms=4, color=color,
                label=f"{label}  [{len(t)} solved, {n_to} TO]")
        if n_to:
            ax.scatter(np.arange(len(t) + 1, len(t) + n_to + 1),
                       [ceiling] * n_to, marker="x", color=color, s=45, zorder=5)

    ax.axhline(ceiling, ls=":", color="0.5", lw=1)
    ax.set_yscale("log")
    ax.set_xlabel("instances solved (cumulative, sorted by time)")
    ax.set_ylabel("per-instance median wall-clock time (s)")
    ax.set_title("F4  -  Cactus: practical vs adversarial")
    ax.legend(frameon=True, edgecolor="0.7", loc="upper left")
    fig.tight_layout()
    _save(fig, plotdir, "F4_cactus")
    print("[plot]   F4_cactus")


# ============================================================================
# Tables.
# ============================================================================

def _tex_escape(s):
    return str(s).replace("\\", r"\textbackslash{}").replace("_", r"\_") \
                 .replace("%", r"\%").replace("&", r"\&")


def _fit_for(family, solved):
    """Return (kind, alpha, r2, n) per the plan: semilog for linear-x families,
    log-log for log-x families; classify near-zero slope as 'flat'."""
    if solved.empty or len(solved) < 3:
        return ("-", float("nan"), float("nan"), len(solved))
    log_x = bool(solved["log_x"].iloc[0])
    if log_x:
        ft = _loglog_fit(solved["param"], solved["time_s"])
        if ft is None:
            return ("-", float("nan"), float("nan"), len(solved))
        sl, _, r2, n = ft
        kind = "flat" if abs(sl) < 0.10 else "power"
        return (kind, sl, r2, n)
    ft = _semilog_fit(solved["param"], solved["time_s"])
    if ft is None:
        return ("-", float("nan"), float("nan"), len(solved))
    sl, _, r2, n = ft
    kind = "flat" if abs(sl) < 0.02 else "exp"
    return (kind, sl, r2, n)


def _num(n):
    """Integer with a LaTeX-safe thousands separator: 7638 -> 7{,}638."""
    return f"{int(n):,}".replace(",", "{,}")


def write_t1(df, tabledir):
    """T1 - RQ1 driver ranking & fitted scaling laws (one row per family x verdict).

    Emits the paper table (label tab:perf-rq1): pretty family names, the dominant
    exp-fit alpha in \\textbf{}, LaTeX-safe thousands, negatives in math mode.
    Hand-authoring is avoided: evaluation.tex \\input{}s this file verbatim.
    """
    pretty = {"DEPTH": "Depth", "OBL": "Clocks", "MAXCONST": "Max-const", "SIZE": "Size"}
    factor = {"DEPTH": r"depth $d$", "OBL": r"clocks $k$",
              "MAXCONST": r"$M$", "SIZE": r"size $m$"}
    rows = []
    for fam in RQ1_FAMILIES:
        sub = df[df["family"] == fam]
        for var in sorted(sub["variant"].unique()):
            s = sub[sub["variant"] == var]
            exp = s["expected_verdict"].iloc[0]
            solved = s[s["verdict"].isin(SOLVED)]
            to = s[~s["verdict"].isin(SOLVED)]
            pr = f"{int(s['param'].min())}--{int(s['param'].max())}"
            kind, alpha, r2, _ = _fit_for(fam, solved)
            rows.append({
                "family": fam, "factor": factor.get(fam, fam), "verdict": exp,
                "range": pr, "fit": kind, "alpha": alpha, "r2": r2,
                "max_time_s": float(solved["time_s"].max()) if len(solved) else float("nan"),
                "max_nodes": int(solved["nodes"].max()) if solved["nodes"].notna().any() else 0,
                "max_zones": int(solved["distinct_zones"].max()) if solved["distinct_zones"].notna().any() else 0,
                "n_timeout": int(len(to)),
            })
    rdf = pd.DataFrame(rows)
    rdf.to_csv(os.path.join(tabledir, "T1_rq1_drivers.csv"), index=False)

    # The dominant driver: largest |alpha| among exponential (linear-x) fits; its
    # alpha cell is bold-faced, mirroring the paper.
    exp_alphas = [abs(r["alpha"]) for r in rows
                  if r["fit"] == "exp" and np.isfinite(r["alpha"])]
    dom = max(exp_alphas) if exp_alphas else None

    lines = [
        r"\begin{table}[t]\centering",
        r"\caption{\textbf{RQ1 cost-driver ranking and fitted scaling laws.} "
        r"One row per family $\times$ verdict; fits exclude timeouts. Linear-$x$ "
        r"families (depth, clocks) use a semilog fit $\log_{10}t=\alpha x+\beta$, "
        r"log-$x$ families ($M$, size) a log--log fit $\log_{10}t=\alpha\log_{10}x"
        r"+\beta$ (near-zero $\alpha\Rightarrow$ flat). "
        r"Ranking: $\textit{depth}\gg\textit{clocks}\gg\{M,\text{size}\}$.}"
        r"\label{tab:perf-rq1}",
        r"\small\setlength{\tabcolsep}{4pt}",
        r"\begin{tabular}{llllrrrrrr}",
        r"\toprule",
        r"Family & Factor & Verd. & Range & Fit & $\alpha$ & $R^2$ & "
        r"max $t$(s) & max nodes & \#TO \\",
        r"\midrule",
    ]
    for r in rows:
        if not np.isfinite(r["alpha"]):
            a = "--"
        else:
            a = f"{r['alpha']:.2f}"
            if r["alpha"] < 0:
                a = f"${a}$"                         # render the minus sign
            if dom is not None and r["fit"] == "exp" and abs(r["alpha"]) == dom:
                a = rf"\textbf{{{a}}}"               # dominant driver in bold
        r2 = "--" if not np.isfinite(r["r2"]) else f"{r['r2']:.2f}"
        mt = "--" if not np.isfinite(r["max_time_s"]) else f"{r['max_time_s']:.2f}"
        lines.append(
            f"{pretty.get(r['family'], r['family'])} & {r['factor']} & {r['verdict']} & "
            f"{r['range']} & {r['fit']} & {a} & {r2} & {mt} & "
            f"{_num(r['max_nodes'])} & {r['n_timeout']} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}", r"\end{table}", ""]
    with open(os.path.join(tabledir, "T1_rq1_drivers.tex"), "w") as f:
        f.write("\n".join(lines))
    return rdf


def write_t2(df, tabledir):
    """T2 - RQ2 practical envelope (one row per UPPAAL shape)."""
    rows = []
    for fam in RQ2_FAMILIES:
        sub = df[df["family"] == fam]
        if sub.empty:
            continue
        solved = sub[sub["verdict"].isin(SOLVED)]
        to = sub[~sub["verdict"].isin(SOLVED)]
        msub = sub[sub["param_name"] == "m"]
        bsub = sub[sub["param_name"] == "b"]
        mr = (f"{int(msub['param'].min())}--{int(msub['param'].max())}"
              if len(msub) else "--")
        br = (f"{int(bsub['param'].min())}--{int(bsub['param'].max())}"
              if len(bsub) else "--")
        rows.append({
            "shape": fam, "label": RQ2_SHAPES[fam][0], "tctl": RQ2_SHAPES[fam][1],
            "m_range": mr, "b_range": br,
            "max_time_s": float(solved["time_s"].max()) if len(solved) else float("nan"),
            "max_nodes": int(solved["nodes"].max()) if solved["nodes"].notna().any() else 0,
            "max_zones": int(solved["distinct_zones"].max()) if solved["distinct_zones"].notna().any() else 0,
            "max_mem_kb": int(solved["peak_mem_kb"].max()) if solved["peak_mem_kb"].notna().any() else 0,
            "n_solved": int(len(solved)), "n_total": int(len(sub)),
            "n_timeout": int(len(to)),
        })
    rdf = pd.DataFrame(rows)
    rdf.to_csv(os.path.join(tabledir, "T2_rq2_envelope.csv"), index=False)

    n_solved_all = sum(r["n_solved"] for r in rows)
    n_total_all = sum(r["n_total"] for r in rows)
    n_to_all = sum(r["n_timeout"] for r in rows)
    # Caption asserts the count and the timeout-free property the table demonstrates.
    if n_to_all == 0:
        tail = (rf"all ${n_total_all}$ instances were solved, none timed out.")
    else:
        tail = (rf"${n_solved_all}$ of ${n_total_all}$ instances were solved "
                rf"(${n_to_all}$ timed out).")

    lines = [
        r"\begin{table}[t]\centering",
        r"\caption{\textbf{RQ2 practical envelope for flat \textsc{Uppaal}-shaped "
        r"queries.} Worst-case resources across the entire size ($m$) and "
        r"time-bound ($b$) sweep, per shape; " + tail + r"}"
        r"\label{tab:perf-rq2}",
        r"\small\setlength{\tabcolsep}{5pt}",
        r"\begin{tabular}{llllrrrr}",
        r"\toprule",
        r"Shape & TCTL form & $m$ & $b$ & max $t$(s) & max nodes & "
        r"max zones & max mem(kB) \\",
        r"\midrule",
    ]
    for r in rows:
        mt = "--" if not np.isfinite(r["max_time_s"]) else f"{r['max_time_s']:.2f}"
        lines.append(
            # labels are authored as valid LaTeX (e.g. AG$\to$AF); do not escape.
            f"{r['label']} & {r['tctl']} & {r['m_range']} & "
            f"{r['b_range']} & {mt} & {_num(r['max_nodes'])} & "
            f"{_num(r['max_zones'])} & {_num(r['max_mem_kb'])} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}", r"\end{table}", ""]
    with open(os.path.join(tabledir, "T2_rq2_envelope.tex"), "w") as f:
        f.write("\n".join(lines))
    return rdf


def main() -> int:
    ap = argparse.ArgumentParser(description="Figures F1-F4 + Tables T1-T2 for the perf eval.")
    ap.add_argument("--outdir", default=DEFAULT_OUTDIR,
                    help="benchmark root (default scripts/outputs_perf)")
    ap.add_argument("--results", default=None,
                    help="results CSV (default <outdir>/results/results.csv)")
    ap.add_argument("--plotdir", default=None)
    ap.add_argument("--tabledir", default=None)
    args = ap.parse_args()

    results_path = args.results or os.path.join(args.outdir, "results", "results.csv")
    if not os.path.exists(results_path):
        print(f"[plot] results not found: {results_path}\n"
              f"       run bench_run.py first.", file=sys.stderr)
        return 2
    plotdir = args.plotdir or os.path.join(args.outdir, "plots")
    tabledir = args.tabledir or os.path.join(args.outdir, "tables")
    os.makedirs(plotdir, exist_ok=True)
    os.makedirs(tabledir, exist_ok=True)

    _apply_style()
    df = load(results_path)
    print(f"[plot] loaded {len(df)} rows, {df['family'].nunique()} families")

    # Shared time y-limits so F3 is visually comparable with F1/F2 (plan: same scale).
    solved_all = df[df["verdict"].isin(SOLVED)]
    if len(solved_all):
        tmax = max(solved_all["time_s"].max(), _ceiling(df))
        tmin = max(1e-4, solved_all["time_s"].clip(lower=1e-6).min() * 0.5)
        time_ylim = (tmin, tmax * 1.4)
    else:
        time_ylim = None

    fig_f1_depth(df, plotdir)
    fig_f2_drivers(df, plotdir)
    fig_f3_uppaal(df, plotdir, time_ylim=time_ylim)
    fig_f4_cactus(df, plotdir)

    t1 = write_t1(df, tabledir)
    t2 = write_t2(df, tabledir)

    print(f"[plot] figures -> {plotdir}/{{pdf,png}}")
    print(f"[plot] tables  -> {tabledir}")
    print("\n[plot] === T1 (RQ1 drivers) ===")
    print(t1.to_string(index=False))
    print("\n[plot] === T2 (RQ2 envelope) ===")
    print(t2.to_string(index=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
