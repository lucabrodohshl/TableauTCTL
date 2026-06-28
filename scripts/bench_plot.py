#!/usr/bin/env python3
# ============================================================================
# bench_plot.py - Publication figures + LaTeX tables from results.csv
# ============================================================================
#
# Reads results.csv (from bench_run.py) and produces:
#   plots/<FAMILY>.{pdf,png}        per-family 2-panel curves (time + nodes vs
#                                   the scaling parameter), SAT vs UNSAT,
#                                   timeouts marked, with fitted scaling laws.
#   plots/overview_cactus.{pdf,png} cactus / survival plot across all instances.
#   tables/family_summary.tex       per-variant summary (range, max time/nodes,
#                                   fitted exponent).
#   tables/scaling_laws.tex         log-log time-vs-parameter regressions.
#   tables/verdict_validation.tex   solver verdict vs designed ground truth.
#   tables/scaling_laws.csv         machine-readable fits.
#
# Style follows the existing benchmark_analysis.py conventions: Wong (2011)
# colour-blind-safe palette, serif fonts, dashed grid, log axes where sensible,
# a diverging SAT/UNSAT colour map, multi-format vector output.
#
# Usage:
#   python3 bench_plot.py                          # uses scripts/outputs
#   python3 bench_plot.py --results path/to/results.csv --outdir path
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

try:
    from scipy import stats as _scipy_stats  # noqa: F401
    _HAS_SCIPY = True
except Exception:
    _HAS_SCIPY = False

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_OUTDIR = os.path.join(HERE, "outputs")

# Wong colour-blind-safe palette + a diverging SAT/UNSAT map (see analysis ref).
CB = ["#0072B2", "#D55E00", "#009E73", "#E69F00", "#56B4E9", "#CC79A7", "#F0E442", "#000000"]
VERDICT_COLOR = {"SAT": "#2166AC", "UNSAT": "#B2182B", "TIMEOUT": "#888888", "ERROR": "#000000"}
MARKERS = ["o", "s", "^", "D", "v", "P", "X", "*"]
FORMATS = ["pdf", "png"]


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


def _loglog_fit(x, y):
    """Return (slope, intercept, r2, n) of log10(y) ~ log10(x); None if too few."""
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
    """Return (slope, intercept, r2, n) of log10(y) ~ x (exponential growth)."""
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
    for c in ["param", "time_s", "timeout_s", "max_constant", "nodes",
              "distinct_zones", "loop_checks", "max_depth", "peak_mem_kb", "log_x"]:
        if c in df.columns:
            df[c] = pd.to_numeric(df[c], errors="coerce")
    return df


# ----------------------------------------------------------------------------
# Per-family figure: time (left) and nodes (right) vs the scaling parameter.
# ----------------------------------------------------------------------------

def plot_family(df_fam, plotdir, scaling_rows):
    fam = df_fam["family"].iloc[0]
    fam_label = df_fam["family_label"].iloc[0]
    x_label = df_fam["x_label"].iloc[0]
    log_x = bool(df_fam["log_x"].iloc[0]) if not df_fam["log_x"].isna().all() else False
    ceiling = df_fam["timeout_s"].dropna().max()
    if not np.isfinite(ceiling):
        ceiling = df_fam["time_s"].max() * 1.5 + 1

    fig, (axt, axn) = plt.subplots(1, 2, figsize=(10.0, 4.0))
    variants = sorted(df_fam["variant"].unique())

    for i, var in enumerate(variants):
        sub = df_fam[df_fam["variant"] == var].sort_values("param")
        exp = sub["expected_verdict"].iloc[0]
        color = VERDICT_COLOR.get(exp, CB[i % len(CB)])
        marker = MARKERS[i % len(MARKERS)]
        label = sub["variant_label"].iloc[0]

        solved = sub[sub["verdict"].isin(["SAT", "UNSAT"])]
        to = sub[sub["verdict"].isin(["TIMEOUT", "ERROR"])]

        # Time panel.
        axt.plot(solved["param"], solved["time_s"].clip(lower=1e-6),
                 marker=marker, color=color, label=label, alpha=0.9)
        if len(to):
            axt.scatter(to["param"], [ceiling] * len(to), marker="x",
                        color=color, s=55, zorder=5)

        # Nodes panel (engine stat; may be absent if stats were disabled).
        if "nodes" in sub.columns and solved["nodes"].notna().any():
            axn.plot(solved["param"], solved["nodes"].clip(lower=1),
                     marker=marker, color=color, label=label, alpha=0.9)
            if len(to) and to["nodes"].notna().any():
                axn.scatter(to["param"], to["nodes"].clip(lower=1), marker="x",
                            color=color, s=55, zorder=5)

        # Scaling-law fit (prefer power law on log-x families, else exponential).
        fit = _loglog_fit(solved["param"], solved["time_s"]) if log_x else None
        kind = "power"
        if fit is None:
            fit = _semilog_fit(solved["param"], solved["time_s"])
            kind = "exp"
        if fit is not None:
            sl, ic, r2, n = fit
            scaling_rows.append({
                "family": fam, "variant": var, "expected": exp, "fit_kind": kind,
                "slope": sl, "intercept": ic, "r2": r2, "n_points": n,
                "max_time_s": float(solved["time_s"].max()) if len(solved) else float("nan"),
                "n_timeout": int(len(to)),
            })

    axt.axhline(ceiling, ls=":", color="0.5", lw=1)
    axt.set_yscale("log")
    axn.set_yscale("log")
    if log_x:
        axt.set_xscale("log", base=2)
        axn.set_xscale("log", base=2)
    axt.set_xlabel(x_label); axt.set_ylabel("wall-clock time (s)")
    axn.set_xlabel(x_label); axn.set_ylabel("tableau nodes")
    axt.set_title("runtime")
    axn.set_title("search size")
    axt.legend(frameon=True, edgecolor="0.7")
    fig.suptitle(f"{fam}  -  {fam_label}", fontsize=12)
    fig.tight_layout(rect=(0, 0, 1, 0.96))
    _save(fig, plotdir, fam)


def plot_cactus(df, plotdir):
    """Cactus/survival: #instances solved within time t, split by verdict."""
    fig, ax = plt.subplots(figsize=(6.2, 4.2))
    for verdict in ["SAT", "UNSAT"]:
        sub = df[df["verdict"] == verdict].sort_values("time_s")
        if not len(sub):
            continue
        t = sub["time_s"].clip(lower=1e-6).values
        ax.plot(np.arange(1, len(t) + 1), t, marker=".", ms=4,
                color=VERDICT_COLOR[verdict], label=f"{verdict} ({len(t)})")
    ax.set_yscale("log")
    ax.set_xlabel("instances solved (cumulative)")
    ax.set_ylabel("per-instance wall-clock time (s)")
    ax.set_title("Cactus plot: solved instances vs time")
    ax.legend(frameon=True, edgecolor="0.7")
    fig.tight_layout()
    _save(fig, plotdir, "overview_cactus")


# ----------------------------------------------------------------------------
# LaTeX tables.
# ----------------------------------------------------------------------------

def _tex_escape(s):
    return str(s).replace("_", r"\_").replace("%", r"\%").replace("&", r"\&")


def write_family_summary(df, tabledir):
    lines = [
        r"\begin{table}[t]\centering",
        r"\caption{Synthetic TCTL benchmark families: designed verdict, scaling "
        r"range, peak cost, and fitted growth. $\alpha$ is the log--log slope "
        r"(power-law exponent) for $M$-swept families and the $\log_{10}$-slope "
        r"per unit parameter otherwise.}",
        r"\label{tab:bench-family-summary}",
        r"\small",
        r"\begin{tabular}{llrrrrr}",
        r"\toprule",
        r"Family & Variant & Exp. & \#inst & param range & max $t$ (s) & $\alpha$ \\",
        r"\midrule",
    ]
    for fam in sorted(df["family"].unique()):
        sub = df[df["family"] == fam]
        for var in sorted(sub["variant"].unique()):
            s = sub[sub["variant"] == var].sort_values("param")
            exp = s["expected_verdict"].iloc[0]
            n = len(s)
            pr = f"{int(s['param'].min())}--{int(s['param'].max())}"
            solved = s[s["verdict"].isin(["SAT", "UNSAT"])]
            mt = f"{solved['time_s'].max():.3f}" if len(solved) else "--"
            fit = (_loglog_fit(solved["param"], solved["time_s"])
                   if bool(s["log_x"].iloc[0]) else
                   _semilog_fit(solved["param"], solved["time_s"]))
            al = f"{fit[0]:.2f}" if fit else "--"
            lines.append(
                f"{_tex_escape(fam)} & {_tex_escape(var)} & {exp} & {n} & "
                f"{pr} & {mt} & {al} \\\\")
        lines.append(r"\midrule")
    if lines[-1] == r"\midrule":
        lines.pop()
    lines += [r"\bottomrule", r"\end{tabular}", r"\end{table}", ""]
    with open(os.path.join(tabledir, "family_summary.tex"), "w") as f:
        f.write("\n".join(lines))


def write_verdict_validation(df, tabledir):
    lines = [
        r"\begin{table}[t]\centering",
        r"\caption{Verdict validation: the solver's answer against the "
        r"ground-truth verdict fixed by construction. A correct tableau yields "
        r"zero mismatches.}",
        r"\label{tab:bench-verdict-validation}",
        r"\small",
        r"\begin{tabular}{llrrrrr}",
        r"\toprule",
        r"Family & Variant & Exp. & \#inst & match & mismatch & timeout \\",
        r"\midrule",
    ]
    total_mismatch = 0
    for fam in sorted(df["family"].unique()):
        sub = df[df["family"] == fam]
        for var in sorted(sub["variant"].unique()):
            s = sub[sub["variant"] == var]
            exp = s["expected_verdict"].iloc[0]
            match = int((s["verdict_match"] == "yes").sum())
            mism = int((s["verdict_match"] == "no").sum())
            to = int((s["verdict_match"] == "timeout").sum())
            total_mismatch += mism
            lines.append(
                f"{_tex_escape(fam)} & {_tex_escape(var)} & {exp} & {len(s)} & "
                f"{match} & {mism} & {to} \\\\")
    lines += [
        r"\midrule",
        rf"\multicolumn{{7}}{{l}}{{Total verdict mismatches: {total_mismatch}}} \\",
        r"\bottomrule", r"\end{tabular}", r"\end{table}", ""]
    with open(os.path.join(tabledir, "verdict_validation.tex"), "w") as f:
        f.write("\n".join(lines))
    return total_mismatch


def write_scaling_laws(scaling_rows, tabledir):
    sdf = pd.DataFrame(scaling_rows)
    if len(sdf):
        sdf.to_csv(os.path.join(tabledir, "scaling_laws.csv"), index=False)
    lines = [
        r"\begin{table}[t]\centering",
        r"\caption{Fitted scaling laws for runtime versus the family parameter. "
        r"`power' rows fit $\log t = \alpha\log x + \beta$; `exp' rows fit "
        r"$\log t = \alpha x + \beta$.}",
        r"\label{tab:bench-scaling-laws}",
        r"\small",
        r"\begin{tabular}{lllrrr}",
        r"\toprule",
        r"Family & Variant & fit & $\alpha$ & $R^2$ & \#pts \\",
        r"\midrule",
    ]
    for r in scaling_rows:
        lines.append(
            f"{_tex_escape(r['family'])} & {_tex_escape(r['variant'])} & "
            f"{r['fit_kind']} & {r['slope']:.3f} & {r['r2']:.3f} & {r['n_points']} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}", r"\end{table}", ""]
    with open(os.path.join(tabledir, "scaling_laws.tex"), "w") as f:
        f.write("\n".join(lines))


def main() -> int:
    ap = argparse.ArgumentParser(description="Plot + tabulate TCTL benchmark results.")
    ap.add_argument("--outdir", default=DEFAULT_OUTDIR,
                    help="benchmark root (default scripts/outputs)")
    ap.add_argument("--results", default=None,
                    help="results CSV (default <outdir>/results/results.csv)")
    ap.add_argument("--plotdir", default=None,
                    help="plot output dir (default <outdir>/plots)")
    ap.add_argument("--tabledir", default=None,
                    help="table output dir (default <outdir>/tables)")
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

    scaling_rows: list = []
    for fam in sorted(df["family"].unique()):
        plot_family(df[df["family"] == fam].copy(), plotdir, scaling_rows)
        print(f"[plot]   figure: {fam}")
    plot_cactus(df, plotdir)

    write_family_summary(df, tabledir)
    n_mismatch = write_verdict_validation(df, tabledir)
    write_scaling_laws(scaling_rows, tabledir)

    print(f"[plot] figures -> {plotdir}")
    print(f"[plot] tables  -> {tabledir}")
    print(f"[plot] verdict mismatches vs ground truth: {n_mismatch}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
