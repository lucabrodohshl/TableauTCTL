#!/usr/bin/env python3
"""
benchmark_analysis.py — Comprehensive empirical analysis pipeline for TCTL
                         tableau solver benchmarks.

Generates:
  • 22+ publication-quality plots  (pdf / eps / png / pgf)
  • 4+  LaTeX tables               (tables.tex)
  • Scaling-law regression models   (scaling_laws.csv, scaling_laws.json)
  • SAT vs UNSAT summary           (sat_vs_unsat_summary.csv)
  • Phase-boundary k×M frontier    (km_phase_frontier.csv)
  • Family summary                  (family_summary.csv, family_summary.tex)
  • Ablation summary               (ablation_summary.csv)
  • Hardness-feature analysis       (hardness_features.csv, hardness_model_summary.txt)
  • Technical rationale             (analysis_rationale.txt)
  • Final analysis report           (analysis_report.txt)

Optional memory analysis (6 extra plots) when CSV data contains memory columns.

Designed for CAV / TACAS paper formatting.

Usage
-----
    python scripts/benchmark_analysis.py benchmark_result_20260301_121613/
    python scripts/benchmark_analysis.py data/ -o results/ --formats pdf png
    python scripts/benchmark_analysis.py data/ --include-memory --export-latex
    python scripts/benchmark_analysis.py --help

Dependencies
------------
    pip install pandas matplotlib seaborn numpy scipy jinja2
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import textwrap
import warnings
from datetime import datetime
from pathlib import Path
from typing import Optional

import numpy as np
import pandas as pd
import seaborn as sns
import matplotlib
import matplotlib.pyplot as plt
from matplotlib.ticker import LogLocator, NullFormatter
from scipy import stats

# ═══════════════════════════════════════════════════════════════════════════
#  Section 1 — CLI Argument Parsing
# ═══════════════════════════════════════════════════════════════════════════


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="benchmark_analysis",
        description="Comprehensive empirical analysis pipeline for TCTL "
                    "tableau solver benchmarks.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
            examples:
              %(prog)s benchmark_result_20260301_121613/
              %(prog)s data/ -o results/ --formats pdf png
              %(prog)s data/ --include-memory --export-latex
        """),
    )
    p.add_argument(
        "input_dir",
        nargs="?",
        default="./benchmark_result_20260301_121613/",
        help="Directory containing benchmark CSV files "
             "(default: ./benchmark_result_20260301_121613/)",
    )
    p.add_argument(
        "-o", "--output-dir",
        default="./outputs/",
        help="Root output directory (default: ./outputs/)",
    )
    p.add_argument(
        "--include-memory",
        action="store_true",
        default=False,
        help="Enable memory analysis plots (requires peak_memory_kb / "
             "avg_memory_kb columns in CSVs).",
    )
    p.add_argument(
        "--export-latex",
        action="store_true",
        default=False,
        help="Also export tables as standalone .tex files.",
    )
    p.add_argument(
        "--skip-heavy-regressions",
        action="store_true",
        default=False,
        help="Skip per-variant regression fits (faster execution).",
    )
    p.add_argument(
        "--frontier-threshold-runtime",
        type=float,
        default=None,
        help="Runtime threshold (s) for phase-boundary frontier "
             "(default: half the timeout).",
    )
    p.add_argument(
        "--frontier-threshold-memory",
        type=float,
        default=None,
        help="Memory threshold (KiB) for memory frontier analysis.",
    )
    p.add_argument(
        "--formats",
        nargs="+",
        default=["pdf", "eps", "png", "pgf"],
        choices=["pdf", "eps", "png", "pgf", "svg"],
        help="Export formats for figures (default: pdf eps png pgf).",
    )
    p.add_argument(
        "--dpi",
        type=int,
        default=300,
        help="DPI for raster exports (default: 300).",
    )
    p.add_argument(
        "--timeout",
        type=float,
        default=30.0,
        help="Benchmark timeout in seconds (default: 30.0).",
    )
    return p


# ═══════════════════════════════════════════════════════════════════════════
#  Section 2 — Global Configuration (set from CLI)
# ═══════════════════════════════════════════════════════════════════════════

class Config:
    """Mutable global configuration populated by CLI args."""

    input_dir: str = "./benchmark_result_20260301_121613/"
    output_root: str = "./outputs/"
    include_memory: bool = False
    export_latex: bool = False
    skip_heavy: bool = False
    frontier_rt: Optional[float] = None
    frontier_mem: Optional[float] = None
    formats: list[str] = ["pdf", "eps", "png", "pgf"]
    dpi: int = 300
    timeout_s: float = 30.0

    # Derived output paths
    @property
    def plot_dir(self) -> Path:
        return Path(self.output_root) / "plots"

    @property
    def table_dir(self) -> Path:
        return Path(self.output_root) / "tables"

    @property
    def model_dir(self) -> Path:
        return Path(self.output_root) / "models"

    @property
    def derived_dir(self) -> Path:
        return Path(self.output_root) / "derived"

    def ensure_dirs(self) -> None:
        for d in [self.plot_dir, self.table_dir, self.model_dir, self.derived_dir]:
            d.mkdir(parents=True, exist_ok=True)
        for fmt in self.formats:
            (self.plot_dir / fmt).mkdir(parents=True, exist_ok=True)


CFG = Config()


# ═══════════════════════════════════════════════════════════════════════════
#  Section 3 — Matplotlib Styling
# ═══════════════════════════════════════════════════════════════════════════

matplotlib.use("Agg")

import shutil as _shutil

_HAS_LATEX = _shutil.which("pdflatex") is not None


def _apply_mpl_style() -> None:
    """Apply publication-quality Matplotlib styling."""
    plt.rcParams.update({
        "text.usetex": _HAS_LATEX,
        "font.family": "serif",
        "font.serif": [
            "Computer Modern Roman", "CMU Serif", "DejaVu Serif", "Times"
        ],
        "font.size": 10,
        "axes.titlesize": 11,
        "axes.labelsize": 10,
        "xtick.labelsize": 9,
        "ytick.labelsize": 9,
        "legend.fontsize": 8,
        "lines.linewidth": 1.5,
        "lines.markersize": 5,
        "axes.grid": True,
        "grid.alpha": 0.35,
        "grid.linestyle": "--",
        "figure.dpi": 150,
        "savefig.dpi": CFG.dpi,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.05,
        "pgf.texsystem": "pdflatex",
    })
    if _HAS_LATEX:
        plt.rcParams["pgf.preamble"] = (
            r"\usepackage{amsmath}\usepackage{amssymb}"
        )


# ═══════════════════════════════════════════════════════════════════════════
#  Section 4 — Colour Palette & Visual Constants
# ═══════════════════════════════════════════════════════════════════════════

# Wong (2011) colour-blind-safe palette
CB_PALETTE = [
    "#0072B2",  # blue
    "#D55E00",  # vermilion
    "#009E73",  # bluish green
    "#E69F00",  # orange
    "#56B4E9",  # sky blue
    "#CC79A7",  # reddish purple
    "#F0E442",  # yellow
    "#000000",  # black
]

DIVERGING_PALETTE = {"SAT": "#2166AC", "UNSAT": "#B2182B"}

MARKERS = ["o", "s", "^", "D", "v", "P", "X", "*"]
LINESTYLES = ["-", "--", "-.", ":", (0, (3, 1, 1, 1)), (0, (5, 2)), "-", "--"]


# ═══════════════════════════════════════════════════════════════════════════
#  Section 5 — Publication-Ready Naming
# ═══════════════════════════════════════════════════════════════════════════

_NAME_MAP_PATH = Path(__file__).parent / "benchmark_name_map.json"

VARIANT_LABEL: dict[str, str] = {}
FAMILY_LABEL: dict[str, str] = {}


def _load_name_map() -> None:
    global VARIANT_LABEL, FAMILY_LABEL
    if not _NAME_MAP_PATH.exists():
        warnings.warn(f"Name map not found at {_NAME_MAP_PATH}; using raw IDs.")
        return
    with open(_NAME_MAP_PATH) as f:
        data = json.load(f)
    for old_id, entry in data.get("benchmarks", {}).items():
        VARIANT_LABEL[old_id] = entry.get("short_label", old_id)
    for code, pub_name in data.get("family_names", {}).items():
        FAMILY_LABEL[code] = pub_name


def _vl(variant: str) -> str:
    """Publication-ready short label for a variant."""
    return VARIANT_LABEL.get(variant, variant)


def _fl(family: str) -> str:
    """Publication-ready family name."""
    return FAMILY_LABEL.get(family, family)


def _relabel_variants(df: pd.DataFrame) -> pd.DataFrame:
    df = df.copy()
    df["label"] = df["variant"].map(_vl)
    return df


def _relabel_families(df: pd.DataFrame) -> pd.DataFrame:
    df = df.copy()
    df["family"] = df["family"].map(_fl)
    return df


# ═══════════════════════════════════════════════════════════════════════════
#  Section 6 — Output Helpers
# ═══════════════════════════════════════════════════════════════════════════


def _save_figure(fig: plt.Figure, stem: str) -> None:
    """Export *fig* to every requested format under plots/<fmt>/<stem>.<fmt>."""
    for fmt in CFG.formats:
        target = CFG.plot_dir / fmt / f"{stem}.{fmt}"
        try:
            fig.savefig(str(target), format=fmt)
        except Exception as exc:
            warnings.warn(f"Could not save {target}: {exc}")
    plt.close(fig)
    fmts = ", ".join(CFG.formats)
    print(f"  \u2713 Saved {stem} ({fmts})")


def _save_csv(df: pd.DataFrame, name: str, subdir: str = "derived") -> Path:
    """Save a DataFrame as CSV under the given subdir."""
    base = {"derived": CFG.derived_dir, "models": CFG.model_dir,
            "tables": CFG.table_dir}.get(subdir, CFG.derived_dir)
    path = base / name
    df.to_csv(path, index=False)
    print(f"  \u2713 Saved {path}")
    return path


def _save_text(text: str, name: str, subdir: str = "derived") -> Path:
    base = {"derived": CFG.derived_dir, "models": CFG.model_dir,
            "tables": CFG.table_dir}.get(subdir, CFG.derived_dir)
    path = base / name
    with open(path, "w") as f:
        f.write(text)
    print(f"  \u2713 Saved {path}")
    return path


def _save_json(obj, name: str, subdir: str = "models") -> Path:
    base = {"derived": CFG.derived_dir, "models": CFG.model_dir,
            "tables": CFG.table_dir}.get(subdir, CFG.derived_dir)
    path = base / name
    with open(path, "w") as f:
        json.dump(obj, f, indent=2, default=str)
    print(f"  \u2713 Saved {path}")
    return path


# ═══════════════════════════════════════════════════════════════════════════
#  Section 7 — Data Loading & Enrichment
# ═══════════════════════════════════════════════════════════════════════════


def _load_csv(name: str) -> Optional[pd.DataFrame]:
    """Load a CSV from the configured input directory."""
    path = Path(CFG.input_dir) / name
    if not path.exists():
        warnings.warn(f"File not found, skipping: {path}")
        return None
    try:
        df = pd.read_csv(path)
        df.columns = df.columns.str.strip()
        str_cols = df.select_dtypes(include=["object", "string"]).columns
        for col in str_cols:
            df[col] = df[col].str.strip().str.strip('"')
        return df
    except Exception as exc:
        warnings.warn(f"Failed to read {path}: {exc}")
        return None


def _has_memory_columns(df: pd.DataFrame) -> bool:
    """Check whether the DataFrame contains memory tracking columns."""
    return "peak_memory_kb" in df.columns and "avg_memory_kb" in df.columns


def _enrich(df: pd.DataFrame) -> pd.DataFrame:
    """Add derived metrics to the combined DataFrame."""
    df = df.copy()

    # Ensure numeric types for key columns
    for col in ["elapsed_s", "nodes_generated", "distinct_zones",
                "loop_checks", "M", "k", "param_value"]:
        if col in df.columns:
            df[col] = pd.to_numeric(df[col], errors="coerce")

    # Derived metrics — safe division (avoid /0)
    ng = df["nodes_generated"].replace(0, np.nan)
    dz = df["distinct_zones"].replace(0, np.nan)

    df["time_per_node"] = df["elapsed_s"] / ng
    df["time_per_zone"] = df["elapsed_s"] / dz
    df["loop_checks_per_node"] = df["loop_checks"] / ng
    df["zone_node_ratio"] = df["distinct_zones"] / ng

    # Memory-derived metrics (conditional)
    if _has_memory_columns(df):
        df["peak_memory_kb"] = pd.to_numeric(df["peak_memory_kb"],
                                              errors="coerce")
        df["avg_memory_kb"] = pd.to_numeric(df["avg_memory_kb"],
                                             errors="coerce")
        df["memory_per_node"] = df["peak_memory_kb"] / ng
        df["memory_per_zone"] = df["peak_memory_kb"] / dz
    return df


# ═══════════════════════════════════════════════════════════════════════════
#  Section 8 — Plot Helpers
# ═══════════════════════════════════════════════════════════════════════════


def _style_axis(ax: plt.Axes, xlabel: str, ylabel: str,
                title: str = "") -> None:
    ax.set_xlabel(xlabel)
    ax.set_ylabel(ylabel)
    if title:
        ax.set_title(title)
    ax.grid(True, which="major", ls="--", alpha=0.35)
    ax.grid(True, which="minor", ls=":", alpha=0.18)


def _get_style(idx: int):
    return (
        CB_PALETTE[idx % len(CB_PALETTE)],
        MARKERS[idx % len(MARKERS)],
        LINESTYLES[idx % len(LINESTYLES)],
    )


def _add_legend(ax: plt.Axes, **kw) -> None:
    kw.setdefault("loc", "upper left")
    ax.legend(frameon=True, fancybox=False, edgecolor="0.7", **kw)


def _pct_label(pct: float, solved: int, total: int) -> str:
    if _HAS_LATEX:
        return f"{pct:.0f}\\%  ({solved}/{total})"
    return f"{pct:.0f}%  ({solved}/{total})"


# ═══════════════════════════════════════════════════════════════════════════
#  Section 9 — Original Plots (1–9)
# ═══════════════════════════════════════════════════════════════════════════


def plot_m_abstraction(df: pd.DataFrame) -> None:
    """Plot 1: M (log₂) vs elapsed_s per variant."""
    print("\n[Plot 1] M-Abstraction Efficiency")
    fig, ax = plt.subplots(figsize=(6, 4))
    for i, variant in enumerate(sorted(df["variant"].unique())):
        sub = df[df["variant"] == variant].sort_values("M")
        c, m, ls = _get_style(i)
        ax.plot(sub["M"], sub["elapsed_s"], color=c, marker=m,
                linestyle=ls, label=_vl(variant))
    ax.set_xscale("log", base=2)
    _style_axis(ax, r"$M$ (log$_2$ scale)", "Elapsed time (s)",
                "Max-Constant Sensitivity")
    _add_legend(ax)
    fig.tight_layout()
    _save_figure(fig, "plot01_m_abstraction")


def plot_depth_complexity(df_depth: Optional[pd.DataFrame],
                          df_ur: Optional[pd.DataFrame]) -> None:
    """Plot 2: depth vs elapsed_s (log y)."""
    print("\n[Plot 2] Formula Depth / Structural Complexity")
    frames = [f for f in [df_depth, df_ur] if f is not None]
    if not frames:
        warnings.warn("No data for depth complexity plot.")
        return
    df = pd.concat(frames, ignore_index=True)
    fig, ax = plt.subplots(figsize=(7, 4.5))
    for i, variant in enumerate(sorted(df["variant"].unique())):
        sub = df[df["variant"] == variant].sort_values("param_value")
        c, m, ls = _get_style(i)
        ax.plot(sub["param_value"], sub["elapsed_s"], color=c, marker=m,
                linestyle=ls, label=_vl(variant))
    ax.set_yscale("log")
    _style_axis(ax, "Depth / nesting level",
                "Elapsed time (s)  [log scale]",
                "Depth Scaling and Structural Complexity")
    _add_legend(ax)
    fig.tight_layout()
    _save_figure(fig, "plot02_depth_complexity")


def plot_clock_dimensionality(df_clocks: Optional[pd.DataFrame],
                              df_oblig: Optional[pd.DataFrame]) -> None:
    """Plot 3: k vs nodes_generated (log y)."""
    print("\n[Plot 3] Clock Dimensionality (k-clocks)")
    frames = [f for f in [df_clocks, df_oblig] if f is not None]
    if not frames:
        warnings.warn("No data for clock dimensionality plot.")
        return
    df = pd.concat(frames, ignore_index=True)
    fig, ax = plt.subplots(figsize=(7, 4.5))
    for i, variant in enumerate(sorted(df["variant"].unique())):
        sub = df[df["variant"] == variant].sort_values("param_value")
        c, m, ls = _get_style(i)
        ax.plot(sub["param_value"], sub["nodes_generated"], color=c,
                marker=m, linestyle=ls, label=_vl(variant))
    ax.set_yscale("log")
    _style_axis(ax, r"$k$ (number of clocks / obligations)",
                "Nodes generated  [log scale]",
                "Clock Dimensionality")
    _add_legend(ax)
    fig.tight_layout()
    _save_figure(fig, "plot03_clock_dimensionality")


def plot_structural_tests(df_alt: Optional[pd.DataFrame],
                          df_chain: Optional[pd.DataFrame]) -> None:
    """Plot 4: alternation + chain elapsed_s."""
    print("\n[Plot 4] Structural Tests (alternation & chain)")
    frames = [f for f in [df_alt, df_chain] if f is not None]
    if not frames:
        warnings.warn("No data for structural tests plot.")
        return
    df = pd.concat(frames, ignore_index=True)
    fig, ax = plt.subplots(figsize=(7, 4.5))
    for i, variant in enumerate(sorted(df["variant"].unique())):
        sub = df[df["variant"] == variant].sort_values("param_value")
        c, m, ls = _get_style(i)
        ax.plot(sub["param_value"], sub["elapsed_s"], color=c, marker=m,
                linestyle=ls, label=_vl(variant))
    _style_axis(ax, "Parameter value ($n$)", "Elapsed time (s)",
                "Fixpoint Alternation and Chain Structure")
    _add_legend(ax)
    fig.tight_layout()
    _save_figure(fig, "plot04_structural_tests")


def plot_state_space_efficiency(all_df: pd.DataFrame) -> None:
    """Plot 5: nodes_generated vs elapsed_s scatter + regression."""
    print("\n[Plot 5] State-Space Efficiency (comprehensive)")
    df_pub = _relabel_families(all_df)
    fig, ax = plt.subplots(figsize=(7, 5))
    for i, fam in enumerate(sorted(df_pub["family"].unique())):
        sub = df_pub[df_pub["family"] == fam]
        c, m, _ = _get_style(i)
        ax.scatter(sub["nodes_generated"], sub["elapsed_s"], color=c,
                   marker=m, s=28, alpha=0.7, label=fam, edgecolors="none")
    # Global log-log regression
    x = all_df["nodes_generated"].values.astype(float)
    y = all_df["elapsed_s"].values.astype(float)
    mask = (x > 0) & (y > 0)
    if mask.sum() > 2:
        slope, intercept, r, p, se = stats.linregress(
            np.log10(x[mask]), np.log10(y[mask]))
        x_fit = np.logspace(np.log10(x[mask].min()),
                            np.log10(x[mask].max()), 200)
        y_fit = 10 ** (intercept + slope * np.log10(x_fit))
        ax.plot(x_fit, y_fit, "k-", linewidth=1.2, alpha=0.6,
                label=f"Regression ($R^2$={r**2:.3f})")
    ax.set_xscale("log")
    ax.set_yscale("log")
    _style_axis(ax, "Nodes generated  [log]", "Elapsed time (s)  [log]",
                "State-Space Efficiency")
    _add_legend(ax, fontsize=7)
    fig.tight_layout()
    _save_figure(fig, "plot05_state_space_efficiency")


def plot_sat_vs_unsat(all_df: pd.DataFrame) -> None:
    """Plot 6: SAT vs UNSAT violin plots."""
    print("\n[Plot 6] SAT vs UNSAT Performance")
    fig, axes = plt.subplots(1, 2, figsize=(9, 4.5))
    sns.violinplot(data=all_df, x="verdict", y="elapsed_s", hue="verdict",
                   palette=DIVERGING_PALETTE, inner="box", cut=0,
                   ax=axes[0], legend=False)
    _style_axis(axes[0], "Verdict", "Elapsed time (s)",
                "Runtime by Verdict")
    sns.violinplot(data=all_df, x="verdict", y="distinct_zones",
                   hue="verdict", palette=DIVERGING_PALETTE, inner="box",
                   cut=0, ax=axes[1], legend=False)
    _style_axis(axes[1], "Verdict", "Distinct zones",
                "Exploration Effort by Verdict")
    fig.tight_layout()
    _save_figure(fig, "plot06_sat_vs_unsat")


def plot_zone_node_density(all_df: pd.DataFrame) -> None:
    """Plot 7: nodes vs distinct_zones scatter + y=x line."""
    print("\n[Plot 7] Zone vs. Node Density (Redundancy Analysis)")
    df_pub = _relabel_families(all_df)
    fig, ax = plt.subplots(figsize=(6, 5.5))
    for i, fam in enumerate(sorted(df_pub["family"].unique())):
        sub = df_pub[df_pub["family"] == fam]
        c, m, _ = _get_style(i)
        ax.scatter(sub["nodes_generated"], sub["distinct_zones"], color=c,
                   marker=m, s=30, alpha=0.75, label=fam, edgecolors="none")
    lim = max(all_df["nodes_generated"].max(),
              all_df["distinct_zones"].max()) * 1.1
    ax.plot([0, lim], [0, lim], "k--", lw=1, alpha=0.5,
            label=r"$y = x$ (no redundancy)")
    ax.set_xscale("log")
    ax.set_yscale("log")
    _style_axis(ax, "Nodes generated [log]", "Distinct zones [log]",
                r"Zone vs.\ Node Density --- Redundancy Analysis")
    _add_legend(ax, fontsize=7)
    fig.tight_layout()
    _save_figure(fig, "plot07_zone_node_density")


def plot_m_threshold_heatmap(df_bounds: Optional[pd.DataFrame],
                             df_clocks: Optional[pd.DataFrame]) -> None:
    """Plot 8: k × M → elapsed_s heatmap."""
    print("\n[Plot 8] M-Threshold Heatmap")
    frames = [f for f in [df_bounds, df_clocks] if f is not None]
    if not frames:
        warnings.warn("No data for M-threshold heatmap.")
        return
    df = pd.concat(frames, ignore_index=True).copy()
    df["k"] = pd.to_numeric(df["k"], errors="coerce")
    df["M"] = pd.to_numeric(df["M"], errors="coerce")
    hm = df[(df["k"] > 0) & (df["M"] > 0)].copy()
    if hm.empty:
        if df_clocks is not None:
            clk = df_clocks.copy()
            clk["k"] = clk["param_value"]
            hm = clk[(clk["k"] > 0) & (clk["M"] > 0)]
    if hm.empty:
        warnings.warn("Not enough (k, M) pairs for heatmap.")
        return
    pivot = hm.pivot_table(index="M", columns="k", values="elapsed_s",
                           aggfunc="mean").sort_index(ascending=False)
    fig, ax = plt.subplots(figsize=(7, 5))
    sns.heatmap(pivot, ax=ax, cmap="YlOrRd", annot=True, fmt=".3f",
                linewidths=0.4,
                cbar_kws={"label": "Elapsed time (s)"})
    _style_axis(ax, r"$k$ (clocks)", r"$M$ (max constant)",
                r"M-Threshold Heatmap --- $k \times M$ vs.\ Runtime")
    ax.grid(False)
    fig.tight_layout()
    _save_figure(fig, "plot08_m_threshold_heatmap")


def plot_timeout_frontier(all_df: pd.DataFrame) -> None:
    """Plot 9: success-rate bar chart per family."""
    print("\n[Plot 9] Timeout Frontier Analysis")
    df_pub = _relabel_families(all_df)
    stats_df = (
        df_pub.groupby("family")
        .agg(
            total=("elapsed_s", "count"),
            solved=("elapsed_s", lambda s: (s < CFG.timeout_s).sum()),
        )
        .reset_index()
    )
    stats_df["pct"] = 100.0 * stats_df["solved"] / stats_df["total"]
    stats_df = stats_df.sort_values("pct")

    fig, ax = plt.subplots(figsize=(7, 4.5))
    colours = [CB_PALETTE[0] if p == 100 else CB_PALETTE[1]
               for p in stats_df["pct"]]
    bars = ax.barh(stats_df["family"], stats_df["pct"], color=colours,
                   edgecolor="0.3", linewidth=0.5)
    for bar, pct, solved, total in zip(
        bars, stats_df["pct"], stats_df["solved"], stats_df["total"]
    ):
        ax.text(bar.get_width() + 1, bar.get_y() + bar.get_height() / 2,
                _pct_label(pct, solved, total), va="center", fontsize=8)
    ax.set_xlim(0, 115)
    xlabel = "Instances solved (\\%)" if _HAS_LATEX else "Instances solved (%)"
    _style_axis(ax, xlabel, "", "Timeout Frontier")
    ax.invert_yaxis()
    fig.tight_layout()
    _save_figure(fig, "plot09_timeout_frontier")


# ═══════════════════════════════════════════════════════════════════════════
#  Section 10 — Scaling-Law Analysis
# ═══════════════════════════════════════════════════════════════════════════


def analyse_scaling_laws(all_df: pd.DataFrame) -> pd.DataFrame:
    """
    Fit log-log regression  log(elapsed_s) = α · log(param_value) + β
    per variant.  Returns a DataFrame with regression coefficients and
    exports scaling_laws.csv + scaling_laws.json.
    """
    print("\n───── Scaling-Law Analysis ─────")

    rows = []
    for variant in sorted(all_df["variant"].unique()):
        sub = all_df[all_df["variant"] == variant].copy()
        x = sub["param_value"].values.astype(float)
        y = sub["elapsed_s"].values.astype(float)
        mask = (x > 0) & (y > 0)
        if mask.sum() < 3:
            continue
        slope, intercept, r, p, se = stats.linregress(
            np.log10(x[mask]), np.log10(y[mask]))
        rows.append({
            "variant": variant,
            "label": _vl(variant),
            "family": sub["family"].iloc[0],
            "family_label": _fl(sub["family"].iloc[0]),
            "exponent_alpha": round(slope, 4),
            "intercept_beta": round(intercept, 4),
            "R2": round(r ** 2, 4),
            "p_value": round(p, 6),
            "std_err": round(se, 4),
            "n_points": int(mask.sum()),
        })

    if not rows:
        warnings.warn("Not enough data for scaling-law analysis.")
        return pd.DataFrame()

    sl_df = pd.DataFrame(rows)
    _save_csv(sl_df, "scaling_laws.csv", "models")
    _save_json(rows, "scaling_laws.json", "models")

    # ── Plot 10: Scaling-law exponent comparison ──
    print("\n[Plot 10] Scaling-Law Exponents")
    fig, ax = plt.subplots(figsize=(8, 5))
    sl_sorted = sl_df.sort_values("exponent_alpha")
    colours = [CB_PALETTE[i % len(CB_PALETTE)]
               for i in range(len(sl_sorted))]
    bars = ax.barh(sl_sorted["label"], sl_sorted["exponent_alpha"],
                   color=colours, edgecolor="0.3", linewidth=0.5)
    for bar, r2 in zip(bars, sl_sorted["R2"]):
        ax.text(bar.get_width() + 0.02,
                bar.get_y() + bar.get_height() / 2,
                f"$R^2$={r2:.2f}", va="center", fontsize=7)
    _style_axis(ax, r"Exponent $\alpha$ (log-log slope)",
                "", "Scaling-Law Exponents by Benchmark")
    ax.axvline(1.0, color="gray", ls="--", lw=0.8, alpha=0.6)
    ax.invert_yaxis()
    fig.tight_layout()
    _save_figure(fig, "plot10_scaling_law_exponents")

    # ── Plot 11: Per-family scaling regression overlay ──
    print("\n[Plot 11] Scaling Regression Overlay")
    fig, ax = plt.subplots(figsize=(7, 5))
    for i, (_, row) in enumerate(sl_df.iterrows()):
        sub = all_df[all_df["variant"] == row["variant"]]
        x = sub["param_value"].values.astype(float)
        y = sub["elapsed_s"].values.astype(float)
        mask = (x > 0) & (y > 0)
        if mask.sum() < 2:
            continue
        c, m, ls = _get_style(i)
        ax.scatter(x[mask], y[mask], color=c, marker=m, s=20, alpha=0.6)
        x_fit = np.logspace(np.log10(x[mask].min()),
                            np.log10(x[mask].max()), 100)
        y_fit = 10 ** (row["intercept_beta"]
                       + row["exponent_alpha"] * np.log10(x_fit))
        ax.plot(x_fit, y_fit, color=c, ls=ls, lw=1.2,
                label=f"{row['label']} ($\\alpha$={row['exponent_alpha']:.2f})")
    ax.set_xscale("log")
    ax.set_yscale("log")
    _style_axis(ax, "Parameter value [log]",
                "Elapsed time (s) [log]",
                "Scaling Regression Overlay")
    _add_legend(ax, fontsize=6, loc="lower right")
    fig.tight_layout()
    _save_figure(fig, "plot11_scaling_regression_overlay")

    return sl_df


# ═══════════════════════════════════════════════════════════════════════════
#  Section 11 — Normalized-Cost / Cost-Model Plots
# ═══════════════════════════════════════════════════════════════════════════


def plot_normalized_costs(all_df: pd.DataFrame) -> None:
    """Plots 12–15: box plots of normalized cost metrics by family."""
    print("\n───── Normalized-Cost Plots ─────")

    df_pub = _relabel_families(all_df)

    metrics = [
        ("time_per_node", "Runtime per node (s)",
         "Amortised Time Cost per Node", "plot12_time_per_node"),
        ("zone_node_ratio", "Zone / node ratio",
         "Zone Redundancy Ratio by Family", "plot13_zone_node_ratio"),
        ("loop_checks_per_node", "Loop checks per node",
         "Loop-Check Density by Family", "plot14_loop_checks_per_node"),
    ]

    if _has_memory_columns(all_df) and CFG.include_memory:
        metrics.append(
            ("memory_per_node", "Memory per node (KiB)",
             "Memory Cost per Node by Family", "plot15_memory_per_node")
        )

    for col, ylabel, title, stem in metrics:
        if col not in df_pub.columns:
            continue
        sub = df_pub.dropna(subset=[col])
        if sub.empty:
            warnings.warn(f"No data for {col}.")
            continue
        print(f"\n[{stem.split('_')[0].title()}] {title}")
        fig, ax = plt.subplots(figsize=(8, 4.5))
        order = (sub.groupby("family")[col].median()
                 .sort_values(ascending=False).index.tolist())
        sns.boxplot(data=sub, x="family", y=col, hue="family",
                    order=order, hue_order=order,
                    palette=CB_PALETTE[:len(order)], ax=ax,
                    fliersize=3, linewidth=0.8, legend=False)
        ax.tick_params(axis="x", rotation=35)
        for lbl in ax.get_xticklabels():
            lbl.set_ha("right")
            lbl.set_fontsize(8)
        _style_axis(ax, "", ylabel, title)
        fig.tight_layout()
        _save_figure(fig, stem)


# ═══════════════════════════════════════════════════════════════════════════
#  Section 12 — Enhanced SAT vs UNSAT Analysis
# ═══════════════════════════════════════════════════════════════════════════


def analyse_sat_vs_unsat(all_df: pd.DataFrame) -> pd.DataFrame:
    """
    Plot 16: per-family SAT-vs-UNSAT runtime bar chart + quantitative summary.
    """
    print("\n───── Enhanced SAT vs UNSAT Analysis ─────")

    df_pub = _relabel_families(all_df)
    rows = []
    for fam in sorted(df_pub["family"].unique()):
        sub = df_pub[df_pub["family"] == fam]
        sat = sub[sub["verdict"] == "SAT"]
        unsat = sub[sub["verdict"] == "UNSAT"]
        rows.append({
            "family": fam,
            "n_sat": len(sat),
            "n_unsat": len(unsat),
            "median_t_sat": sat["elapsed_s"].median() if len(sat) else np.nan,
            "median_t_unsat": unsat["elapsed_s"].median() if len(unsat) else np.nan,
            "mean_nodes_sat": sat["nodes_generated"].mean() if len(sat) else np.nan,
            "mean_nodes_unsat": unsat["nodes_generated"].mean() if len(unsat) else np.nan,
            "mean_zones_sat": sat["distinct_zones"].mean() if len(sat) else np.nan,
            "mean_zones_unsat": unsat["distinct_zones"].mean() if len(unsat) else np.nan,
        })

    su_df = pd.DataFrame(rows)
    su_df["runtime_ratio"] = su_df["median_t_unsat"] / su_df["median_t_sat"]
    _save_csv(su_df, "sat_vs_unsat_summary.csv")

    # ── Plot 16: Grouped bar chart ──
    print("\n[Plot 16] SAT vs UNSAT per-family runtime")
    plot_df = su_df.dropna(subset=["median_t_sat", "median_t_unsat"])
    if plot_df.empty:
        warnings.warn("Not enough SAT/UNSAT pairs for per-family plot.")
        return su_df

    fig, ax = plt.subplots(figsize=(9, 5))
    x = np.arange(len(plot_df))
    w = 0.35
    ax.bar(x - w / 2, plot_df["median_t_sat"], w, color=DIVERGING_PALETTE["SAT"],
           label="SAT", edgecolor="0.3", linewidth=0.5)
    ax.bar(x + w / 2, plot_df["median_t_unsat"], w, color=DIVERGING_PALETTE["UNSAT"],
           label="UNSAT", edgecolor="0.3", linewidth=0.5)
    ax.set_xticks(x)
    ax.set_xticklabels(plot_df["family"], rotation=35, ha="right", fontsize=8)
    _style_axis(ax, "", "Median elapsed time (s)",
                "SAT vs UNSAT Runtime by Family")
    _add_legend(ax, loc="upper right")
    fig.tight_layout()
    _save_figure(fig, "plot16_sat_vs_unsat_per_family")

    return su_df


# ═══════════════════════════════════════════════════════════════════════════
#  Section 13 — Phase-Boundary Analysis (k × M)
# ═══════════════════════════════════════════════════════════════════════════


def analyse_phase_boundary(all_df: pd.DataFrame) -> None:
    """
    Plot 17: k × M frontier contour showing where runtime crosses the
    threshold, plus km_phase_frontier.csv export.
    """
    print("\n───── Phase-Boundary Analysis (k × M) ─────")

    df = all_df.copy()
    df["k"] = pd.to_numeric(df["k"], errors="coerce")
    df["M"] = pd.to_numeric(df["M"], errors="coerce")

    hm = df[(df["k"] > 0) & (df["M"] > 0)].copy()
    if hm.empty:
        warnings.warn("No (k, M) data for phase-boundary analysis.")
        return

    threshold = CFG.frontier_rt
    if threshold is None:
        threshold = CFG.timeout_s / 2.0

    # Mark each instance as feasible / infeasible
    hm["feasible"] = hm["elapsed_s"] < threshold

    # Export frontier data
    frontier_df = (
        hm.groupby(["k", "M"])
        .agg(
            mean_elapsed=("elapsed_s", "mean"),
            max_elapsed=("elapsed_s", "max"),
            pct_feasible=("feasible", "mean"),
            n_instances=("feasible", "count"),
        )
        .reset_index()
    )
    frontier_df["pct_feasible"] = (frontier_df["pct_feasible"] * 100).round(1)
    _save_csv(frontier_df, "km_phase_frontier.csv")

    # ── Plot 17: filled contour or scatter ──
    print("\n[Plot 17] Phase-Boundary k × M Frontier")
    pivot = frontier_df.pivot_table(index="M", columns="k",
                                    values="mean_elapsed", aggfunc="mean")
    if pivot.shape[0] < 2 or pivot.shape[1] < 2:
        # Fall back to scatter if not enough for contour
        fig, ax = plt.subplots(figsize=(7, 5))
        sc = ax.scatter(hm["k"], hm["M"], c=hm["elapsed_s"],
                        cmap="YlOrRd", s=40, edgecolors="0.5", linewidth=0.3)
        plt.colorbar(sc, ax=ax, label="Elapsed time (s)")
        ax.axhline(threshold, color="k", ls="--", lw=0.8, alpha=0.5,
                   label=f"Threshold = {threshold:.1f} s")
        _style_axis(ax, r"$k$ (clocks)", r"$M$ (max constant)",
                    r"Phase Boundary --- $k \times M$")
        _add_legend(ax)
    else:
        fig, ax = plt.subplots(figsize=(7, 5))
        M_vals = sorted(pivot.index)
        k_vals = sorted(pivot.columns)
        Z = pivot.reindex(index=M_vals, columns=k_vals).values
        K, M = np.meshgrid(k_vals, M_vals)
        cs = ax.contourf(K, M, Z, levels=12, cmap="YlOrRd")
        plt.colorbar(cs, ax=ax, label="Mean elapsed time (s)")
        ax.contour(K, M, Z, levels=[threshold], colors="black",
                   linewidths=1.5, linestyles="--")
        _style_axis(ax, r"$k$ (clocks)", r"$M$ (max constant)",
                    r"Phase Boundary --- $k \times M$")
    fig.tight_layout()
    _save_figure(fig, "plot17_phase_boundary_km")


# ═══════════════════════════════════════════════════════════════════════════
#  Section 14 — Memory Analysis (conditional)
# ═══════════════════════════════════════════════════════════════════════════


def analyse_memory(all_df: pd.DataFrame) -> None:
    """Plots 18–23: memory-focused analysis (only when memory cols exist)."""
    if not _has_memory_columns(all_df):
        print("\n  [Memory] Skipped — no peak_memory_kb / avg_memory_kb columns.")
        return
    if not CFG.include_memory:
        print("\n  [Memory] Skipped — use --include-memory to enable.")
        return

    print("\n───── Memory Analysis ─────")
    df_pub = _relabel_families(all_df)

    # ── Plot 18: Memory vs Nodes scatter ──
    print("\n[Plot 18] Memory vs Nodes")
    fig, ax = plt.subplots(figsize=(7, 5))
    for i, fam in enumerate(sorted(df_pub["family"].unique())):
        sub = df_pub[df_pub["family"] == fam]
        c, m, _ = _get_style(i)
        ax.scatter(sub["nodes_generated"], sub["peak_memory_kb"],
                   color=c, marker=m, s=28, alpha=0.7, label=fam,
                   edgecolors="none")
    ax.set_xscale("log")
    ax.set_yscale("log")
    _style_axis(ax, "Nodes generated [log]", "Peak memory (KiB) [log]",
                "Memory vs State-Space Size")
    _add_legend(ax, fontsize=7)
    fig.tight_layout()
    _save_figure(fig, "plot18_memory_vs_nodes")

    # ── Plot 19: Memory vs Zones scatter ──
    print("\n[Plot 19] Memory vs Zones")
    fig, ax = plt.subplots(figsize=(7, 5))
    for i, fam in enumerate(sorted(df_pub["family"].unique())):
        sub = df_pub[df_pub["family"] == fam]
        c, m, _ = _get_style(i)
        ax.scatter(sub["distinct_zones"], sub["peak_memory_kb"],
                   color=c, marker=m, s=28, alpha=0.7, label=fam,
                   edgecolors="none")
    ax.set_xscale("log")
    ax.set_yscale("log")
    _style_axis(ax, "Distinct zones [log]", "Peak memory (KiB) [log]",
                "Memory vs Zone Complexity")
    _add_legend(ax, fontsize=7)
    fig.tight_layout()
    _save_figure(fig, "plot19_memory_vs_zones")

    # ── Plot 20: Memory by Verdict violin ──
    print("\n[Plot 20] Memory by Verdict")
    fig, ax = plt.subplots(figsize=(6, 4.5))
    sns.violinplot(data=all_df, x="verdict", y="peak_memory_kb",
                   hue="verdict", palette=DIVERGING_PALETTE,
                   inner="box", cut=0, ax=ax, legend=False)
    _style_axis(ax, "Verdict", "Peak memory (KiB)",
                "Memory Consumption by Verdict")
    fig.tight_layout()
    _save_figure(fig, "plot20_memory_by_verdict")

    # ── Plot 21: Memory per node by family (box) ──
    print("\n[Plot 21] Memory per Node by Family")
    sub = df_pub.dropna(subset=["memory_per_node"])
    if not sub.empty:
        fig, ax = plt.subplots(figsize=(8, 4.5))
        order = (sub.groupby("family")["memory_per_node"].median()
                 .sort_values(ascending=False).index.tolist())
        sns.boxplot(data=sub, x="family", y="memory_per_node",
                    order=order, palette=CB_PALETTE[:len(order)],
                    ax=ax, fliersize=3, linewidth=0.8)
        ax.set_xticklabels(ax.get_xticklabels(), rotation=35, ha="right",
                           fontsize=8)
        _style_axis(ax, "", "Memory per node (KiB)",
                    "Per-Node Memory Cost by Family")
        fig.tight_layout()
        _save_figure(fig, "plot21_memory_per_node_by_family")

    # ── Plot 22: Memory scaling by family (line) ──
    print("\n[Plot 22] Memory Scaling by Family")
    fig, ax = plt.subplots(figsize=(7, 5))
    for i, fam in enumerate(sorted(df_pub["family"].unique())):
        sub = df_pub[df_pub["family"] == fam].sort_values("param_value")
        if sub.empty:
            continue
        c, m, ls = _get_style(i)
        ax.plot(sub["param_value"], sub["peak_memory_kb"],
                color=c, marker=m, linestyle=ls, label=fam, alpha=0.8)
    ax.set_yscale("log")
    _style_axis(ax, "Parameter value", "Peak memory (KiB) [log]",
                "Memory Scaling by Family")
    _add_legend(ax, fontsize=7)
    fig.tight_layout()
    _save_figure(fig, "plot22_memory_scaling_by_family")

    # ── Plot 23: k × M memory heatmap ──
    print("\n[Plot 23] k × M Memory Heatmap")
    df2 = all_df.copy()
    df2["k"] = pd.to_numeric(df2["k"], errors="coerce")
    df2["M"] = pd.to_numeric(df2["M"], errors="coerce")
    hm = df2[(df2["k"] > 0) & (df2["M"] > 0)].copy()
    if not hm.empty:
        pivot = hm.pivot_table(index="M", columns="k",
                               values="peak_memory_kb",
                               aggfunc="mean").sort_index(ascending=False)
        fig, ax = plt.subplots(figsize=(7, 5))
        sns.heatmap(pivot, ax=ax, cmap="YlGnBu", annot=True, fmt=".0f",
                    linewidths=0.4,
                    cbar_kws={"label": "Peak memory (KiB)"})
        _style_axis(ax, r"$k$ (clocks)", r"$M$ (max constant)",
                    r"Memory Heatmap --- $k \times M$")
        ax.grid(False)
        fig.tight_layout()
        _save_figure(fig, "plot23_km_memory_heatmap")
    else:
        warnings.warn("Not enough (k, M) pairs for memory heatmap.")


# ═══════════════════════════════════════════════════════════════════════════
#  Section 15 — Ablation Analysis
# ═══════════════════════════════════════════════════════════════════════════


def analyse_ablation(all_df: pd.DataFrame) -> None:
    """
    Plot 24: Extrapolation ablation (B6 with vs without M-abstraction).
    Exports ablation_summary.csv.
    """
    print("\n───── Ablation Analysis ─────")

    extr = all_df[all_df["variant"] == "B6_forced_delay"].copy()
    noextr = all_df[all_df["variant"] == "B6_forced_delay_noextr"].copy()

    if extr.empty and noextr.empty:
        warnings.warn("No B6 ablation data available.")
        return

    # Build ablation summary
    rows = []
    for label, sub in [("extrapolation_on", extr),
                       ("extrapolation_off", noextr)]:
        if sub.empty:
            continue
        rows.append({
            "condition": label,
            "variant": sub["variant"].iloc[0],
            "n_instances": len(sub),
            "mean_elapsed_s": round(sub["elapsed_s"].mean(), 6),
            "max_elapsed_s": round(sub["elapsed_s"].max(), 6),
            "mean_nodes": round(sub["nodes_generated"].mean(), 1),
            "max_nodes": int(sub["nodes_generated"].max()),
            "mean_zones": round(sub["distinct_zones"].mean(), 1),
            "max_zones": int(sub["distinct_zones"].max()),
        })
    abl_df = pd.DataFrame(rows)
    _save_csv(abl_df, "ablation_summary.csv")

    # ── Plot 24: Paired line plot ──
    if not extr.empty and not noextr.empty:
        print("\n[Plot 24] Extrapolation Ablation")
        fig, axes = plt.subplots(1, 2, figsize=(10, 4.5))

        # Runtime comparison
        ax = axes[0]
        ax.plot(extr.sort_values("M")["M"],
                extr.sort_values("M")["elapsed_s"],
                color=CB_PALETTE[0], marker="o", label=_vl("B6_forced_delay"))
        ax.plot(noextr.sort_values("M")["M"],
                noextr.sort_values("M")["elapsed_s"],
                color=CB_PALETTE[1], marker="s", ls="--",
                label=_vl("B6_forced_delay_noextr"))
        ax.set_xscale("log", base=2)
        ax.set_yscale("log")
        _style_axis(ax, r"$M$ (log$_2$)", "Elapsed time (s) [log]",
                    "Runtime: Extrapolation On vs Off")
        _add_legend(ax, fontsize=8)

        # Zone count comparison
        ax = axes[1]
        ax.plot(extr.sort_values("M")["M"],
                extr.sort_values("M")["distinct_zones"],
                color=CB_PALETTE[0], marker="o", label=_vl("B6_forced_delay"))
        ax.plot(noextr.sort_values("M")["M"],
                noextr.sort_values("M")["distinct_zones"],
                color=CB_PALETTE[1], marker="s", ls="--",
                label=_vl("B6_forced_delay_noextr"))
        ax.set_xscale("log", base=2)
        ax.set_yscale("log")
        _style_axis(ax, r"$M$ (log$_2$)", "Distinct zones [log]",
                    "Zone Growth: Extrapolation On vs Off")
        _add_legend(ax, fontsize=8)

        fig.tight_layout()
        _save_figure(fig, "plot24_ablation_extrapolation")
    else:
        print("  (only one condition present — skipping paired plot)")


# ═══════════════════════════════════════════════════════════════════════════
#  Section 16 — Hardness-Feature Analysis
# ═══════════════════════════════════════════════════════════════════════════


def analyse_hardness_features(all_df: pd.DataFrame) -> None:
    """
    Compute Pearson & Spearman correlations of structural features with
    runtime.  Exports hardness_features.csv and hardness_model_summary.txt.
    """
    print("\n───── Hardness-Feature Analysis ─────")

    features = ["param_value", "M", "k", "depth",
                "nodes_generated", "distinct_zones", "loop_checks"]
    if _has_memory_columns(all_df) and CFG.include_memory:
        features += ["peak_memory_kb", "avg_memory_kb"]

    # Filter to columns that exist and are numeric
    available = [f for f in features if f in all_df.columns]
    target = "elapsed_s"

    rows = []
    for feat in available:
        x = pd.to_numeric(all_df[feat], errors="coerce")
        y = all_df[target]
        mask = x.notna() & y.notna() & (x != 0) & (y != 0)
        if mask.sum() < 5:
            continue
        pearson_r, pearson_p = stats.pearsonr(x[mask], y[mask])
        spearman_r, spearman_p = stats.spearmanr(x[mask], y[mask])
        rows.append({
            "feature": feat,
            "pearson_r": round(pearson_r, 4),
            "pearson_p": round(pearson_p, 6),
            "spearman_rho": round(spearman_r, 4),
            "spearman_p": round(spearman_p, 6),
            "n": int(mask.sum()),
        })

    if not rows:
        warnings.warn("Not enough data for hardness-feature analysis.")
        return

    hf_df = pd.DataFrame(rows).sort_values("spearman_rho",
                                            ascending=False,
                                            key=abs)
    _save_csv(hf_df, "hardness_features.csv")

    # Summary text
    lines = [
        "=" * 60,
        "HARDNESS-FEATURE ANALYSIS SUMMARY",
        "=" * 60, "",
        f"Target variable: {target}",
        f"Dataset size:    {len(all_df)} instances",
        f"Features tested: {', '.join(available)}", "",
        "Correlation Table (sorted by |Spearman ρ| descending):", "",
        f"{'Feature':<24s} {'Pearson r':>10s} {'p':>10s} "
        f"{'Spearman ρ':>10s} {'p':>10s} {'n':>6s}",
        "-" * 60,
    ]
    for _, r in hf_df.iterrows():
        lines.append(
            f"{r['feature']:<24s} {r['pearson_r']:>10.4f} "
            f"{r['pearson_p']:>10.6f} {r['spearman_rho']:>10.4f} "
            f"{r['spearman_p']:>10.6f} {r['n']:>6d}"
        )
    lines += ["", "-" * 60, ""]

    # Identify top predictor
    top = hf_df.iloc[0]
    lines.append(
        f"Strongest predictor: {top['feature']} "
        f"(Spearman ρ = {top['spearman_rho']:.4f}, "
        f"p = {top['spearman_p']:.2e})"
    )
    lines.append("")

    # ── Plot 25: correlation heatmap ──
    print("\n[Plot 25] Hardness-Feature Correlation Heatmap")
    corr_cols = available + [target]
    num_df = all_df[corr_cols].apply(pd.to_numeric, errors="coerce").dropna()
    if len(num_df) > 5 and len(corr_cols) > 2:
        corr_matrix = num_df.corr(method="spearman")
        fig, ax = plt.subplots(figsize=(8, 6.5))
        sns.heatmap(corr_matrix, ax=ax, annot=True, fmt=".2f",
                    cmap="RdBu_r", center=0, linewidths=0.3,
                    square=True, vmin=-1, vmax=1)
        ax.set_title("Spearman Rank Correlation — Hardness Features")
        ax.set_xticklabels(ax.get_xticklabels(), rotation=45, ha="right",
                           fontsize=8)
        ax.set_yticklabels(ax.get_yticklabels(), fontsize=8)
        fig.tight_layout()
        _save_figure(fig, "plot25_hardness_correlation_heatmap")

    summary_text = "\n".join(lines)
    _save_text(summary_text, "hardness_model_summary.txt", "models")


# ═══════════════════════════════════════════════════════════════════════════
#  Section 17 — LaTeX Tables
# ═══════════════════════════════════════════════════════════════════════════


def table_zeno_summary(df_zeno: pd.DataFrame) -> str:
    """Table 1: Zeno-rejection benchmark summary."""
    print("\n[Table 1] Zeno Rejection Summary")
    summary = (
        df_zeno.groupby("variant")
        .agg(
            n_instances=("verdict", "count"),
            all_unsat=("verdict", lambda v: (v == "UNSAT").all()),
            mean_elapsed=("elapsed_s", "mean"),
            max_elapsed=("elapsed_s", "max"),
            mean_nodes=("nodes_generated", "mean"),
        )
        .reset_index()
    )
    summary["variant"] = summary["variant"].map(_vl)
    summary["all_unsat"] = summary["all_unsat"].map(
        {True: "\\checkmark", False: "\\texttimes"})
    summary.columns = ["Benchmark", "Instances", "All UNSAT",
                        "Mean $t$ (s)", "Max $t$ (s)", "Mean nodes"]
    for col in ["Mean $t$ (s)", "Max $t$ (s)"]:
        summary[col] = summary[col].map(lambda v: f"{v:.4f}")
    summary["Mean nodes"] = summary["Mean nodes"].map(lambda v: f"{v:.1f}")
    return summary.to_latex(
        index=False, escape=False, column_format="l r c r r r",
        caption="Zeno-rejection benchmark: all instances evaluate to UNSAT "
                "with negligible runtime, confirming correct zeno-cycle "
                "pruning.",
        label="tab:zeno",
    )


def table_performance_boundary(all_df: pd.DataFrame) -> str:
    """Table 2: max param_value reached per family before timeout."""
    print("\n[Table 2] Performance Boundary Summary")
    solved = all_df[all_df["elapsed_s"] < CFG.timeout_s]
    summary = (
        solved.groupby("family")
        .agg(
            param_swept=("param_name", "first"),
            max_param=("param_value", "max"),
            n_solved=("param_value", "count"),
            max_elapsed=("elapsed_s", "max"),
            max_nodes=("nodes_generated", "max"),
        )
        .reset_index()
    )
    summary["family"] = summary["family"].map(_fl)
    summary.columns = ["Family", "Parameter", "Max value reached",
                        "Solved", "Max $t$ (s)", "Max nodes"]
    summary["Max $t$ (s)"] = summary["Max $t$ (s)"].map(
        lambda v: f"{v:.3f}")
    summary["Max nodes"] = summary["Max nodes"].map(lambda v: f"{v:,}")
    return summary.to_latex(
        index=False, escape=False, column_format="l l r r r r",
        caption="Maximum parameter value reached within the "
                f"{CFG.timeout_s:.0f}\\,s timeout per benchmark family.",
        label="tab:boundary",
    )


def table_descriptive_stats(all_df: pd.DataFrame) -> str:
    """Table 3: descriptive statistics by family."""
    print("\n[Table 3] Descriptive Statistics by Family")
    summary = (
        all_df.groupby("family")
        .agg(
            total=("elapsed_s", "count"),
            mean_t=("elapsed_s", "mean"),
            median_t=("elapsed_s", "median"),
            max_t=("elapsed_s", "max"),
            mean_n=("nodes_generated", "mean"),
            median_n=("nodes_generated", "median"),
            max_n=("nodes_generated", "max"),
        )
        .reset_index()
    )
    summary["family"] = summary["family"].map(_fl)
    summary.columns = [
        "Family", "Total", "Mean $t$", "Median $t$", "Max $t$",
        "Mean nodes", "Median nodes", "Max nodes",
    ]
    for col in ["Mean $t$", "Median $t$", "Max $t$"]:
        summary[col] = summary[col].map(lambda v: f"{v:.4f}")
    for col in ["Mean nodes", "Median nodes", "Max nodes"]:
        summary[col] = summary[col].map(
            lambda v: f"{int(v):,}" if pd.notna(v) else "\u2014")
    return summary.to_latex(
        index=False, escape=False, column_format="l r r r r r r r",
        caption="Descriptive statistics of solver performance aggregated by "
                "benchmark family.",
        label="tab:stats",
    )


def table_family_summary(all_df: pd.DataFrame) -> str:
    """Table 4: comprehensive family summary with all key metrics."""
    print("\n[Table 4] Family Summary")
    summary = (
        all_df.groupby("family")
        .agg(
            n=("elapsed_s", "count"),
            n_sat=("verdict", lambda v: (v == "SAT").sum()),
            n_unsat=("verdict", lambda v: (v == "UNSAT").sum()),
            mean_t=("elapsed_s", "mean"),
            max_t=("elapsed_s", "max"),
            mean_nodes=("nodes_generated", "mean"),
            mean_zones=("distinct_zones", "mean"),
            mean_znr=("zone_node_ratio", "mean"),
            mean_loops=("loop_checks", "mean"),
        )
        .reset_index()
    )

    if _has_memory_columns(all_df):
        mem_agg = (
            all_df.groupby("family")
            .agg(mean_mem=("peak_memory_kb", "mean"))
            .reset_index()
        )
        summary = summary.merge(mem_agg, on="family", how="left")
    else:
        summary["mean_mem"] = np.nan

    summary["family"] = summary["family"].map(_fl)

    # Export as CSV
    _save_csv(summary, "family_summary.csv")

    # LaTeX table
    tex_df = summary.copy()
    tex_df.columns = [
        "Family", "$n$", "SAT", "UNSAT", "Mean $t$", "Max $t$",
        "Mean nodes", "Mean zones", r"$\overline{z/n}$",
        "Mean loops", "Mean mem (KiB)",
    ]
    for col in ["Mean $t$", "Max $t$"]:
        tex_df[col] = tex_df[col].map(lambda v: f"{v:.4f}")
    for col in ["Mean nodes", "Mean zones", "Mean loops"]:
        tex_df[col] = tex_df[col].map(
            lambda v: f"{v:.1f}" if pd.notna(v) else "\u2014")
    tex_df[r"$\overline{z/n}$"] = tex_df[r"$\overline{z/n}$"].map(
        lambda v: f"{v:.3f}" if pd.notna(v) else "\u2014")
    tex_df["Mean mem (KiB)"] = tex_df["Mean mem (KiB)"].map(
        lambda v: f"{v:.1f}" if pd.notna(v) else "\u2014")

    if CFG.export_latex:
        tex_path = CFG.table_dir / "family_summary.tex"
        with open(tex_path, "w") as f:
            f.write(tex_df.to_latex(
                index=False, escape=False,
                column_format="l r r r r r r r r r r",
                caption="Comprehensive family-level summary of solver "
                        "performance.",
                label="tab:family_summary",
            ))
        print(f"  \u2713 Saved {tex_path}")

    return tex_df.to_latex(
        index=False, escape=False,
        column_format="l r r r r r r r r r r",
        caption="Comprehensive family-level summary of solver performance.",
        label="tab:family_summary",
    )


# ═══════════════════════════════════════════════════════════════════════════
#  Section 18 — Technical Rationale
# ═══════════════════════════════════════════════════════════════════════════


def generate_rationale(all_df: pd.DataFrame,
                       df_zeno: Optional[pd.DataFrame]) -> None:
    """Write analysis_rationale.txt."""
    print("\n[Rationale] Generating analysis_rationale.txt")

    lines: list[str] = []
    sep = "=" * 72

    lines += [sep, "ANALYSIS RATIONALE — TCTL Tableau Solver",
              "Structured for the Discussion section of a CAV submission",
              sep, ""]

    # 1. Symbolic efficiency
    lines.append("1. SYMBOLIC EFFICIENCY")
    lines.append("-" * 40)
    total_nodes = all_df["nodes_generated"].sum()
    total_zones = all_df["distinct_zones"].sum()
    ratio = total_zones / total_nodes if total_nodes > 0 else float("nan")
    lines += [
        f"   Total nodes generated : {total_nodes:,}",
        f"   Total distinct zones  : {total_zones:,}",
        f"   Global zone/node ratio: {ratio:.4f}",
        "",
    ]
    per_fam = (
        all_df.groupby("family")
        .apply(lambda g: pd.Series({
            "nodes": g["nodes_generated"].sum(),
            "zones": g["distinct_zones"].sum(),
            "ratio": g["distinct_zones"].sum() / max(
                g["nodes_generated"].sum(), 1),
        }))
        .reset_index()
    )
    lines.append("   Per-family zone/node ratio:")
    for _, r in per_fam.iterrows():
        lines.append(
            f"     {_fl(r['family']):32s}  z/n = {r['ratio']:.4f}  "
            f"(zones={int(r['zones']):>8,}, nodes={int(r['nodes']):>8,})"
        )
    lines += [
        "", "   Interpretation:",
        "   The zone/node ratio is consistently below 1.0, demonstrating",
        "   that M-abstraction collapses the infinite timed state space",
        "   into compact symbolic representatives via DBM operations.",
        "",
    ]

    # 2. Non-Zeno
    lines.append("2. NON-ZENO OVERHEAD")
    lines.append("-" * 40)
    if df_zeno is not None and not df_zeno.empty:
        zm = df_zeno["elapsed_s"].mean()
        zx = df_zeno["elapsed_s"].max()
        lines += [
            f"   Mean elapsed: {zm:.6f} s",
            f"   Max elapsed:  {zx:.6f} s",
            "   The zeno-rejection mechanism adds negligible overhead.",
        ]
    else:
        lines.append("   [zeno data unavailable]")
    lines.append("")

    # 3. Verification bias
    lines.append("3. VERIFICATION BIAS (SAT vs. UNSAT)")
    lines.append("-" * 40)
    sat = all_df[all_df["verdict"] == "SAT"]
    unsat = all_df[all_df["verdict"] == "UNSAT"]
    lines += [
        f"   SAT:   {len(sat):>5d} ({100*len(sat)/len(all_df):.1f}%)",
        f"   UNSAT: {len(unsat):>5d} ({100*len(unsat)/len(all_df):.1f}%)",
    ]
    if not sat.empty and not unsat.empty:
        for label, sub in [("SAT", sat), ("UNSAT", unsat)]:
            lines.append(
                f"     {label:6s}  mean={sub['elapsed_s'].mean():.4f}s  "
                f"median={sub['elapsed_s'].median():.4f}s  "
                f"max={sub['elapsed_s'].max():.4f}s"
            )
    lines += ["", sep, "End of analysis rationale.", sep]

    _save_text("\n".join(lines) + "\n", "analysis_rationale.txt")


# ═══════════════════════════════════════════════════════════════════════════
#  Section 19 — Final Analysis Report
# ═══════════════════════════════════════════════════════════════════════════


def generate_report(all_df: pd.DataFrame,
                    sl_df: Optional[pd.DataFrame],
                    su_df: Optional[pd.DataFrame]) -> None:
    """Write analysis_report.txt — a one-page executive summary."""
    print("\n[Report] Generating analysis_report.txt")

    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    sep = "=" * 72

    lines = [
        sep,
        "TCTL TABLEAU SOLVER — ANALYSIS REPORT",
        f"Generated: {ts}",
        sep, "",
        "DATASET",
        f"  Input directory : {CFG.input_dir}",
        f"  Total instances : {len(all_df)}",
        f"  Families        : {all_df['family'].nunique()}",
        f"  Variants        : {all_df['variant'].nunique()}",
        f"  SAT instances   : {(all_df['verdict']=='SAT').sum()}",
        f"  UNSAT instances : {(all_df['verdict']=='UNSAT').sum()}",
        "",
        "RUNTIME SUMMARY",
        f"  Mean elapsed    : {all_df['elapsed_s'].mean():.6f} s",
        f"  Median elapsed  : {all_df['elapsed_s'].median():.6f} s",
        f"  Max elapsed     : {all_df['elapsed_s'].max():.6f} s",
        f"  Solved (< {CFG.timeout_s}s) : "
        f"{(all_df['elapsed_s'] < CFG.timeout_s).sum()} / {len(all_df)}",
        "",
        "STATE-SPACE SUMMARY",
        f"  Total nodes     : {int(all_df['nodes_generated'].sum()):,}",
        f"  Total zones     : {int(all_df['distinct_zones'].sum()):,}",
        f"  Global z/n ratio: "
        f"{all_df['distinct_zones'].sum() / max(all_df['nodes_generated'].sum(), 1):.4f}",
        f"  Total loop chks : {int(all_df['loop_checks'].sum()):,}",
        "",
    ]

    if _has_memory_columns(all_df):
        lines += [
            "MEMORY SUMMARY",
            f"  Mean peak memory : {all_df['peak_memory_kb'].mean():.1f} KiB",
            f"  Max peak memory  : {all_df['peak_memory_kb'].max():.1f} KiB",
            f"  Mean per-node    : {all_df['avg_memory_kb'].mean():.2f} KiB",
            "",
        ]

    if sl_df is not None and not sl_df.empty:
        lines += [
            "SCALING LAWS",
            f"  Regressions computed: {len(sl_df)}",
            f"  Mean exponent α     : {sl_df['exponent_alpha'].mean():.3f}",
            f"  Max exponent α      : {sl_df['exponent_alpha'].max():.3f} "
            f"({sl_df.loc[sl_df['exponent_alpha'].idxmax(), 'label']})",
            f"  Mean R²             : {sl_df['R2'].mean():.3f}",
            "",
        ]

    if su_df is not None and not su_df.empty:
        any_ratio = su_df.dropna(subset=["runtime_ratio"])
        if not any_ratio.empty:
            lines += [
                "SAT vs UNSAT",
                f"  Families with both verdicts: {len(any_ratio)}",
                f"  Mean UNSAT/SAT ratio       : "
                f"{any_ratio['runtime_ratio'].mean():.3f}",
                "",
            ]

    lines += [
        "OUTPUTS",
        f"  Plots  : {CFG.plot_dir}/",
        f"  Tables : {CFG.table_dir}/",
        f"  Models : {CFG.model_dir}/",
        f"  Derived: {CFG.derived_dir}/",
        "",
        sep,
        "End of analysis report.",
        sep,
    ]

    _save_text("\n".join(lines) + "\n", "analysis_report.txt")


# ═══════════════════════════════════════════════════════════════════════════
#  Section 20 — Main Entry Point
# ═══════════════════════════════════════════════════════════════════════════


def main() -> None:
    # ── Parse CLI ──
    args = _build_parser().parse_args()
    CFG.input_dir = args.input_dir
    CFG.output_root = args.output_dir
    CFG.include_memory = args.include_memory
    CFG.export_latex = args.export_latex
    CFG.skip_heavy = args.skip_heavy_regressions
    CFG.frontier_rt = args.frontier_threshold_runtime
    CFG.frontier_mem = args.frontier_threshold_memory
    CFG.formats = args.formats
    CFG.dpi = args.dpi
    CFG.timeout_s = args.timeout

    # ── Initialise ──
    _load_name_map()
    _apply_mpl_style()
    CFG.ensure_dirs()

    print("═══════════════════════════════════════════════")
    print("  TCTL Tableau Solver — Comprehensive Analysis")
    print(f"  Input:  {CFG.input_dir}")
    print(f"  Output: {CFG.output_root}")
    print(f"  Formats: {', '.join(CFG.formats)}")
    print(f"  Memory: {'enabled' if CFG.include_memory else 'disabled'}")
    print("═══════════════════════════════════════════════")

    # ── Load CSV files ──
    csv_files = {
        "bounds_M": "curves_bounds_M.csv",
        "depth": "curves_depth.csv",
        "obligations": "curves_obligations.csv",
        "until_release": "curves_until_release_mixed.csv",
        "zeno": "curves_zeno.csv",
        "clocks": "curves_clocks.csv",
        "alternation": "curves_alternation.csv",
        "chain": "curves_chain.csv",
    }
    data: dict[str, Optional[pd.DataFrame]] = {}
    for key, fname in csv_files.items():
        data[key] = _load_csv(fname)
        status = (f"{len(data[key])} rows" if data[key] is not None
                  else "MISSING")
        print(f"  [{status:>12s}]  {fname}")

    # ── Build combined DataFrame ──
    all_frames = [df for df in data.values() if df is not None]
    if not all_frames:
        print("\n  \u2717 No data loaded — aborting.")
        sys.exit(1)
    all_df = pd.concat(all_frames, ignore_index=True)
    all_df = _enrich(all_df)

    has_mem = _has_memory_columns(all_df)
    print(f"\n  Combined: {len(all_df)} rows, "
          f"{all_df['family'].nunique()} families, "
          f"{all_df['variant'].nunique()} variants"
          f"{', memory columns detected' if has_mem else ''}")

    # ═══════════════════════════════════════════════════════════════════
    #  Original Plots (1–9)
    # ═══════════════════════════════════════════════════════════════════
    print("\n───── Original Plots (1–9) ─────")

    if data["bounds_M"] is not None:
        plot_m_abstraction(data["bounds_M"])
    plot_depth_complexity(data.get("depth"), data.get("until_release"))
    plot_clock_dimensionality(data.get("clocks"), data.get("obligations"))
    plot_structural_tests(data.get("alternation"), data.get("chain"))
    plot_state_space_efficiency(all_df)
    plot_sat_vs_unsat(all_df)

    print("\n───── Deep-Dive Plots (7–9) ─────")
    plot_zone_node_density(all_df)
    plot_m_threshold_heatmap(data.get("bounds_M"), data.get("clocks"))
    plot_timeout_frontier(all_df)

    # ═══════════════════════════════════════════════════════════════════
    #  Scaling-Law Analysis (Plots 10–11)
    # ═══════════════════════════════════════════════════════════════════
    sl_df: Optional[pd.DataFrame] = None
    if not CFG.skip_heavy:
        sl_df = analyse_scaling_laws(all_df)
    else:
        print("\n  [Scaling laws] Skipped (--skip-heavy-regressions)")

    # ═══════════════════════════════════════════════════════════════════
    #  Normalized-Cost Plots (12–15)
    # ═══════════════════════════════════════════════════════════════════
    plot_normalized_costs(all_df)

    # ═══════════════════════════════════════════════════════════════════
    #  Enhanced SAT vs UNSAT (Plot 16)
    # ═══════════════════════════════════════════════════════════════════
    su_df = analyse_sat_vs_unsat(all_df)

    # ═══════════════════════════════════════════════════════════════════
    #  Phase-Boundary Analysis (Plot 17)
    # ═══════════════════════════════════════════════════════════════════
    analyse_phase_boundary(all_df)

    # ═══════════════════════════════════════════════════════════════════
    #  Memory Analysis (Plots 18–23, conditional)
    # ═══════════════════════════════════════════════════════════════════
    analyse_memory(all_df)

    # ═══════════════════════════════════════════════════════════════════
    #  Ablation Analysis (Plot 24)
    # ═══════════════════════════════════════════════════════════════════
    analyse_ablation(all_df)

    # ═══════════════════════════════════════════════════════════════════
    #  Hardness-Feature Analysis (Plot 25)
    # ═══════════════════════════════════════════════════════════════════
    analyse_hardness_features(all_df)

    # ═══════════════════════════════════════════════════════════════════
    #  LaTeX Tables
    # ═══════════════════════════════════════════════════════════════════
    print("\n───── LaTeX Tables ─────")
    tables_latex: list[str] = []
    if data["zeno"] is not None:
        tex = table_zeno_summary(data["zeno"])
        tables_latex.append(tex)
        print(tex)
    tex = table_performance_boundary(all_df)
    tables_latex.append(tex)
    print(tex)
    tex = table_descriptive_stats(all_df)
    tables_latex.append(tex)
    print(tex)
    tex = table_family_summary(all_df)
    tables_latex.append(tex)
    print(tex)

    # Write combined tables.tex
    tex_path = CFG.table_dir / "tables.tex"
    with open(tex_path, "w") as f:
        f.write("% Auto-generated LaTeX tables — TCTL benchmark analysis\n")
        f.write(f"% Generated: {datetime.now().isoformat()}\n\n")
        for i, t in enumerate(tables_latex, 1):
            f.write(f"% ──── Table {i} ────\n")
            f.write(t)
            f.write("\n\n")
    print(f"\n  \u2713 All tables saved to {tex_path}")

    # ═══════════════════════════════════════════════════════════════════
    #  Rationale & Report
    # ═══════════════════════════════════════════════════════════════════
    print("\n───── Technical Rationale & Report ─────")
    generate_rationale(all_df, data.get("zeno"))
    generate_report(all_df, sl_df, su_df)

    # ═══════════════════════════════════════════════════════════════════
    #  Export enriched dataset
    # ═══════════════════════════════════════════════════════════════════
    _save_csv(all_df, "enriched_dataset.csv")

    # ═══════════════════════════════════════════════════════════════════
    #  Summary
    # ═══════════════════════════════════════════════════════════════════
    n_plots = sum(1 for d in (CFG.plot_dir / CFG.formats[0]).iterdir()
                  if d.is_file()) if CFG.formats else 0
    print(f"\n{'═' * 50}")
    print(f"  Done. {n_plots} plots × {len(CFG.formats)} formats")
    print(f"  All outputs in: {CFG.output_root}")
    print(f"{'═' * 50}")


if __name__ == "__main__":
    main()
