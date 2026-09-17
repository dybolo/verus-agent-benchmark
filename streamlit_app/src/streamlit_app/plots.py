"""Build exportable matplotlib figures from the flattened benchmark-attempt table."""

from __future__ import annotations

import io
import itertools
from contextlib import AbstractContextManager
from dataclasses import dataclass

import matplotlib as mpl
import matplotlib.colors as mcolors
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import numpy as np
import pandas as pd
from matplotlib.figure import Figure
from matplotlib.lines import Line2D
from matplotlib.patches import Patch

COLORS = {
    "blue": "#0072B2",
    "orange": "#E69F00",
    "green": "#009E73",
    "red": "#D55E00",
    "purple": "#CC79A7",
    "sky": "#56B4E9",
    "yellow": "#F0E442",
    "gray": "#B7B7B7",
    "light_gray": "#E6E6E6",
    "dark": "#222222",
}

OUTCOME_ORDER = (
    "Valid repair",
    "Timed out without a valid repair",
    "Verus passed, Lynette rejected",
    "Verification failed",
)

OUTCOME_COLORS = {
    OUTCOME_ORDER[0]: COLORS["green"],
    OUTCOME_ORDER[1]: COLORS["gray"],
    OUTCOME_ORDER[2]: COLORS["orange"],
    OUTCOME_ORDER[3]: COLORS["red"],
}


@dataclass
class PlotResult:
    """A rendered figure, its export table, and an optional caveat for the viewer."""

    figure: Figure
    data: pd.DataFrame
    warning: str | None = None


def _style() -> AbstractContextManager[None]:
    """Return the shared matplotlib style used by every dashboard figure."""
    return mpl.rc_context(
        {
            "font.size": 10,
            "axes.titlesize": 12,
            "axes.labelsize": 10,
            "legend.fontsize": 9,
            "xtick.labelsize": 9,
            "ytick.labelsize": 9,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "figure.facecolor": "white",
            "axes.facecolor": "white",
            "savefig.facecolor": "white",
            "savefig.bbox": "tight",
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
        }
    )


def _ordered_conditions(attempts: pd.DataFrame) -> list[str]:
    """Return conditions in stable harness-then-model order."""
    conditions = attempts[["condition", "harness", "model"]].drop_duplicates()
    conditions = conditions.sort_values(["harness", "model"], kind="stable")
    return conditions["condition"].tolist()


def _format_usd_tick(value: float) -> str:
    """Format agent costs precisely enough to distinguish nearby plot positions."""
    return f"${value:,.4f}".rstrip("0").rstrip(".")


def outcome_composition(attempts: pd.DataFrame, width: float, height: float) -> PlotResult:
    """Plot the proportion of outcome categories for every selected condition."""
    condition_order = _ordered_conditions(attempts)
    counts = (
        attempts.groupby(["condition", "outcome"], observed=True)
        .size()
        .unstack(fill_value=0)
        .reindex(index=condition_order, columns=OUTCOME_ORDER, fill_value=0)
    )
    totals = counts.sum(axis=1)
    percentages = counts.div(totals.replace(0, np.nan), axis=0) * 100
    export = (
        counts.rename_axis(index="condition", columns="outcome").stack(future_stack=True).rename("count").reset_index()
    )
    export["percentage"] = export.apply(lambda row: percentages.loc[row["condition"], row["outcome"]], axis=1)

    with _style():
        figure, axis = plt.subplots(
            figsize=(width, max(height, 1.0 + 0.55 * len(condition_order))),
            constrained_layout=True,
        )
        left = np.zeros(len(condition_order))
        y = np.arange(len(condition_order))
        for outcome in OUTCOME_ORDER:
            values = percentages[outcome].to_numpy(dtype=float)
            bars = axis.barh(
                y,
                values,
                left=left,
                color=OUTCOME_COLORS[outcome],
                label=outcome,
                edgecolor="white",
                linewidth=0.6,
            )
            for index, (bar, percentage) in enumerate(zip(bars, values)):
                count = int(counts.iloc[index][outcome])
                if count and percentage >= 7:
                    axis.text(
                        bar.get_x() + bar.get_width() / 2,
                        bar.get_y() + bar.get_height() / 2,
                        f"{count}\n{percentage:.0f}%",
                        ha="center",
                        va="center",
                        fontsize=8,
                        color="white" if outcome != OUTCOME_ORDER[1] else COLORS["dark"],
                    )
            left += np.nan_to_num(values)
        axis.set_yticks(y, condition_order)
        axis.invert_yaxis()
        axis.set_xlim(0, 100)
        axis.set_xlabel("Share of attempted tasks (%)")
        axis.set_ylabel("Harness / model")
        axis.set_title("Proof-repair outcome composition", loc="left", fontweight="bold")
        axis.grid(axis="x", color=COLORS["light_gray"], linewidth=0.7)
        axis.set_axisbelow(True)
        axis.legend(
            loc="upper center",
            bbox_to_anchor=(0.5, -0.18),
            frameon=False,
            ncol=2,
        )
    return PlotResult(figure=figure, data=export)


def quality_cost(attempts: pd.DataFrame, width: float, height: float, cost_scale: str = "log") -> PlotResult:
    """Plot valid-repair rate against mean cost per attempt."""
    summary = (
        attempts.groupby(["condition", "harness", "model"], observed=True)
        .agg(
            attempted_tasks=("task_id", "size"),
            valid_repairs=("strict_success", "sum"),
            cost_observations=("cost_usd", "count"),
            total_cost_usd=("cost_usd", "sum"),
        )
        .reset_index()
    )
    summary["repair_rate"] = summary["valid_repairs"] / summary["attempted_tasks"]
    summary["mean_cost_per_attempt_usd"] = np.where(
        summary["cost_observations"] == summary["attempted_tasks"],
        summary["total_cost_usd"] / summary["attempted_tasks"],
        np.nan,
    )
    plotted = summary.dropna(subset=["mean_cost_per_attempt_usd"]).copy()
    if cost_scale == "log":
        plotted = plotted[plotted["mean_cost_per_attempt_usd"] > 0]

    warning = None
    omitted = len(summary) - len(plotted)
    if omitted:
        warning = f"{omitted} condition(s) omitted because cost data is incomplete or non-positive."

    harnesses = sorted(plotted["harness"].unique())
    markers = ["o", "s", "^", "D", "P", "X"]
    model_colors = {
        model: color
        for model, color in zip(
            sorted(plotted["model"].unique()),
            [
                COLORS["blue"],
                COLORS["orange"],
                COLORS["green"],
                COLORS["purple"],
                COLORS["red"],
            ],
        )
    }

    frontier = plotted.sort_values(["mean_cost_per_attempt_usd", "repair_rate"], ascending=[True, False])
    frontier = frontier[frontier["repair_rate"] > frontier["repair_rate"].cummax().shift(1, fill_value=-np.inf)]

    with _style():
        figure, axis = plt.subplots(figsize=(width, height), constrained_layout=True)
        for index, harness in enumerate(harnesses):
            group = plotted[plotted["harness"] == harness]
            for _, row in group.iterrows():
                axis.scatter(
                    row["mean_cost_per_attempt_usd"],
                    row["repair_rate"] * 100,
                    marker=markers[index % len(markers)],
                    s=78,
                    color=model_colors[row["model"]],
                    edgecolor=COLORS["dark"],
                    linewidth=0.6,
                    zorder=3,
                )
                axis.annotate(
                    row["condition"],
                    (row["mean_cost_per_attempt_usd"], row["repair_rate"] * 100),
                    xytext=(6, 6),
                    textcoords="offset points",
                    fontsize=8,
                )
        if len(frontier) > 1:
            axis.plot(
                frontier["mean_cost_per_attempt_usd"],
                frontier["repair_rate"] * 100,
                color=COLORS["dark"],
                linestyle="--",
                linewidth=1,
                label="Empirical Pareto frontier",
                zorder=2,
            )
        if cost_scale == "log" and not plotted.empty:
            axis.set_xscale("log")
            axis.xaxis.set_minor_formatter(mticker.NullFormatter())
        if not plotted.empty:
            agent_costs = np.sort(plotted["mean_cost_per_attempt_usd"].unique())
            axis.set_xticks(
                agent_costs,
                [_format_usd_tick(cost) for cost in agent_costs],
                rotation=30,
                ha="right",
            )
        axis.set_ylim(0, 100)
        axis.set_xlabel("Mean cost per attempted task (USD)")
        axis.set_ylabel("Valid repair rate (%)")
        axis.set_title("Proof-repair quality versus cost", loc="left", fontweight="bold")
        axis.grid(color=COLORS["light_gray"], linewidth=0.7)
        axis.set_axisbelow(True)
        harness_handles = [
            Line2D(
                [],
                [],
                color=COLORS["dark"],
                marker=markers[index % len(markers)],
                linestyle="None",
                label=harness,
            )
            for index, harness in enumerate(harnesses)
        ]
        if harness_handles:
            axis.legend(handles=harness_handles, title="Harness", frameon=False, loc="best")
    return PlotResult(figure=figure, data=summary, warning=warning)


def caterpillar(attempts: pd.DataFrame, width: float, minimum_height: float) -> PlotResult:
    """Plot repair rates by proof style and source module."""
    summary = (
        attempts.dropna(subset=["proof_style", "source_module"])
        .groupby(["proof_style", "source_module", "task_id"], observed=True)
        .agg(observed=("strict_success", "size"), solved=("strict_success", "sum"))
        .reset_index()
    )
    summary["solve_rate"] = summary["solved"] / summary["observed"]
    proof_order = [
        proof for proof in ("atomic-operation", "tokenized_state_machine!") if proof in set(summary["proof_style"])
    ]
    proof_order.extend(sorted(set(summary["proof_style"]) - set(proof_order)))
    if not proof_order:
        with _style():
            figure, axis = plt.subplots(figsize=(width, minimum_height))
            axis.text(0.5, 0.5, "No tasks with metadata", ha="center", va="center")
            axis.axis("off")
        return PlotResult(figure, summary, "No selected tasks have proof-style metadata.")

    rows_per_panel = [
        len(summary[summary["proof_style"] == proof])
        + summary[summary["proof_style"] == proof]["source_module"].nunique()
        for proof in proof_order
    ]
    figure_height = max(minimum_height, 1.8 + 0.33 * max(rows_per_panel))
    with _style():
        figure, axes = plt.subplots(
            1,
            len(proof_order),
            figsize=(width, figure_height),
            constrained_layout=True,
            squeeze=False,
        )
        for axis, proof_style in zip(axes[0], proof_order):
            panel = summary[summary["proof_style"] == proof_style].sort_values(
                ["source_module", "solve_rate", "task_id"], kind="stable"
            )
            task_positions: list[float] = []
            tick_positions: list[float] = []
            labels: list[str] = []
            header_ticks: list[bool] = []
            cursor = 0.0
            for source_module, module_tasks in panel.groupby("source_module", observed=True, sort=False):
                header_position = cursor
                tick_positions.append(header_position)
                labels.append(str(source_module))
                header_ticks.append(True)
                axis.axhspan(
                    header_position - 0.38,
                    header_position + 0.38,
                    color=COLORS["light_gray"],
                    alpha=0.65,
                    linewidth=0,
                    zorder=0,
                )
                cursor += 0.85
                for task_id in module_tasks["task_id"]:
                    task_positions.append(cursor)
                    tick_positions.append(cursor)
                    labels.append(f"    {task_id}")
                    header_ticks.append(False)
                    cursor += 1.0
                cursor += 0.35
            axis.hlines(
                task_positions,
                0,
                panel["solve_rate"],
                color=COLORS["light_gray"],
                linewidth=1.5,
            )
            axis.scatter(
                panel["solve_rate"],
                task_positions,
                color=COLORS["blue"] if proof_style == "atomic-operation" else COLORS["orange"],
                edgecolor=COLORS["dark"],
                linewidth=0.4,
                s=38,
                zorder=3,
            )
            for position, (_, row) in zip(task_positions, panel.iterrows()):
                axis.annotate(
                    f"{int(row['solved'])}/{int(row['observed'])}",
                    (row["solve_rate"], position),
                    xytext=(5, 0),
                    textcoords="offset points",
                    va="center",
                    fontsize=8,
                )
            axis.set_yticks(tick_positions, labels)
            for tick_label, is_header in zip(axis.get_yticklabels(), header_ticks):
                if is_header:
                    tick_label.set_fontweight("bold")
            axis.set_ylim(-0.5, cursor - 0.15)
            axis.invert_yaxis()
            axis.set_xlim(-0.02, 1.14)
            axis.set_xticks(np.linspace(0, 1, 5), ["0", "25", "50", "75", "100"])
            axis.set_xlabel("Valid repair rate (%)")
            axis.set_title(proof_style, loc="left", fontweight="bold")
            axis.grid(axis="x", color=COLORS["light_gray"], linewidth=0.7)
            axis.set_axisbelow(True)
        figure.suptitle("Task difficulty by proof style and source module", fontweight="bold")
    return PlotResult(figure=figure, data=summary)


def difficulty_bubble_scatter(
    attempts: pd.DataFrame, width: float, height: float
) -> PlotResult:
    """Relate task size and missing proof code to repair success and atomic operations."""
    dimensions = ["method_lines", "missing_code_lines", "atomic_operations"]
    available = attempts.dropna(subset=dimensions).copy()
    summary = (
        available.groupby(
            ["task_id", "proof_style", "source_module", *dimensions],
            observed=True,
            dropna=False,
        )
        .agg(attempts=("strict_success", "size"), valid_repairs=("strict_success", "sum"))
        .reset_index()
    )
    summary["agent_success_rate"] = (
        summary["valid_repairs"] / summary["attempts"] * 100
    )
    plotted = summary[
        (summary["method_lines"] > 0) & (summary["missing_code_lines"] > 0)
    ].copy()

    omitted = attempts["task_id"].nunique() - plotted["task_id"].nunique()
    warning = None
    if omitted:
        warning = (
            f"{omitted} task(s) omitted because size metadata is missing or non-positive."
        )

    minimum_area = 32.0
    area_per_operation = 30.0
    bubble_areas = minimum_area + area_per_operation * plotted["atomic_operations"]
    success_colors = mcolors.LinearSegmentedColormap.from_list(
        "agent_success_rate", ["#355FB3", "#66B7AE"]
    )

    with _style():
        figure, axis = plt.subplots(figsize=(width, height), constrained_layout=True)
        scatter = axis.scatter(
            plotted["method_lines"],
            plotted["missing_code_lines"],
            s=bubble_areas,
            c=plotted["agent_success_rate"],
            cmap=success_colors,
            norm=mcolors.Normalize(vmin=0, vmax=100),
            alpha=0.6,
            edgecolor=COLORS["dark"],
            linewidth=0.5,
            zorder=3,
        )
        if not plotted.empty:
            axis.set_xscale("log")
            axis.set_yscale("log")
            for scale_axis in (axis.xaxis, axis.yaxis):
                scale_axis.set_major_locator(
                    mticker.LogLocator(base=10, subs=(1.0, 3.0))
                )
                scale_axis.set_major_formatter(mticker.ScalarFormatter())
                scale_axis.set_minor_formatter(mticker.NullFormatter())
        axis.set_xlabel("Method lines (log scale)")
        axis.set_ylabel("Missing-code lines (log scale)")
        axis.set_title(
            "Task size, missing proof code, and agent success",
            loc="left",
            fontweight="bold",
        )
        axis.grid(color=COLORS["light_gray"], linewidth=0.7, which="both")
        axis.set_axisbelow(True)
        colorbar = figure.colorbar(scatter, ax=axis, pad=0.02)
        colorbar.set_label("Agent success rate (%)")

        if not plotted.empty:
            maximum_operations = int(plotted["atomic_operations"].max())
            size_handles = [
                Line2D(
                    [],
                    [],
                    marker="o",
                    linestyle="None",
                    markersize=np.sqrt(area),
                    markerfacecolor="none",
                    markeredgecolor=COLORS["dark"],
                )
                for area in (
                    minimum_area,
                    minimum_area + area_per_operation * maximum_operations,
                )
            ]
            axis.legend(
                handles=size_handles,
                labels=["", "size: atomic operations"],
                frameon=False,
                loc="upper left",
                ncol=2,
                handletextpad=0.2,
                columnspacing=0.4,
            )
    return PlotResult(figure=figure, data=summary, warning=warning)


def _format_range_value(value: float) -> str:
    """Format a numeric bin boundary without unnecessary decimal places."""
    return f"{value:g}"


def _quartile_bin_codes(values: pd.Series) -> tuple[pd.Series, list[tuple[float, float]]]:
    """Assign numeric values to up to four quantile bins."""
    edges = np.unique(values.quantile(np.linspace(0, 1, 5)).to_numpy(dtype=float))
    if len(edges) == 1:
        return pd.Series(0, index=values.index, dtype=int), [(edges[0], edges[0])]
    codes = pd.cut(values, bins=edges, labels=False, include_lowest=True).astype(int)
    ranges = list(itertools.pairwise(edges))
    return codes, ranges


def _atomic_operation_bin_codes(
    values: pd.Series,
) -> tuple[pd.Series, list[tuple[float, float]]]:
    """Keep repeated operation counts together in four interpretable ranges."""
    maximum = float(values.max())
    definitions = [
        (values == 0, (0.0, 0.0)),
        (values == 1, (1.0, 1.0)),
        (values.between(2, 3), (2.0, min(3.0, maximum))),
        (values >= 4, (4.0, maximum)),
    ]
    codes = pd.Series(-1, index=values.index, dtype=int)
    ranges: list[tuple[float, float]] = []
    for mask, value_range in definitions:
        if not mask.any():
            continue
        codes.loc[mask] = len(ranges)
        ranges.append(value_range)
    return codes, ranges


def binned_success_curves(
    attempts: pd.DataFrame, width: float, height: float
) -> PlotResult:
    """Plot valid-repair rates across task-complexity ranges."""
    metrics = [
        ("method_lines", "Method lines"),
        ("missing_code_lines", "Missing-code lines"),
        ("atomic_operations", "Atomic operations"),
    ]
    dimensions = [metric for metric, _ in metrics]
    tasks = (
        attempts.dropna(subset=dimensions)
        .groupby(["task_id", *dimensions], observed=True)
        .agg(attempts=("strict_success", "size"), valid_repairs=("strict_success", "sum"))
        .reset_index()
    )
    records: list[dict[str, object]] = []
    for metric, label in metrics:
        if tasks.empty:
            continue
        if metric == "atomic_operations":
            codes, ranges = _atomic_operation_bin_codes(tasks[metric])
        else:
            codes, ranges = _quartile_bin_codes(tasks[metric])
        binned = tasks.assign(bin_order=codes)
        for bin_order, value_range in enumerate(ranges):
            members = binned[binned["bin_order"] == bin_order]
            if members.empty:
                continue
            attempted = int(members["attempts"].sum())
            repaired = int(members["valid_repairs"].sum())
            lower, upper = value_range
            records.append(
                {
                    "metric": metric,
                    "metric_label": label,
                    "bin_order": bin_order,
                    "bin_label": (
                        f"{_format_range_value(lower)}–{_format_range_value(upper)}"
                    ),
                    "range_min": lower,
                    "range_max": upper,
                    "tasks": members["task_id"].nunique(),
                    "attempts": attempted,
                    "valid_repairs": repaired,
                    "agent_success_rate": repaired / attempted * 100,
                }
            )
    summary = pd.DataFrame.from_records(records)

    warning = None
    omitted = attempts["task_id"].nunique() - tasks["task_id"].nunique()
    if omitted:
        warning = f"{omitted} task(s) omitted because complexity metadata is missing."

    success_colors = mcolors.LinearSegmentedColormap.from_list(
        "binned_agent_success_rate", ["#355FB3", "#66B7AE"]
    )
    with _style():
        figure, axes = plt.subplots(
            1,
            len(metrics),
            figsize=(width, height),
            constrained_layout=True,
            squeeze=False,
        )
        for axis, (metric, label) in zip(axes[0], metrics):
            panel = summary[summary["metric"] == metric].sort_values("bin_order")
            positions = np.arange(len(panel))
            rates = panel["agent_success_rate"].to_numpy(dtype=float)
            axis.plot(
                positions,
                rates,
                color=COLORS["yellow"],
                linewidth=2,
                zorder=2,
            )
            axis.scatter(
                positions,
                rates,
                c=rates,
                cmap=success_colors,
                norm=mcolors.Normalize(vmin=0, vmax=100),
                s=70,
                edgecolor="white",
                linewidth=0.8,
                zorder=3,
            )
            axis.set_xticks(positions, panel["bin_label"])
            axis.set_ylim(0, 100)
            axis.set_yticks(np.arange(0, 101, 20))
            axis.yaxis.set_major_formatter(mticker.PercentFormatter(xmax=100, decimals=0))
            axis.set_xlabel(f"{label} (quartile range)")
            axis.set_ylabel("Agent success rate")
            axis.set_title(label, fontweight="bold")
            axis.grid(axis="y", color=COLORS["light_gray"], linewidth=0.7)
            axis.set_axisbelow(True)
        figure.suptitle("Binned success curves", fontweight="bold")
    return PlotResult(figure=figure, data=summary, warning=warning)


def harness_comparisons(attempts: pd.DataFrame) -> pd.DataFrame:
    """Build task-level same-model comparisons between harnesses."""
    metadata = attempts[["task_id", "proof_style", "source_module"]].drop_duplicates("task_id").set_index("task_id")
    all_tasks = sorted(attempts["task_id"].unique())
    records: list[dict[str, object]] = []
    for model, model_attempts in attempts.groupby("model", observed=True):
        harnesses = sorted(model_attempts["harness"].unique())
        for harness_a, harness_b in itertools.combinations(harnesses, 2):
            success_a = (
                model_attempts[model_attempts["harness"] == harness_a].set_index("task_id")["strict_success"].to_dict()
            )
            success_b = (
                model_attempts[model_attempts["harness"] == harness_b].set_index("task_id")["strict_success"].to_dict()
            )
            comparison = f"{model}\n{harness_a} ↔ {harness_b}"
            for identifier in all_tasks:
                value_a = success_a.get(identifier)
                value_b = success_b.get(identifier)
                if value_a is None or value_b is None:
                    disagreement = "Missing"
                    agreement = "Missing"
                elif value_a and not value_b:
                    disagreement = f"{harness_a} only"
                    agreement = "Disagreement"
                elif value_b and not value_a:
                    disagreement = f"{harness_b} only"
                    agreement = "Disagreement"
                elif value_a and value_b:
                    disagreement = "Agreement"
                    agreement = "Both pass"
                else:
                    disagreement = "Agreement"
                    agreement = "Both fail"
                task_metadata = metadata.loc[identifier] if identifier in metadata.index else {}
                records.append(
                    {
                        "task_id": identifier,
                        "proof_style": task_metadata.get("proof_style") if hasattr(task_metadata, "get") else None,
                        "source_module": task_metadata.get("source_module") if hasattr(task_metadata, "get") else None,
                        "model": model,
                        "harness_a": harness_a,
                        "harness_b": harness_b,
                        "comparison": comparison,
                        "harness_a_success": value_a,
                        "harness_b_success": value_b,
                        "disagreement": disagreement,
                        "agreement": agreement,
                    }
                )
    return pd.DataFrame.from_records(records)


def _matrix(
    comparison_data: pd.DataFrame,
    kind: str,
    width: float,
    minimum_height: float,
) -> PlotResult:
    """Render a task-by-comparison agreement or disagreement matrix."""
    if comparison_data.empty:
        with _style():
            figure, axis = plt.subplots(figsize=(width, minimum_height))
            axis.text(
                0.5,
                0.5,
                "No same-model harness pair is available",
                ha="center",
                va="center",
            )
            axis.axis("off")
        return PlotResult(
            figure,
            comparison_data,
            "Select at least two harnesses that evaluated the same model.",
        )

    ordered_tasks = (
        comparison_data[["task_id", "proof_style", "source_module"]]
        .drop_duplicates("task_id")
        .sort_values(["proof_style", "source_module", "task_id"], na_position="last")["task_id"]
        .tolist()
    )
    comparisons = comparison_data["comparison"].drop_duplicates().tolist()
    if kind == "disagreement":
        statuses = comparison_data["disagreement"]
        directional = [value for value in statuses.unique() if value.endswith(" only")]
        status_order = ["Agreement", *sorted(directional), "Missing"]
        status_colors = {"Agreement": COLORS["light_gray"], "Missing": COLORS["gray"]}
        for status, color in zip(sorted(directional), [COLORS["blue"], COLORS["orange"]]):
            status_colors[status] = color
        palette = [status_colors[status] for status in status_order]
        labels = {"Agreement": "·", "Missing": "×"}
        title = "Task-level harness disagreements"
        value_column = "disagreement"
    else:
        status_order = ["Both fail", "Disagreement", "Both pass", "Missing"]
        status_colors = {
            "Both fail": COLORS["red"],
            "Disagreement": COLORS["light_gray"],
            "Both pass": COLORS["green"],
            "Missing": COLORS["gray"],
        }
        palette = [status_colors[status] for status in status_order]
        labels = {
            "Both fail": "F",
            "Disagreement": "·",
            "Both pass": "P",
            "Missing": "×",
        }
        title = "Task-level harness agreements"
        value_column = "agreement"

    status_to_code = {status: index for index, status in enumerate(status_order)}
    pivot = comparison_data.pivot(index="task_id", columns="comparison", values=value_column)
    pivot = pivot.reindex(index=ordered_tasks, columns=comparisons)
    matrix = pivot.apply(lambda column: column.map(status_to_code)).to_numpy(dtype=float)
    cmap = mcolors.ListedColormap(palette[: len(status_order)])
    norm = mcolors.BoundaryNorm(np.arange(-0.5, len(status_order) + 0.5), cmap.N)
    figure_height = max(minimum_height, 1.8 + 0.27 * len(ordered_tasks))

    with _style():
        figure, axis = plt.subplots(figsize=(width, figure_height), constrained_layout=True)
        axis.imshow(matrix, cmap=cmap, norm=norm, aspect="auto", interpolation="none")
        axis.set_xticks(np.arange(len(comparisons)), comparisons)
        axis.set_yticks(np.arange(len(ordered_tasks)), ordered_tasks)
        axis.tick_params(axis="x", labelrotation=25)
        axis.set_xlabel("Same-model harness comparison")
        axis.set_ylabel("Task")
        axis.set_title(title, loc="left", fontweight="bold")
        axis.set_xticks(np.arange(-0.5, len(comparisons), 1), minor=True)
        axis.set_yticks(np.arange(-0.5, len(ordered_tasks), 1), minor=True)
        axis.grid(which="minor", color="white", linewidth=0.8)
        axis.tick_params(which="minor", bottom=False, left=False)
        for row_index, task in enumerate(ordered_tasks):
            for column_index, comparison in enumerate(comparisons):
                status = pivot.loc[task, comparison]
                text = labels.get(status, "A" if str(status).endswith(" only") else "")
                if kind == "disagreement" and str(status).endswith(" only"):
                    harness = str(status).removesuffix(" only")
                    text = harness[:1].upper()
                axis.text(column_index, row_index, text, ha="center", va="center", fontsize=7)
        axis.legend(
            handles=[Patch(facecolor=palette[index], label=status) for index, status in enumerate(status_order)],
            frameon=False,
            loc="upper center",
            bbox_to_anchor=(0.5, -0.05),
            ncol=min(4, len(status_order)),
        )
    return PlotResult(figure=figure, data=comparison_data)


def disagreement_matrix(comparison_data: pd.DataFrame, width: float, minimum_height: float) -> PlotResult:
    """Render directional differences between same-model harness results."""
    return _matrix(comparison_data, "disagreement", width, minimum_height)


def agreement_matrix(comparison_data: pd.DataFrame, width: float, minimum_height: float) -> PlotResult:
    """Render matching and non-matching same-model harness results."""
    return _matrix(comparison_data, "agreement", width, minimum_height)


def exclusive_solves_matrix(attempts: pd.DataFrame, width: float, minimum_height: float) -> PlotResult:
    """Plot task outcomes and highlight solves unique to one same-model harness."""
    comparable_models = [
        model for model, group in attempts.groupby("model", observed=True) if group["harness"].nunique() >= 2
    ]
    records: list[dict[str, object]] = []
    panels: list[tuple[str, pd.DataFrame, list[str]]] = []
    for model in comparable_models:
        model_attempts = attempts[attempts["model"] == model]
        harnesses = sorted(model_attempts["harness"].unique())
        success = model_attempts.pivot_table(
            index="task_id",
            columns="harness",
            values="strict_success",
            aggfunc="max",
        ).reindex(columns=harnesses)
        solver_counts = success.fillna(False).sum(axis=1).astype(int)
        exclusive_solver = success.apply(
            lambda row: str(row[row.fillna(False).astype(bool)].index[0]) if row.fillna(False).sum() == 1 else None,
            axis=1,
        )
        ordering = pd.DataFrame(
            {
                "task_id": success.index,
                "is_exclusive": solver_counts.eq(1).astype(int).to_numpy(),
                "solver_count": solver_counts.to_numpy(),
            }
        ).sort_values(
            ["is_exclusive", "solver_count", "task_id"],
            ascending=[False, True, True],
            kind="stable",
        )
        success = success.reindex(ordering["task_id"])
        panels.append((str(model), success, harnesses))
        for task_id, row in success.iterrows():
            count = int(solver_counts.loc[task_id])
            only = exclusive_solver.loc[task_id]
            for harness in harnesses:
                value = row[harness]
                records.append(
                    {
                        "model": model,
                        "task_id": task_id,
                        "harness": harness,
                        "success": value if pd.notna(value) else pd.NA,
                        "solver_count": count,
                        "exclusive_solver": only,
                        "status": (
                            "Missing"
                            if pd.isna(value)
                            else "Exclusive solve"
                            if bool(value) and only == harness
                            else "Shared solve"
                            if bool(value)
                            else "Failed"
                        ),
                    }
                )

    export = pd.DataFrame.from_records(
        records,
        columns=[
            "model",
            "task_id",
            "harness",
            "success",
            "solver_count",
            "exclusive_solver",
            "status",
        ],
    )
    if not panels:
        with _style():
            figure, axis = plt.subplots(figsize=(width, minimum_height))
            axis.text(
                0.5,
                0.5,
                "No same-model harness comparison is available",
                ha="center",
                va="center",
            )
            axis.axis("off")
        return PlotResult(
            figure,
            export,
            "Select at least two harnesses that evaluated the same model.",
        )

    total_rows = sum(len(panel) for _, panel, _ in panels)
    figure_height = max(minimum_height, 1.8 + 0.25 * total_rows)
    status_order = ["Failed", "Shared solve", "Exclusive solve", "Missing"]
    status_colors = [
        COLORS["light_gray"],
        COLORS["green"],
        COLORS["blue"],
        COLORS["gray"],
    ]
    cmap = mcolors.ListedColormap(status_colors)
    norm = mcolors.BoundaryNorm(np.arange(-0.5, len(status_order) + 0.5), cmap.N)

    with _style():
        figure, axes = plt.subplots(
            len(panels),
            1,
            figsize=(width, figure_height),
            constrained_layout=True,
            squeeze=False,
            gridspec_kw={"height_ratios": [len(panel) for _, panel, _ in panels]},
        )
        for axis, (model, success, harnesses) in zip(axes[:, 0], panels):
            codes = np.full(success.shape, 3, dtype=float)
            for row_index, task_id in enumerate(success.index):
                for column_index, harness in enumerate(harnesses):
                    value = success.loc[task_id, harness]
                    if pd.isna(value):
                        continue
                    if not bool(value):
                        codes[row_index, column_index] = 0
                    elif int(success.loc[task_id].fillna(False).sum()) == 1:
                        codes[row_index, column_index] = 2
                    else:
                        codes[row_index, column_index] = 1
            axis.imshow(codes, cmap=cmap, norm=norm, aspect="auto", interpolation="none")
            axis.set_xticks(np.arange(len(harnesses)), harnesses)
            axis.set_yticks(np.arange(len(success.index)), success.index)
            axis.set_xlabel("Harness")
            axis.set_ylabel("Task")
            axis.set_title(model, loc="left", fontweight="bold")
            axis.set_xticks(np.arange(-0.5, len(harnesses), 1), minor=True)
            axis.set_yticks(np.arange(-0.5, len(success.index), 1), minor=True)
            axis.grid(which="minor", color="white", linewidth=0.8)
            axis.tick_params(which="minor", bottom=False, left=False)
            for row_index, task_id in enumerate(success.index):
                for column_index, harness in enumerate(harnesses):
                    code = int(codes[row_index, column_index])
                    text = "★" if code == 2 else "●" if code == 1 else "×" if code == 3 else ""
                    if text:
                        axis.text(
                            column_index,
                            row_index,
                            text,
                            ha="center",
                            va="center",
                            fontsize=7,
                            color="white" if code in (1, 2) else COLORS["dark"],
                        )
        figure.suptitle(
            "Task-level proof-repair outcomes by harness",
            fontweight="bold",
        )
        axes[-1, 0].legend(
            handles=[Patch(facecolor=color, label=status) for color, status in zip(status_colors, status_order)],
            frameon=False,
            loc="upper center",
            bbox_to_anchor=(0.5, -0.12),
            ncol=4,
        )
    omitted_models = attempts["model"].nunique() - len(comparable_models)
    warning = None
    if omitted_models:
        warning = f"{omitted_models} model(s) omitted because fewer than two harnesses evaluated that model."
    return PlotResult(figure=figure, data=export, warning=warning)


def task_normalized_harness_effect(
    attempts: pd.DataFrame,
    width: float,
    minimum_height: float,
    *,
    reference_harness: str = "pi",
    bootstrap_samples: int = 10_000,
    random_seed: int = 0,
) -> PlotResult:
    """Compare each harness with Pi on the same tasks and model.

    Resource effects are median within-task ratios. Repair effects are paired
    repair-rate differences because a ratio is not meaningful for binary task
    outcomes. Confidence intervals bootstrap whole task contrasts.
    """
    metric_specs = (
        ("total_input_tokens", "Input tokens", "ratio"),
        ("total_output_tokens", "Output tokens", "ratio"),
        ("total_tool_calls", "Tool calls", "ratio"),
        ("strict_success", "Valid proof repairs", "difference"),
    )
    values = (
        attempts.groupby(["model", "harness", "task_id"], observed=True)
        .agg(
            total_input_tokens=("total_input_tokens", "median"),
            total_output_tokens=("total_output_tokens", "median"),
            total_tool_calls=("total_tool_calls", "median"),
            strict_success=("strict_success", "max"),
        )
        .reset_index()
    )
    rng = np.random.default_rng(random_seed)
    records: list[dict[str, object]] = []
    models_without_reference = 0

    for model, model_values in values.groupby("model", observed=True, sort=True):
        if reference_harness not in set(model_values["harness"]):
            models_without_reference += 1
            continue
        reference = model_values[model_values["harness"] == reference_harness]
        harnesses = sorted(set(model_values["harness"]) - {reference_harness})
        for harness in harnesses:
            candidate = model_values[model_values["harness"] == harness]
            available_tasks = len(set(reference["task_id"]) | set(candidate["task_id"]))
            for metric, metric_label, effect_type in metric_specs:
                paired = candidate[["task_id", metric]].merge(
                    reference[["task_id", metric]],
                    on="task_id",
                    how="inner",
                    suffixes=("_harness", "_reference"),
                )
                harness_values = pd.to_numeric(paired[f"{metric}_harness"], errors="coerce")
                reference_values = pd.to_numeric(paired[f"{metric}_reference"], errors="coerce")
                valid = harness_values.notna() & reference_values.notna()
                if effect_type == "ratio":
                    valid &= (harness_values > 0) & (reference_values > 0)
                paired = paired[valid]
                if paired.empty:
                    continue

                harness_array = pd.to_numeric(paired[f"{metric}_harness"]).to_numpy(dtype=float)
                reference_array = pd.to_numeric(paired[f"{metric}_reference"]).to_numpy(dtype=float)
                contrasts = harness_array / reference_array if effect_type == "ratio" else harness_array - reference_array
                statistic = np.median if effect_type == "ratio" else np.mean
                estimate = float(statistic(contrasts))
                if bootstrap_samples > 0:
                    samples = rng.choice(contrasts, size=(bootstrap_samples, len(contrasts)), replace=True)
                    bootstrap_estimates = statistic(samples, axis=1)
                    ci_low, ci_high = np.quantile(bootstrap_estimates, [0.025, 0.975])
                else:
                    ci_low = ci_high = estimate

                scale = 1 if effect_type == "ratio" else 100
                records.append(
                    {
                        "model": model,
                        "harness": harness,
                        "reference_harness": reference_harness,
                        "comparison": f"{harness} vs {reference_harness}",
                        "metric": metric,
                        "metric_label": metric_label,
                        "effect_type": "median within-task ratio" if effect_type == "ratio" else "paired rate difference",
                        "paired_tasks": len(contrasts),
                        "excluded_tasks": available_tasks - len(contrasts),
                        "harness_task_median": float(np.median(harness_array)),
                        "reference_task_median": float(np.median(reference_array)),
                        "estimate": estimate * scale,
                        "ci_low": float(ci_low) * scale,
                        "ci_high": float(ci_high) * scale,
                        "unit": "ratio" if effect_type == "ratio" else "percentage points",
                    }
                )

    summary = pd.DataFrame.from_records(
        records,
        columns=[
            "model",
            "harness",
            "reference_harness",
            "comparison",
            "metric",
            "metric_label",
            "effect_type",
            "paired_tasks",
            "excluded_tasks",
            "harness_task_median",
            "reference_task_median",
            "estimate",
            "ci_low",
            "ci_high",
            "unit",
        ],
    )
    if summary.empty:
        with _style():
            figure, axis = plt.subplots(figsize=(width, minimum_height))
            axis.text(
                0.5,
                0.5,
                f"No same-model comparison with {reference_harness} is available",
                ha="center",
                va="center",
            )
            axis.axis("off")
        return PlotResult(
            figure,
            summary,
            f"Select {reference_harness} and at least one other harness that evaluated the same model on a shared task.",
        )

    comparison_order = (
        summary[["harness", "model", "comparison"]]
        .drop_duplicates()
        .sort_values(["harness", "model"], kind="stable")["comparison"]
        .tolist()
    )
    metric_order = [metric for metric, _, _ in metric_specs]
    summary["comparison"] = pd.Categorical(summary["comparison"], comparison_order, ordered=True)
    summary["metric"] = pd.Categorical(summary["metric"], metric_order, ordered=True)
    summary = summary.sort_values(["comparison", "metric"], kind="stable").reset_index(drop=True)
    labels = []
    for comparison in comparison_order:
        row = summary[summary["comparison"] == comparison].iloc[0]
        labels.append(f"{row['harness']} | {row['model']}")
    y = np.arange(len(comparison_order))
    figure_height = max(minimum_height, 2.2 + 0.58 * len(comparison_order))
    harnesses = sorted(summary["harness"].unique())
    palette = [COLORS["blue"], COLORS["orange"], COLORS["green"], COLORS["purple"], COLORS["red"]]
    harness_colors = {harness: palette[index % len(palette)] for index, harness in enumerate(harnesses)}

    resource_summary = summary[summary["unit"] == "ratio"]
    if resource_summary.empty:
        log_low, log_high = 0.5, 2.0
    else:
        resource_low = max(float(resource_summary["ci_low"].min()), np.finfo(float).tiny)
        resource_high = float(resource_summary["ci_high"].max())
        log_low = 2.0 ** np.floor(np.log2(min(resource_low, 1.0)))
        log_high = 2.0 ** np.ceil(np.log2(max(resource_high, 1.0)))
    if log_low == log_high:
        log_low /= 2
        log_high *= 2
    ratio_ticks = [tick for tick in (0.125, 0.25, 0.5, 1, 2, 4, 8, 16, 32) if log_low <= tick <= log_high]

    with _style():
        figure, axes = plt.subplots(1, len(metric_specs), figsize=(width, figure_height), constrained_layout=True, sharey=True)
        for axis, (metric, metric_label, effect_type) in zip(axes, metric_specs):
            panel = summary[summary["metric"] == metric].set_index("comparison").reindex(comparison_order)
            estimates = panel["estimate"].to_numpy(dtype=float)
            ci_low = panel["ci_low"].to_numpy(dtype=float)
            ci_high = panel["ci_high"].to_numpy(dtype=float)
            valid = ~np.isnan(estimates)
            reference_value = 1 if effect_type == "ratio" else 0
            axis.axvline(reference_value, color=COLORS["dark"], linewidth=1, linestyle="--", zorder=1)
            for position in y[valid]:
                row = panel.iloc[position]
                estimate = float(row["estimate"])
                low = float(row["ci_low"])
                high = float(row["ci_high"])
                axis.errorbar(
                    estimate,
                    position,
                    xerr=np.array([[estimate - low], [high - estimate]]),
                    fmt="o",
                    color=harness_colors[str(row["harness"])],
                    markeredgecolor=COLORS["dark"],
                    markeredgewidth=0.5,
                    ecolor=COLORS["dark"],
                    elinewidth=1.2,
                    capsize=3,
                    markersize=6,
                    zorder=3,
                )
                label = f"{estimate:.2f}×" if effect_type == "ratio" else f"{estimate:+.1f} pp"
                axis.annotate(label, (estimate, position), xytext=(5, 6), textcoords="offset points", fontsize=7)
            if effect_type == "ratio":
                axis.set_xscale("log", base=2)
                axis.set_xlim(log_low / 1.08, log_high * 1.08)
                axis.set_xticks(ratio_ticks, [f"{tick:g}×" for tick in ratio_ticks])
                axis.xaxis.set_minor_formatter(mticker.NullFormatter())
                axis.set_xlabel(f"Relative to {reference_harness.capitalize()}")
            else:
                extent = min(100.0, max(10.0, float(np.nanmax(np.abs([ci_low, ci_high]))) + 8.0))
                axis.set_xlim(-extent, extent)
                axis.xaxis.set_major_formatter(mticker.PercentFormatter(xmax=100, decimals=0))
                axis.set_xlabel(f"Difference from {reference_harness.capitalize()} (pp)")
            axis.set_title(metric_label, loc="left", fontweight="bold")
            axis.grid(axis="x", color=COLORS["light_gray"], linewidth=0.7)
            axis.set_axisbelow(True)
        axes[0].set_yticks(y, labels)
        axes[0].invert_yaxis()
        axes[0].set_ylabel("Harness | model")
        figure.suptitle(
            f"Task-normalized harness effects relative to {reference_harness.capitalize()}",
            fontweight="bold",
        )

    warning_parts = []
    excluded = int(summary["excluded_tasks"].sum())
    if excluded:
        warning_parts.append(
            f"{excluded} task–metric observation(s) were excluded because the task was unpaired, missing, or had a non-positive resource value"
        )
    if models_without_reference:
        warning_parts.append(
            f"{models_without_reference} selected model(s) were omitted because {reference_harness} was not available"
        )
    warning = "; ".join(warning_parts) + "." if warning_parts else None
    return PlotResult(figure=figure, data=summary, warning=warning)


def tokens_used_by_agent_for_each_task(
    attempts: pd.DataFrame, width: float, minimum_height: float
) -> PlotResult:
    """Plot each agent's input-plus-output token use for every selected task.

    When the input contains repeated attempts for a condition/task pair, the bar
    shows their median total token use rather than adding separate attempts.
    """
    condition_order = _ordered_conditions(attempts)
    token_attempts = attempts.assign(
        total_tokens=pd.to_numeric(attempts["total_input_tokens"], errors="coerce")
        + pd.to_numeric(attempts["total_output_tokens"], errors="coerce")
    )
    summary = (
        token_attempts.groupby(
            ["task_id", "task_file", "condition", "harness", "model"],
            observed=True,
            dropna=False,
        )
        .agg(
            attempts=("task_id", "size"),
            token_observations=("total_tokens", "count"),
            median_input_tokens=("total_input_tokens", "median"),
            median_output_tokens=("total_output_tokens", "median"),
            total_tokens=("total_tokens", "median"),
        )
        .reset_index()
    )
    task_labels = (
        attempts[["task_id", "task_file"]]
        .drop_duplicates("task_id")
        .assign(task_label=lambda frame: frame["task_file"].fillna(frame["task_id"] + ".rs"))
        .sort_values(["task_label", "task_id"], kind="stable")
    )
    task_order = task_labels["task_id"].tolist()
    labels = task_labels.set_index("task_id").loc[task_order, "task_label"].tolist()
    condition_details = attempts[["condition", "harness", "model"]].drop_duplicates("condition")
    conditions_per_harness = condition_details.groupby("harness", observed=True)["condition"].nunique()
    condition_labels = {
        row.condition: (
            str(row.harness).capitalize()
            if conditions_per_harness[row.harness] == 1
            else f"{str(row.harness).capitalize()} / {row.model}"
        )
        for row in condition_details.itertuples(index=False)
    }
    y = np.arange(len(task_order), dtype=float)
    palette = {
        "codex": "#426FC4",
        "copilot": "#F2D66B",
        "opencode": "#DA8ABD",
        "pi": "#6BC2BE",
    }
    fallback_colors = [COLORS["blue"], COLORS["orange"], COLORS["green"], COLORS["purple"], COLORS["red"]]
    harness_colors = {
        harness: palette.get(harness, fallback_colors[index % len(fallback_colors)])
        for index, harness in enumerate(sorted(summary["harness"].unique()))
    }
    bar_height = 0.8 / max(len(condition_order), 1)
    offsets = (np.arange(len(condition_order)) - (len(condition_order) - 1) / 2) * bar_height
    maximum = float(summary["total_tokens"].max()) if summary["total_tokens"].notna().any() else 0.0
    figure_height = max(minimum_height, 2.4 + 0.52 * len(task_order))

    with _style():
        figure, axis = plt.subplots(figsize=(width, figure_height), constrained_layout=True)
        for index, condition in enumerate(condition_order):
            panel = (
                summary[summary["condition"] == condition]
                .set_index("task_id")
                .reindex(task_order)
            )
            values = panel["total_tokens"].to_numpy(dtype=float)
            valid = ~np.isnan(values)
            bars = axis.barh(
                y[valid] + offsets[index],
                values[valid],
                height=bar_height * 0.82,
                color=harness_colors[str(panel["harness"].dropna().iloc[0])],
                label=condition_labels[condition],
                zorder=3,
            )
            for bar, value in zip(bars, values[valid]):
                label = f"{value / 1_000_000:.2f}M" if value >= 100_000 else f"{value / 1_000:.1f}K"
                axis.annotate(
                    label,
                    (value, bar.get_y() + bar.get_height() / 2),
                    xytext=(5, 0),
                    textcoords="offset points",
                    va="center",
                    fontsize=8,
                    color=COLORS["dark"],
                )
        axis.set_yticks(y, labels)
        axis.invert_yaxis()
        axis.set_xlim(0, maximum * 1.14 if maximum else 1)
        axis.xaxis.set_major_formatter(mticker.FuncFormatter(lambda value, _: f"{value / 1_000_000:g}M"))
        axis.set_xlabel("total tokens used (input + output)")
        axis.set_ylabel("tasks")
        axis.set_title("Tokens used by agent for each task", loc="left", fontweight="bold", pad=56)
        axis.grid(axis="x", color=COLORS["light_gray"], linewidth=0.7)
        axis.set_axisbelow(True)
        if condition_order:
            axis.legend(
                frameon=False,
                loc="lower left",
                bbox_to_anchor=(0, 1.015),
                ncol=min(4, len(condition_order)),
                borderaxespad=0,
            )

    incomplete = summary[summary["token_observations"] < summary["attempts"]]
    warning = None
    if not incomplete.empty:
        warning = (
            f"{len(incomplete)} condition–task combination(s) have missing input or output token data; "
            "bars use attempts with both values."
        )
    return PlotResult(figure=figure, data=summary, warning=warning)


def harness_resource_usage(attempts: pd.DataFrame, width: float, height: float) -> PlotResult:
    """Compare per-task duration, token usage, and tool calls across conditions."""
    metrics = [
        ("duration_seconds", "Duration", "minutes", 1 / 60),
        ("total_input_tokens", "Input tokens", "tokens", 1),
        ("total_output_tokens", "Output tokens", "tokens", 1),
        ("total_tool_calls", "Tool calls", "calls", 1),
    ]
    conditions = _ordered_conditions(attempts)
    records: list[dict[str, object]] = []
    for condition in conditions:
        group = attempts[attempts["condition"] == condition]
        for column, label, unit, scale in metrics:
            metric_values = group[column]
            if column == "duration_seconds":
                metric_values = metric_values.where(~group["timed_out"], 20 * 60)
            values = metric_values.dropna().astype(float)
            records.append(
                {
                    "condition": condition,
                    "harness": group["harness"].iloc[0],
                    "model": group["model"].iloc[0],
                    "metric": column,
                    "metric_label": label,
                    "unit": unit,
                    "attempted_tasks": len(group),
                    "timed_out_attempts": int(group["timed_out"].sum()),
                    "observations": len(values),
                    "total": values.sum() * scale if len(values) else np.nan,
                    "median": values.median() * scale if len(values) else np.nan,
                    "q1": values.quantile(0.25) * scale if len(values) else np.nan,
                    "q3": values.quantile(0.75) * scale if len(values) else np.nan,
                }
            )
    summary = pd.DataFrame.from_records(records)
    y = np.arange(len(conditions))

    with _style():
        figure, axes = plt.subplots(
            1,
            len(metrics),
            figsize=(width, max(height, 1.8 + 0.55 * len(conditions))),
            constrained_layout=True,
            sharey=True,
        )
        for axis, (column, label, unit, _) in zip(axes, metrics):
            panel = summary[summary["metric"] == column].set_index("condition").reindex(conditions)
            medians = panel["median"].to_numpy(dtype=float)
            q1 = panel["q1"].to_numpy(dtype=float)
            q3 = panel["q3"].to_numpy(dtype=float)
            valid = ~np.isnan(medians)
            axis.errorbar(
                medians[valid],
                y[valid],
                xerr=np.vstack((medians[valid] - q1[valid], q3[valid] - medians[valid])),
                fmt="o",
                color=COLORS["blue"],
                ecolor=COLORS["dark"],
                elinewidth=1.2,
                capsize=3,
                markersize=6,
                zorder=3,
            )
            for median, position in zip(medians[valid], y[valid]):
                value_label = f"{median:.1f}" if column == "duration_seconds" else f"{median:,.0f}"
                axis.annotate(
                    value_label,
                    (median, position),
                    xytext=(6, 6),
                    textcoords="offset points",
                    fontsize=8,
                    color=COLORS["dark"],
                )
            if column == "duration_seconds":
                axis.set_xlim(0, 20)
                axis.set_xticks(np.arange(0, 21, 5))
            else:
                axis.set_xlim(left=0)
            if column in {"total_input_tokens", "total_output_tokens"}:
                axis.ticklabel_format(axis="x", style="sci", scilimits=(0, 0))
            axis.set_xlabel(f"Median per attempted task ({unit})")
            panel_title = "Duration (timeouts = 20 min)" if column == "duration_seconds" else label
            axis.set_title(panel_title, loc="left", fontweight="bold")
            axis.grid(axis="x", color=COLORS["light_gray"], linewidth=0.7)
            axis.set_axisbelow(True)
        axes[0].set_yticks(y, conditions)
        axes[0].invert_yaxis()
        axes[0].set_ylabel("Harness / model")
        figure.suptitle("Per-task resource usage (median and IQR)", fontweight="bold")

    incomplete = summary[summary["observations"] < summary["attempted_tasks"]]
    warning = None
    if not incomplete.empty:
        affected = incomplete[["condition", "metric_label"]].drop_duplicates()
        warning = (
            f"{len(affected)} condition–metric combination(s) have missing observations; "
            "summaries use available attempts."
        )
    return PlotResult(figure=figure, data=summary, warning=warning)


def tool_calls_by_type(attempts: pd.DataFrame, width: float, height: float) -> PlotResult:
    """Plot reported tool-call categories per attempted task for each agent."""
    categories = (
        ("read", "tool_calls_read"),
        ("shell", "tool_calls_shell"),
        ("patch", "tool_calls_patch"),
        ("other", "tool_calls_other"),
    )
    agents = _ordered_conditions(attempts)
    records: list[dict[str, object]] = []
    for agent in agents:
        group = attempts[attempts["condition"] == agent]
        attempted_tasks = len(group)
        for category, column in categories:
            values = group[column].dropna().astype(float)
            total_calls = values.sum() if len(values) else np.nan
            records.append(
                {
                    "agent": agent,
                    "harness": group["harness"].iloc[0],
                    "model": group["model"].iloc[0],
                    "reported_tool_call_category": category,
                    "attempted_tasks": attempted_tasks,
                    "reported_attempts": len(values),
                    "total_reported_calls": total_calls,
                    "calls_per_attempted_task": (
                        total_calls / attempted_tasks
                        if attempted_tasks and pd.notna(total_calls)
                        else np.nan
                    ),
                }
            )
    summary = pd.DataFrame.from_records(records)

    category_names = [category for category, _ in categories]
    y = np.arange(len(category_names), dtype=float)
    palette = [
        COLORS["blue"],
        COLORS["orange"],
        COLORS["green"],
        COLORS["purple"],
        COLORS["red"],
        COLORS["sky"],
    ]
    markers = ["o", "s", "^", "D", "P", "X"]

    with _style():
        figure, axis = plt.subplots(
            figsize=(width, max(height, 4.2)),
            constrained_layout=True,
        )
        axis.hlines(
            y,
            xmin=0,
            xmax=1,
            transform=axis.get_yaxis_transform(),
            color=COLORS["light_gray"],
            linewidth=1,
            zorder=0,
        )
        for index, agent in enumerate(agents):
            panel = (
                summary[summary["agent"] == agent]
                .set_index("reported_tool_call_category")
                .reindex(category_names)
            )
            values = panel["calls_per_attempted_task"].to_numpy(dtype=float)
            valid = ~np.isnan(values)
            axis.scatter(
                values[valid],
                y[valid],
                s=82,
                color=palette[index % len(palette)],
                marker=markers[index % len(markers)],
                edgecolor="white",
                linewidth=0.8,
                label=agent,
                zorder=3,
            )
        axis.set_yticks(y, category_names)
        axis.invert_yaxis()
        axis.set_xlim(left=0)
        axis.set_xlabel("Calls per attempted task")
        axis.set_ylabel("Reported tool-call category")
        axis.set_title(
            "Reported tool-call counts by type",
            loc="left",
            fontweight="bold",
            pad=58,
        )
        axis.grid(axis="x", color=COLORS["light_gray"], linewidth=0.7)
        axis.set_axisbelow(True)
        if agents:
            axis.legend(
                frameon=False,
                loc="lower left",
                bbox_to_anchor=(0, 1.015),
                ncol=min(4, len(agents)),
                borderaxespad=0,
            )

    incomplete = summary[summary["reported_attempts"] < summary["attempted_tasks"]]
    warning = None
    if not incomplete.empty:
        affected_agents = incomplete["agent"].nunique()
        warning = (
            f"{affected_agents} agent(s) have attempts without reported tool-call categories; "
            "rates use all attempted tasks as the denominator."
        )
    return PlotResult(figure=figure, data=summary, warning=warning)


def per_attempt_tool_call_composition(
    attempts: pd.DataFrame, width: float, height: float
) -> PlotResult:
    """Plot each tool type's share of an attempt, split by repair outcome.

    Every point is one attempt's reported count for a tool type divided by that
    attempt's total tool calls.  Boxes show the median and interquartile range
    of those percentages across tasks; they do not pool tool calls across
    attempts.
    """
    categories = (
        ("read", "tool_calls_read"),
        ("shell_command", "tool_calls_shell"),
        ("patch", "tool_calls_patch"),
        ("other", "tool_calls_other"),
    )
    outcomes = (
        (True, "Successful attempts"),
        (False, "Unsuccessful attempts"),
    )
    conditions = _ordered_conditions(attempts)
    condition_details = attempts[["condition", "harness", "model"]].drop_duplicates("condition")
    conditions_per_harness = condition_details.groupby("harness", observed=True)["condition"].nunique()
    condition_labels = {
        row.condition: (
            str(row.harness).capitalize()
            if conditions_per_harness[row.harness] == 1
            else f"{str(row.harness).capitalize()} / {row.model}"
        )
        for row in condition_details.itertuples(index=False)
    }
    harness_palette = {
        "codex": "#426FC4",
        "copilot": "#F2D66B",
        "opencode": "#DA8ABD",
        "pi": "#6BC2BE",
    }
    fallback_colors = [COLORS["blue"], COLORS["orange"], COLORS["green"], COLORS["purple"], COLORS["red"]]
    condition_colors = {
        condition: harness_palette.get(
            str(condition_details.set_index("condition").loc[condition, "harness"]),
            fallback_colors[index % len(fallback_colors)],
        )
        for index, condition in enumerate(conditions)
    }

    records: list[dict[str, object]] = []
    for row in attempts.itertuples(index=False):
        total = pd.to_numeric(pd.Series([row.total_tool_calls]), errors="coerce").iloc[0]
        for tool_call_type, column in categories:
            count = pd.to_numeric(pd.Series([getattr(row, column)]), errors="coerce").iloc[0]
            if pd.isna(total) or total <= 0 or pd.isna(count):
                continue
            records.append(
                {
                    "entry_id": row.entry_id,
                    "run_id": row.run_id,
                    "condition": row.condition,
                    "harness": row.harness,
                    "model": row.model,
                    "task_id": row.task_id,
                    "strict_success": row.strict_success,
                    "outcome": "Successful attempts" if row.strict_success else "Unsuccessful attempts",
                    "tool_call_type": tool_call_type,
                    "total_tool_calls": float(total),
                    "tool_call_count": float(count),
                    "tool_call_share_pct": float(count / total * 100),
                }
            )
    columns = [
        "entry_id",
        "run_id",
        "condition",
        "harness",
        "model",
        "task_id",
        "strict_success",
        "outcome",
        "tool_call_type",
        "total_tool_calls",
        "tool_call_count",
        "tool_call_share_pct",
    ]
    shares = pd.DataFrame.from_records(records, columns=columns)
    category_names = [category for category, _ in categories]
    y = np.arange(len(category_names), dtype=float)
    figure_height = max(height, 6.0)

    with _style():
        figure, axes = plt.subplots(
            1,
            len(outcomes),
            figsize=(width, figure_height),
            constrained_layout=True,
            sharex=True,
            sharey=True,
            squeeze=False,
        )
        # Keep a header band for the figure title and shared condition legend.
        figure.get_layout_engine().set(rect=(0, 0, 1, 0.84))
        condition_width = min(0.16, 0.7 / max(len(conditions), 1))
        offsets = (np.arange(len(conditions)) - (len(conditions) - 1) / 2) * condition_width
        jitter_rng = np.random.default_rng(0)
        for axis, (successful, outcome_label) in zip(axes[0], outcomes):
            outcome_data = shares[shares["strict_success"] == successful]
            attempt_count = int((attempts["strict_success"] == successful).sum())
            for condition_index, condition in enumerate(conditions):
                condition_data = outcome_data[outcome_data["condition"] == condition]
                color = condition_colors[condition]
                for category_index, category in enumerate(category_names):
                    values = condition_data.loc[
                        condition_data["tool_call_type"] == category, "tool_call_share_pct"
                    ].to_numpy(dtype=float)
                    if not len(values):
                        continue
                    position = y[category_index] + offsets[condition_index]
                    box = axis.boxplot(
                        values,
                        vert=False,
                        positions=[position],
                        widths=condition_width * 0.78,
                        whis=(0, 100),
                        showfliers=False,
                        patch_artist=True,
                        manage_ticks=False,
                        zorder=2,
                    )
                    for patch in box["boxes"]:
                        patch.set(facecolor=color, edgecolor=color, alpha=0.62, linewidth=1.1)
                    for key in ("whiskers", "caps", "medians"):
                        for artist in box[key]:
                            artist.set(color=color, linewidth=1.1 if key != "medians" else 1.5)
                    point_y = position + jitter_rng.uniform(-condition_width * 0.18, condition_width * 0.18, len(values))
                    axis.scatter(
                        values,
                        point_y,
                        s=24,
                        color=color,
                        alpha=0.45,
                        edgecolor="none",
                        zorder=3,
                    )
            axis.set_title(f"{outcome_label} · {attempt_count} attempts", loc="left", fontweight="bold")
            axis.set_xlim(0, 100)
            axis.xaxis.set_major_formatter(mticker.PercentFormatter(xmax=100, decimals=0))
            axis.set_xlabel("Tool-call share of attempt (%)")
            axis.grid(axis="x", color=COLORS["light_gray"], linewidth=0.7)
            axis.set_axisbelow(True)
        axes[0, 0].set_yticks(y, category_names)
        axes[0, 0].invert_yaxis()
        axes[0, 0].set_ylabel("Tool-call type")
        figure.suptitle("Per-attempt tool-call composition", x=0.01, ha="left", fontweight="bold")
        figure.text(
            0.01,
            0.88,
            "Each point is one attempt; boxes show the median and IQR of each tool type's share across tasks.",
            ha="left",
            va="top",
            fontsize=9,
            color=COLORS["dark"],
        )
        if conditions:
            figure.legend(
                handles=[Patch(facecolor=condition_colors[condition], label=condition_labels[condition]) for condition in conditions],
                frameon=False,
                loc="upper left",
                bbox_to_anchor=(0.01, 0.95),
                ncol=min(4, len(conditions)),
            )

    expected_values = len(attempts) * len(categories)
    warning = None
    if len(shares) < expected_values:
        warning = (
            f"{expected_values - len(shares)} attempt–tool-type value(s) were omitted because the total or "
            "reported tool-call count was missing, or the attempt made no tool calls."
        )
    return PlotResult(figure=figure, data=shares, warning=warning)


def token_usage_by_outcome(attempts: pd.DataFrame, width: float, height: float) -> PlotResult:
    """Compare input and output token usage for successful and unsuccessful attempts."""
    metrics = (
        ("total_input_tokens", "Input tokens"),
        ("total_output_tokens", "Output tokens"),
    )
    outcomes = (
        (True, "Successful attempt", COLORS["green"], "o", -0.14),
        (False, "Unsuccessful attempt", COLORS["red"], "s", 0.14),
    )
    conditions = _ordered_conditions(attempts)
    records: list[dict[str, object]] = []

    for condition in conditions:
        condition_attempts = attempts[attempts["condition"] == condition]
        for success, outcome_label, _, _, _ in outcomes:
            outcome_attempts = condition_attempts[condition_attempts["strict_success"] == success]
            for metric, metric_label in metrics:
                values = pd.to_numeric(outcome_attempts[metric], errors="coerce").dropna()
                records.append(
                    {
                        "condition": condition,
                        "harness": condition_attempts["harness"].iloc[0],
                        "model": condition_attempts["model"].iloc[0],
                        "successful": success,
                        "outcome": outcome_label,
                        "metric": metric,
                        "metric_label": metric_label,
                        "attempts": len(outcome_attempts),
                        "observations": len(values),
                        "total": values.sum() if len(values) else np.nan,
                        "median": values.median() if len(values) else np.nan,
                        "q1": values.quantile(0.25) if len(values) else np.nan,
                        "q3": values.quantile(0.75) if len(values) else np.nan,
                    }
                )

    summary = pd.DataFrame.from_records(records)
    y = np.arange(len(conditions))
    with _style():
        figure, axes = plt.subplots(
            1,
            len(metrics),
            figsize=(width, max(height, 1.8 + 0.62 * len(conditions))),
            constrained_layout=True,
            sharey=True,
        )
        for axis, (metric, metric_label) in zip(axes, metrics):
            for success, outcome_label, color, marker, offset in outcomes:
                panel = (
                    summary[(summary["metric"] == metric) & (summary["successful"] == success)]
                    .set_index("condition")
                    .reindex(conditions)
                )
                medians = panel["median"].to_numpy(dtype=float)
                q1 = panel["q1"].to_numpy(dtype=float)
                q3 = panel["q3"].to_numpy(dtype=float)
                valid = ~np.isnan(medians)
                axis.errorbar(
                    medians[valid],
                    y[valid] + offset,
                    xerr=np.vstack((medians[valid] - q1[valid], q3[valid] - medians[valid])),
                    fmt=marker,
                    color=color,
                    markeredgecolor=COLORS["dark"],
                    markeredgewidth=0.4,
                    ecolor=color,
                    elinewidth=1.2,
                    capsize=3,
                    markersize=6,
                    label=outcome_label,
                    zorder=3,
                )
            axis.set_xlim(left=0)
            axis.ticklabel_format(axis="x", style="sci", scilimits=(0, 0))
            axis.set_xlabel("Median per attempt (tokens)")
            axis.set_title(metric_label, loc="left", fontweight="bold")
            axis.grid(axis="x", color=COLORS["light_gray"], linewidth=0.7)
            axis.set_axisbelow(True)
        axes[0].set_yticks(y, conditions)
        axes[0].invert_yaxis()
        axes[0].set_ylabel("Harness / model")
        axes[-1].legend(frameon=False, loc="best")
        figure.suptitle("Token usage by proof-repair outcome (median and IQR)", fontweight="bold")

    incomplete = summary[summary["observations"] < summary["attempts"]]
    warning = None
    if not incomplete.empty:
        affected = incomplete[["condition", "outcome", "metric_label"]].drop_duplicates()
        warning = (
            f"{len(affected)} condition–outcome–metric combination(s) have missing observations; "
            "summaries use available attempts."
        )
    return PlotResult(figure=figure, data=summary, warning=warning)


def _has_complete_two_by_two(summary: pd.DataFrame) -> bool:
    """Return whether two harnesses evaluated each of two models."""
    cells = set(zip(summary["harness"], summary["model"]))
    for harnesses in itertools.combinations(summary["harness"].unique(), 2):
        for models in itertools.combinations(summary["model"].unique(), 2):
            if all((harness, model) in cells for harness in harnesses for model in models):
                return True
    return False


def harness_model_interaction(attempts: pd.DataFrame, width: float, height: float) -> PlotResult:
    """Plot repair rate for each observed harness and model combination."""
    summary = (
        attempts.groupby(["harness", "model", "condition"], observed=True)
        .agg(
            attempted_tasks=("task_id", "size"),
            valid_repairs=("strict_success", "sum"),
        )
        .reset_index()
    )
    summary["repair_rate"] = summary["valid_repairs"] / summary["attempted_tasks"]
    model_order = summary.groupby("model", observed=True)["repair_rate"].mean().sort_values().index.tolist()
    harnesses = sorted(summary["harness"].unique())
    palette = [COLORS["blue"], COLORS["orange"], COLORS["green"], COLORS["purple"]]
    markers = ["o", "s", "^", "D"]

    with _style():
        figure, axis = plt.subplots(figsize=(width, height), constrained_layout=True)
        x = np.arange(len(model_order))
        for index, harness in enumerate(harnesses):
            harness_summary = summary[summary["harness"] == harness].set_index("model")
            values = np.array(
                [
                    harness_summary.loc[model, "repair_rate"] * 100 if model in harness_summary.index else np.nan
                    for model in model_order
                ],
                dtype=float,
            )
            axis.plot(
                x,
                values,
                marker=markers[index % len(markers)],
                color=palette[index % len(palette)],
                linewidth=1.5,
                markersize=7,
                label=harness,
            )
            for position, value in zip(x, values):
                if not np.isnan(value):
                    axis.annotate(
                        f"{value:.0f}%",
                        (position, value),
                        xytext=(0, 7),
                        textcoords="offset points",
                        ha="center",
                        fontsize=8,
                    )
        axis.set_xticks(x, model_order, rotation=20, ha="right")
        axis.set_ylim(0, 100)
        axis.set_xlabel("Model (ordered by mean observed repair rate)")
        axis.set_ylabel("Valid repair rate (%)")
        axis.set_title("Harness × model proof-repair performance", loc="left", fontweight="bold")
        axis.grid(axis="y", color=COLORS["light_gray"], linewidth=0.7)
        axis.set_axisbelow(True)
        axis.legend(title="Harness", frameon=False)

    warning = None
    if not _has_complete_two_by_two(summary):
        warning = (
            "The selected data has no complete 2×2 harness–model subset; gaps are shown "
            "and the figure does not support an interaction estimate."
        )
    return PlotResult(figure=figure, data=summary, warning=warning)


def figure_bytes(figure: Figure, file_format: str) -> bytes:
    """Serialize a figure for one of the viewer's download buttons."""
    buffer = io.BytesIO()
    if file_format == "png":
        figure.savefig(buffer, format=file_format, bbox_inches="tight", dpi=300)
    else:
        figure.savefig(buffer, format=file_format, bbox_inches="tight")
    return buffer.getvalue()


def csv_bytes(data: pd.DataFrame) -> bytes:
    """Serialize a plot's source table as UTF-8 CSV."""
    return data.to_csv(index=False).encode("utf-8")
