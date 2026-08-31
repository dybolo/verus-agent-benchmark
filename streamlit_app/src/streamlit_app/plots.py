"""Build exportable matplotlib figures from the flattened benchmark-attempt table."""

from __future__ import annotations

import io
import itertools
from contextlib import AbstractContextManager
from dataclasses import dataclass

import matplotlib as mpl
import matplotlib.colors as mcolors
import matplotlib.pyplot as plt
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
        counts.rename_axis(index="condition", columns="outcome")
        .stack(future_stack=True)
        .rename("count")
        .reset_index()
    )
    export["percentage"] = export.apply(
        lambda row: percentages.loc[row["condition"], row["outcome"]], axis=1
    )

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


def quality_cost(
    attempts: pd.DataFrame, width: float, height: float, cost_scale: str = "log"
) -> PlotResult:
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
            [COLORS["blue"], COLORS["orange"], COLORS["green"], COLORS["purple"], COLORS["red"]],
        )
    }

    frontier = plotted.sort_values(
        ["mean_cost_per_attempt_usd", "repair_rate"], ascending=[True, False]
    )
    frontier = frontier[
        frontier["repair_rate"]
        > frontier["repair_rate"].cummax().shift(1, fill_value=-np.inf)
    ]

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
        proof
        for proof in ("atomic-operation", "tokenized_state_machine!")
        if proof in set(summary["proof_style"])
    ]
    proof_order.extend(sorted(set(summary["proof_style"]) - set(proof_order)))
    if not proof_order:
        with _style():
            figure, axis = plt.subplots(figsize=(width, minimum_height))
            axis.text(0.5, 0.5, "No tasks with metadata", ha="center", va="center")
            axis.axis("off")
        return PlotResult(figure, summary, "No selected tasks have proof-style metadata.")

    rows_per_panel = [len(summary[summary["proof_style"] == proof]) for proof in proof_order]
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
            y = np.arange(len(panel))
            labels: list[str] = []
            previous_module = None
            for _, row in panel.iterrows():
                prefix = f"{row['source_module']}  ›  " if row["source_module"] != previous_module else "    "
                labels.append(prefix + row["task_id"])
                previous_module = row["source_module"]
            axis.hlines(y, 0, panel["solve_rate"], color=COLORS["light_gray"], linewidth=1.5)
            axis.scatter(
                panel["solve_rate"],
                y,
                color=COLORS["blue"] if proof_style == "atomic-operation" else COLORS["orange"],
                edgecolor=COLORS["dark"],
                linewidth=0.4,
                s=38,
                zorder=3,
            )
            for position, (_, row) in enumerate(panel.iterrows()):
                axis.annotate(
                    f"{int(row['solved'])}/{int(row['observed'])}",
                    (row["solve_rate"], position),
                    xytext=(5, 0),
                    textcoords="offset points",
                    va="center",
                    fontsize=8,
                )
            axis.set_yticks(y, labels)
            axis.invert_yaxis()
            axis.set_xlim(-0.02, 1.14)
            axis.set_xticks(np.linspace(0, 1, 5), ["0", "25", "50", "75", "100"])
            axis.set_xlabel("Valid repair rate (%)")
            axis.set_title(proof_style, loc="left", fontweight="bold")
            axis.grid(axis="x", color=COLORS["light_gray"], linewidth=0.7)
            axis.set_axisbelow(True)
        figure.suptitle("Task difficulty by proof style and source module", fontweight="bold")
    return PlotResult(figure=figure, data=summary)


def harness_comparisons(attempts: pd.DataFrame) -> pd.DataFrame:
    """Build task-level same-model comparisons between harnesses."""
    metadata = (
        attempts[["task_id", "proof_style", "source_module"]]
        .drop_duplicates("task_id")
        .set_index("task_id")
    )
    all_tasks = sorted(attempts["task_id"].unique())
    records: list[dict[str, object]] = []
    for model, model_attempts in attempts.groupby("model", observed=True):
        harnesses = sorted(model_attempts["harness"].unique())
        for harness_a, harness_b in itertools.combinations(harnesses, 2):
            success_a = (
                model_attempts[model_attempts["harness"] == harness_a]
                .set_index("task_id")["strict_success"]
                .to_dict()
            )
            success_b = (
                model_attempts[model_attempts["harness"] == harness_b]
                .set_index("task_id")["strict_success"]
                .to_dict()
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
            axis.text(0.5, 0.5, "No same-model harness pair is available", ha="center", va="center")
            axis.axis("off")
        return PlotResult(
            figure,
            comparison_data,
            "Select at least two harnesses that evaluated the same model.",
        )

    ordered_tasks = (
        comparison_data[["task_id", "proof_style", "source_module"]]
        .drop_duplicates("task_id")
        .sort_values(["proof_style", "source_module", "task_id"], na_position="last")
        ["task_id"]
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
        labels = {"Both fail": "F", "Disagreement": "·", "Both pass": "P", "Missing": "×"}
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


def disagreement_matrix(
    comparison_data: pd.DataFrame, width: float, minimum_height: float
) -> PlotResult:
    """Render directional differences between same-model harness results."""
    return _matrix(comparison_data, "disagreement", width, minimum_height)


def agreement_matrix(
    comparison_data: pd.DataFrame, width: float, minimum_height: float
) -> PlotResult:
    """Render matching and non-matching same-model harness results."""
    return _matrix(comparison_data, "agreement", width, minimum_height)


def exclusive_solves_matrix(
    attempts: pd.DataFrame, width: float, minimum_height: float
) -> PlotResult:
    """Plot task outcomes and highlight solves unique to one same-model harness."""
    comparable_models = [
        model
        for model, group in attempts.groupby("model", observed=True)
        if group["harness"].nunique() >= 2
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
            lambda row: str(row[row.fillna(False).astype(bool)].index[0])
            if row.fillna(False).sum() == 1
            else None,
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
            axis.text(0.5, 0.5, "No same-model harness comparison is available", ha="center", va="center")
            axis.axis("off")
        return PlotResult(
            figure,
            export,
            "Select at least two harnesses that evaluated the same model.",
        )

    total_rows = sum(len(panel) for _, panel, _ in panels)
    figure_height = max(minimum_height, 1.8 + 0.25 * total_rows)
    status_order = ["Failed", "Shared solve", "Exclusive solve", "Missing"]
    status_colors = [COLORS["light_gray"], COLORS["green"], COLORS["blue"], COLORS["gray"]]
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
            handles=[
                Patch(facecolor=color, label=status)
                for color, status in zip(status_colors, status_order)
            ],
            frameon=False,
            loc="upper center",
            bbox_to_anchor=(0.5, -0.12),
            ncol=4,
        )
    omitted_models = attempts["model"].nunique() - len(comparable_models)
    warning = None
    if omitted_models:
        warning = (
            f"{omitted_models} model(s) omitted because fewer than two harnesses "
            "evaluated that model."
        )
    return PlotResult(figure=figure, data=export, warning=warning)


def harness_resource_usage(
    attempts: pd.DataFrame, width: float, height: float
) -> PlotResult:
    """Compare per-task duration, turns, and tool calls across conditions."""
    metrics = [
        ("duration_seconds", "Duration", "minutes", 1 / 60),
        ("total_turns", "Turns", "turns", 1),
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
            3,
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
                axis.annotate(
                    f"{median:.1f}" if column == "duration_seconds" else f"{median:.0f}",
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


def _has_complete_two_by_two(summary: pd.DataFrame) -> bool:
    """Return whether two harnesses evaluated each of two models."""
    cells = set(zip(summary["harness"], summary["model"]))
    for harnesses in itertools.combinations(summary["harness"].unique(), 2):
        for models in itertools.combinations(summary["model"].unique(), 2):
            if all((harness, model) in cells for harness in harnesses for model in models):
                return True
    return False


def harness_model_interaction(
    attempts: pd.DataFrame, width: float, height: float
) -> PlotResult:
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
    model_order = (
        summary.groupby("model", observed=True)["repair_rate"]
        .mean()
        .sort_values()
        .index.tolist()
    )
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
                    harness_summary.loc[model, "repair_rate"] * 100
                    if model in harness_summary.index
                    else np.nan
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
