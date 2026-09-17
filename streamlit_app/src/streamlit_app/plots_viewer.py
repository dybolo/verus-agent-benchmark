"""Render the interactive dashboard for comparing benchmark-run plots."""

from __future__ import annotations

import matplotlib.pyplot as plt
import pandas as pd
import streamlit as st

from streamlit_app.data import (
    cohort_attempts,
    discover_cohorts,
    flatten_runs,
    load_runs,
    load_task_metadata,
)
from streamlit_app.paths import app_data_path, repository_root
from streamlit_app.plots import (
    PlotResult,
    binned_success_curves,
    caterpillar,
    csv_bytes,
    difficulty_bubble_scatter,
    exclusive_solves_matrix,
    figure_bytes,
    harness_resource_usage,
    outcome_composition,
    quality_cost,
    task_normalized_harness_effect,
    token_usage_by_outcome,
    tokens_used_by_agent_for_each_task,
    tool_calls_by_type,
)


def render_plot(result: PlotResult, name: str) -> None:
    """Display a figure and provide downloads for it and its source data."""
    if result.warning:
        st.warning(result.warning)
    st.pyplot(result.figure, width="stretch")
    svg = figure_bytes(result.figure, "svg")
    pdf = figure_bytes(result.figure, "pdf")
    png = figure_bytes(result.figure, "png")
    data = csv_bytes(result.data)
    first, second, third, fourth = st.columns(4)
    first.download_button(
        "Download SVG",
        svg,
        file_name=f"{name}.svg",
        mime="image/svg+xml",
        key=f"{name}:svg",
        width="stretch",
    )
    second.download_button(
        "Download PDF",
        pdf,
        file_name=f"{name}.pdf",
        mime="application/pdf",
        key=f"{name}:pdf",
        width="stretch",
    )
    third.download_button(
        "Download PNG",
        png,
        file_name=f"{name}.png",
        mime="image/png",
        key=f"{name}:png",
        width="stretch",
    )
    fourth.download_button(
        "Download data",
        data,
        file_name=f"{name}.csv",
        mime="text/csv",
        key=f"{name}:csv",
        width="stretch",
    )
    plt.close(result.figure)


def nonempty_strings(series: pd.Series) -> list[str]:
    """Return sorted, non-empty string values from a pandas series."""
    return sorted(str(value) for value in series.dropna().unique() if str(value))


def main() -> None:
    """Load benchmark data and render the plots dashboard."""
    st.set_page_config(
        page_title="Thesis Evaluation Plots",
        page_icon="📊",
        layout="wide",
    )
    repo_root = repository_root()
    runs, run_errors = load_runs(repo_root / "runs")
    metadata, metadata_errors = load_task_metadata(
        app_data_path("task_metadata.csv"),
        [repo_root / "tasks", repo_root / "full_tasks"],
    )
    attempts = flatten_runs(runs, metadata)

    st.title("Thesis Evaluation Plot Dashboard")
    st.caption("Interactive, exportable analysis of the benchmark run JSON files")

    errors = [*run_errors, *metadata_errors]
    if errors:
        with st.expander(f"Data warnings ({len(errors)})"):
            for error in errors:
                st.warning(error)
    if attempts.empty:
        st.error("No task attempts were found in runs/*.json.")
        st.stop()

    cohorts = discover_cohorts(attempts)
    if not cohorts:
        st.error("No opencode or pi run cohorts were found.")
        st.stop()

    st.sidebar.header("Experiment selection")
    selected_cohort = st.sidebar.selectbox(
        "Task cohort",
        cohorts,
        index=0,
        format_func=lambda cohort: cohort.label,
        help="A cohort contains runs with exactly the same task IDs. The default is the largest cohort.",
    )
    selected = cohort_attempts(attempts, selected_cohort)
    conditions = sorted(selected["condition"].unique())
    chosen_conditions = st.sidebar.multiselect(
        "Harness / model conditions",
        conditions,
        default=conditions,
    )
    selected = selected[selected["condition"].isin(chosen_conditions)]
    if selected.empty:
        st.warning("Select at least one harness/model condition.")
        st.stop()

    st.sidebar.header("Task filters")
    proof_styles = nonempty_strings(selected["proof_style"])
    chosen_styles = st.sidebar.multiselect(
        "Proof styles",
        proof_styles,
        default=proof_styles,
    )
    if proof_styles:
        selected = selected[selected["proof_style"].isin(chosen_styles)]

    source_modules = nonempty_strings(selected["source_module"])
    chosen_modules = st.sidebar.multiselect(
        "Source modules",
        source_modules,
        default=[],
        placeholder="All source modules",
        help="Leave empty to include every source module.",
    )
    if chosen_modules:
        selected = selected[selected["source_module"].isin(chosen_modules)]

    tasks = sorted(selected["task_id"].unique())
    chosen_tasks = st.sidebar.multiselect(
        "Tasks",
        tasks,
        default=[],
        placeholder="All tasks",
        help="Leave empty to include every task remaining after the other filters.",
    )
    if chosen_tasks:
        selected = selected[selected["task_id"].isin(chosen_tasks)]
    if selected.empty:
        st.warning("The task filters exclude every observation.")
        st.stop()

    st.sidebar.header("Figure settings")
    figure_width = st.sidebar.slider("Figure width (inches)", 7.0, 16.0, 11.0, 0.5)
    figure_height = st.sidebar.slider("Minimum figure height (inches)", 4.0, 12.0, 6.0, 0.5)
    cost_scale = st.sidebar.radio("Cost-axis scale", ["log", "linear"], horizontal=True)

    unmapped = selected[selected["proof_style"].isna()]["task_id"].unique()
    if len(unmapped):
        st.warning(
            f"{len(unmapped)} selected task(s) lack taxonomy metadata and will be omitted "
            "from taxonomy-dependent plots."
        )

    metric_columns = st.columns(4)
    metric_columns[0].metric("Cohort tasks", selected["task_id"].nunique())
    metric_columns[1].metric("Conditions", selected["condition"].nunique())
    metric_columns[2].metric("Attempts", len(selected))
    metric_columns[3].metric("Valid repairs", int(selected["strict_success"].sum()))

    question_one, question_two, question_three, _question_four = st.tabs(
        [
            "1 · Overall performance",
            "2 · Difficult proof patterns",
            "3 · Harness effects",
            "4 · Model × harness",
        ]
    )

    with question_one:
        st.header("Can current coding agents repair incomplete concurrent Verus proofs?")
        render_plot(
            outcome_composition(selected, figure_width, figure_height),
            "outcome-composition",
        )
        st.divider()
        render_plot(
            quality_cost(selected, figure_width, figure_height, cost_scale),
            "quality-vs-cost",
        )

    with question_two:
        st.header("Which proof patterns and verification constructs are most difficult?")
        render_plot(
            difficulty_bubble_scatter(selected, figure_width, figure_height),
            "task-difficulty-bubble-scatter",
        )
        st.divider()
        render_plot(
            binned_success_curves(selected, figure_width, figure_height),
            "binned-success-curves",
        )
        st.divider()
        render_plot(
            caterpillar(selected, figure_width, figure_height),
            "hierarchical-caterpillar",
        )

    with question_three:
        st.header("How does agent harness design affect proof-repair performance?")
        render_plot(
            tokens_used_by_agent_for_each_task(selected, figure_width, figure_height),
            "tokens-used-by-agent-for-each-task",
        )
        st.divider()
        render_plot(
            task_normalized_harness_effect(selected, figure_width, figure_height),
            "task-normalized-harness-effect",
        )
        st.divider()
        render_plot(
            exclusive_solves_matrix(selected, figure_width, figure_height),
            "harness-exclusive-solves",
        )
        st.divider()
        render_plot(
            harness_resource_usage(selected, figure_width, figure_height),
            "harness-resource-usage",
        )
        st.divider()
        st.caption(
            "These are reported tool-call categories. Codex performs many reads through shell commands, "
            "while other harnesses expose dedicated read tools."
        )
        render_plot(
            tool_calls_by_type(selected, figure_width, figure_height),
            "reported-tool-calls-by-type",
        )
        st.divider()
        render_plot(
            token_usage_by_outcome(selected, figure_width, figure_height),
            "token-usage-by-outcome",
        )


if __name__ == "__main__":
    main()
