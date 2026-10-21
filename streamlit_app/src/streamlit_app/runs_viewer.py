"""Render the Streamlit interface for browsing run results and saved conversations."""

from __future__ import annotations

import difflib
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import streamlit as st

from streamlit_app.data import all_task_results, load_runs, numeric_total
from streamlit_app.paths import repository_root
from streamlit_app.sessions import (
    TimelineItem,
    load_jsonl,
    normalize_session,
    payload_text,
)

MAX_TOOL_OUTPUT_CHARS = 20_000


def timestamp_caption(item: TimelineItem) -> str:
    """Format an item's absolute timestamp and elapsed time for display."""
    parts: list[str] = []
    if item.timestamp:
        parts.append(item.timestamp.strftime("%Y-%m-%d %H:%M:%S UTC"))
    if item.elapsed_seconds is not None:
        parts.append(f"+{format_duration(item.elapsed_seconds)}")
    return " · ".join(parts)


def format_duration(value: Any) -> str:
    """Format a duration in seconds as a compact, human-readable string."""
    try:
        seconds = max(0, round(float(value)))
    except (TypeError, ValueError):
        return "—"
    hours, remainder = divmod(seconds, 3600)
    minutes, seconds = divmod(remainder, 60)
    if hours:
        return f"{hours}h {minutes:02d}m {seconds:02d}s"
    if minutes:
        return f"{minutes}m {seconds:02d}s"
    return f"{seconds}s"


def format_run_timestamp(value: str) -> str:
    """Format a timestamp-style run filename while leaving other values unchanged."""
    try:
        return datetime.strptime(value, "%Y%m%d_%H%M%S").replace(
            tzinfo=timezone.utc
        ).strftime("%Y-%m-%d %H:%M:%S")
    except ValueError:
        return value


def safe_repo_path(repo_root: Path, value: Any) -> Path | None:
    """Resolve a path only when it stays inside the benchmark repository."""
    if not isinstance(value, str) or not value:
        return None
    resolved_root = repo_root.resolve()
    candidate = Path(value)
    resolved = candidate.resolve() if candidate.is_absolute() else (resolved_root / candidate).resolve()
    try:
        resolved.relative_to(resolved_root)
    except ValueError:
        return None
    return resolved


def original_task_path(repo_root: Path, task_name: str) -> Path | None:
    """Find the original input for a regular or ``--full-file`` benchmark task."""
    for task_directory in ("tasks", "full_tasks"):
        candidate = safe_repo_path(repo_root, f"{task_directory}/{task_name}")
        if candidate is not None and candidate.is_file():
            return candidate
    return None


def summarize_run(run: dict[str, Any]) -> dict[str, Any]:
    """Build the one-row summary displayed in the all-runs table."""
    rows = all_task_results(run)
    return {
        "Run": format_run_timestamp(str(run.get("timestamp", ""))),
        "Agents": ", ".join(run.get("agents", {}).keys()),
        "Tasks": len(rows),
        "Verus passed": sum(result.get("verus_passed") is True for _, _, result in rows),
        "Cheat check passed": sum(result.get("cheat_checker_passed") is True for _, _, result in rows),
        "Timed out": sum(result.get("timed_out") is True for _, _, result in rows),
        "Cost": f"${numeric_total(rows, 'total_costs'):.2f}",
        "Duration": format_duration(numeric_total(rows, "duration_seconds")),
    }


def result_status(result: dict[str, Any]) -> str:
    """Return the viewer status for one task result."""
    if result.get("timed_out") is True:
        return "Timed out"
    if result.get("verus_passed") is True and result.get("cheat_checker_passed") is True:
        return "Passed"
    return "Failed"


def status_label(value: Any) -> str:
    """Return a labelled pass/fail/unknown indicator for a boolean result field."""
    if value is True:
        return "✅ Passed"
    if value is False:
        return "❌ Failed"
    return "— Unknown"


def render_payload(label: str, value: Any, show_full: bool) -> None:
    """Render a tool payload, shortening it unless full output is requested."""
    text = payload_text(value)
    if not text:
        return
    st.markdown(f"**{label}**")
    if not show_full and len(text) > MAX_TOOL_OUTPUT_CHARS:
        st.code(text[:MAX_TOOL_OUTPUT_CHARS])
        st.caption(
            f"Output shortened to {MAX_TOOL_OUTPUT_CHARS:,} characters. "
            "Enable ‘Show full tool outputs’ above to render all of it."
        )
    else:
        st.code(text)


def render_timeline_item(item: TimelineItem, show_thinking: bool, show_full: bool) -> None:
    """Render one normalized session item in the conversation view."""
    caption = timestamp_caption(item)
    if item.kind == "message":
        role = item.role if item.role in {"user", "assistant"} else "assistant"
        avatar = None if item.role in {"user", "assistant"} else "⚙️"
        with st.chat_message(role, avatar=avatar):
            if caption:
                st.caption(caption)
            if item.body:
                st.markdown(item.body)
            elif not item.thinking:
                st.caption("Empty message")
            if show_thinking and item.thinking:
                with st.expander("Reasoning"):
                    st.markdown(item.thinking)
        return
    status_icon = {"completed": "✅", "error": "❌"}.get(item.status or "", "")
    label = " ".join(part for part in [status_icon, item.title, f"· {caption}" if caption else ""] if part)
    with st.expander(label):
        if item.body:
            st.markdown(item.body)
        render_payload("Input", item.input, show_full)
        render_payload("Output", item.output, show_full)
        if item.details is not None and not item.body:
            render_payload("Details", item.details, show_full)


def render_sidebar_run_summary(run: dict[str, Any], agent_name: str) -> None:
    """Render aggregate task counts and costs for the selected agent."""
    rows = [row for row in all_task_results(run) if row[0] == agent_name]
    total = len(rows)
    passed = sum(result_status(result) == "Passed" for _, _, result in rows)
    failed = sum(result_status(result) == "Failed" for _, _, result in rows)
    verus_passed = sum(result.get("verus_passed") is True for _, _, result in rows)
    cheat_passed = sum(result.get("cheat_checker_passed") is True for _, _, result in rows)
    timed_out = sum(result.get("timed_out") is True for _, _, result in rows)
    st.sidebar.subheader("Run summary")
    first, second = st.sidebar.columns(2)
    first.metric("Tasks", total)
    second.metric("Passed", passed)
    first.metric("Failed", failed)
    second.metric("Timed out", timed_out)
    first.metric("Verus", f"{verus_passed}/{total}")
    second.metric("Cheat check", f"{cheat_passed}/{total}")
    st.sidebar.caption(
        f"Cost: ${numeric_total(rows, 'total_costs'):.2f} · "
        f"Duration: {format_duration(numeric_total(rows, 'duration_seconds'))}"
    )


def task_option_label(task_name: str, result: dict[str, Any]) -> str:
    """Return the labelled task selector entry for one task result."""
    status = result_status(result)
    icon = {"Passed": "✅", "Failed": "❌", "Timed out": "⏱️"}[status]
    return f"{icon} {task_name}"


def render_task_metrics(result: dict[str, Any]) -> None:
    """Render the status and resource metrics for the selected task."""
    metrics = st.columns(6)
    metrics[0].metric("Verus", status_label(result.get("verus_passed")))
    metrics[1].metric("Cheat check", status_label(result.get("cheat_checker_passed")))
    metrics[2].metric("Timed out", "Yes" if result.get("timed_out") else "No")
    metrics[3].metric("Cost", f"${float(result.get('total_costs') or 0):.4f}")
    metrics[4].metric("Turns / tools", f"{result.get('total_turns', 0)} / {result.get('total_tool_calls', 0)}")
    metrics[5].metric("Duration", format_duration(result.get("duration_seconds")))


def render_conversation(repo_root: Path, agent_name: str, result: dict[str, Any]) -> None:
    """Load, filter, and display the selected task's saved conversation."""
    session_path = safe_repo_path(repo_root, result.get("session_file"))
    if session_path is None:
        st.warning("This result does not contain a valid session file path.")
        return
    if not session_path.is_file():
        st.warning(f"Session file is missing: {session_path.relative_to(repo_root)}")
        return

    events, errors = load_jsonl(session_path)
    for error in errors:
        st.warning(error)
    items = normalize_session(events, agent_name)

    first, second, third = st.columns([2, 2, 1])
    query = first.text_input(
        "Search conversation", placeholder="Message, tool, command, error…"
    )
    visible_kinds = second.multiselect(
        "Show",
        ["Messages", "Tools", "Events"],
        default=["Messages", "Tools", "Events"],
    )
    show_thinking = third.toggle("Show reasoning", value=True)
    show_system = st.toggle("Show system messages", value=False)
    show_full = st.toggle("Show full tool outputs", value=False)

    kind_names = {"message": "Messages", "tool": "Tools", "event": "Events"}
    query_lower = query.strip().lower()
    visible_items = [
        item
        for item in items
        if kind_names.get(item.kind) in visible_kinds
        and (show_system or item.role != "system")
        and (not query_lower or query_lower in item.searchable_text())
    ]
    st.caption(
        f"Showing {len(visible_items)} of {len(items)} timeline items · "
        f"{session_path.relative_to(repo_root)}"
    )
    if not visible_items:
        st.info("No conversation items match the current filters.")
        return
    for item in visible_items:
        render_timeline_item(item, show_thinking=show_thinking, show_full=show_full)


def render_solution(repo_root: Path, task_name: str, result: dict[str, Any]) -> None:
    """Render a generated solution alongside its original task and unified diff."""
    solution_path = safe_repo_path(repo_root, result.get("solution_file"))
    if solution_path is None or not solution_path.is_file():
        message = (
            "The task timed out and no solution file was produced."
            if result.get("timed_out")
            else "No solution file is available for this task."
        )
        st.warning(message)
        return

    original_path = original_task_path(repo_root, task_name)
    st.caption(str(solution_path.relative_to(repo_root)))
    view = st.radio(
        "Source view", ["Diff", "Original", "Solution"], horizontal=True,
        key="source_view",
    )
    if view == "Original" and original_path is not None:
        try:
            original = original_path.read_text(errors="replace")
        except OSError as error:
            st.error(f"Could not read the original task: {error}")
            return
        st.caption(str(original_path.relative_to(repo_root)))
        st.code(original, language="rust", line_numbers=True)
        return

    try:
        solution = solution_path.read_text(errors="replace")
    except OSError as error:
        st.error(f"Could not read the solution: {error}")
        return

    if view == "Solution":
        st.code(solution, language="rust", line_numbers=True)
        return

    if original_path is None:
        st.info("The original task file is no longer present. Showing the solution only.")
        st.code(solution, language="rust", line_numbers=True)
        return

    try:
        original = original_path.read_text(errors="replace")
    except OSError as error:
        st.warning(f"Could not read the original task: {error}. Showing the solution only.")
        st.code(solution, language="rust", line_numbers=True)
        return

    diff = "".join(
        difflib.unified_diff(
            original.splitlines(keepends=True),
            solution.splitlines(keepends=True),
            fromfile=str(original_path.relative_to(repo_root)),
            tofile=str(solution_path.relative_to(repo_root)),
        )
    )
    if diff:
        st.code(diff, language="diff", line_numbers=True)
    else:
        st.success("The original and solution files are identical.")


def main() -> None:
    """Load benchmark runs and render the run explorer."""
    st.set_page_config(page_title="Benchmark Run Explorer", page_icon="🧪", layout="wide")
    repo_root = repository_root()
    runs_dir = repo_root / "runs"
    st.title("Benchmark Run Explorer")
    st.caption(f"Reading benchmark artifacts from {repo_root}")
    if not runs_dir.is_dir():
        st.error("No runs/ directory was found in the benchmark repository.")
        st.stop()

    runs, run_errors = load_runs(runs_dir)
    for error in run_errors:
        st.warning(error)
    if not runs:
        st.info("No valid run JSON files were found in runs/.")
        st.stop()

    run_query = st.sidebar.text_input("Filter runs", placeholder="Timestamp or agent/model")
    run_query_lower = run_query.strip().lower()
    filtered_runs = [
        run
        for run in runs
        if not run_query_lower
        or run_query_lower in str(run.get("timestamp", "")).lower()
        or run_query_lower in " ".join(run.get("agents", {}).keys()).lower()
    ]
    if not filtered_runs:
        st.sidebar.warning("No runs match the current filter.")
        st.stop()

    selected_run = st.sidebar.selectbox(
        "Run",
        filtered_runs,
        format_func=lambda run: format_run_timestamp(str(run.get("timestamp", "Unknown"))),
    )
    agent_names = sorted(selected_run.get("agents", {}).keys())
    if not agent_names:
        st.sidebar.warning("The selected run does not contain any agents.")
        st.stop()
    selected_agent = st.sidebar.selectbox("Agent / model", agent_names)
    if selected_agent is None:
        st.stop()
    agent_data = selected_run["agents"][selected_agent]
    tasks = agent_data.get("tasks", {}) if isinstance(agent_data, dict) else {}
    render_sidebar_run_summary(selected_run, selected_agent)

    st.sidebar.subheader("Task results")
    statuses = st.sidebar.multiselect(
        "Task status",
        ["Passed", "Failed", "Timed out"],
        default=["Passed", "Failed", "Timed out"],
    )
    task_query = st.sidebar.text_input("Filter tasks")
    filtered_tasks = [
        task_name
        for task_name, result in sorted(tasks.items())
        if result_status(result) in statuses and task_query.lower() in task_name.lower()
    ]
    if not filtered_tasks:
        st.sidebar.warning("No tasks match the current filters.")
        st.stop()
    task_selector_key = f"selected_task:{selected_run.get('timestamp', '')}:{selected_agent}"
    if st.session_state.get(task_selector_key) not in filtered_tasks:
        st.session_state[task_selector_key] = filtered_tasks[0]
    selected_task = st.sidebar.radio(
        "Results",
        filtered_tasks,
        format_func=lambda task_name: task_option_label(task_name, tasks[task_name]),
        key=task_selector_key,
    )
    if selected_task is None:
        st.stop()
    selected_result = tasks[selected_task]

    st.header(selected_task)
    st.caption(
        f"{selected_agent} · Run "
        f"{format_run_timestamp(str(selected_run.get('timestamp', '')))}"
    )
    render_task_metrics(selected_result)

    view = st.radio(
        "View", ["Conversation", "Solution"], horizontal=True, key="task_view"
    )
    if view == "Conversation":
        render_conversation(repo_root, selected_agent, selected_result)
    else:
        render_solution(repo_root, selected_task, selected_result)

    with st.expander("All runs overview"):
        st.dataframe([summarize_run(run) for run in runs], hide_index=True, width="stretch")


if __name__ == "__main__":
    main()
