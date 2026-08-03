#!/usr/bin/env python3

from __future__ import annotations

import difflib
import json
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

import streamlit as st


MAX_TOOL_OUTPUT_CHARS = 20_000


@dataclass
class TimelineItem:
    kind: str
    title: str
    timestamp: datetime | None = None
    role: str | None = None
    body: str = ""
    thinking: str = ""
    input: Any = None
    output: Any = None
    status: str | None = None
    details: Any = None
    elapsed_seconds: float | None = field(default=None, init=False)

    def searchable_text(self) -> str:
        values = (
            self.kind,
            self.title,
            self.role,
            self.body,
            self.thinking,
            payload_text(self.input),
            payload_text(self.output),
            payload_text(self.details),
            self.status,
        )
        return "\n".join(str(value) for value in values if value).lower()


def payload_text(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    try:
        return json.dumps(value, ensure_ascii=False, indent=2)
    except (TypeError, ValueError):
        return str(value)


def content_text(content: Any) -> str:
    if isinstance(content, str):
        return content
    if not isinstance(content, list):
        return payload_text(content)

    parts: list[str] = []
    for block in content:
        if isinstance(block, str):
            parts.append(block)
        elif isinstance(block, dict):
            text = block.get("text") or block.get("content")
            if text:
                parts.append(payload_text(text))
    return "\n\n".join(parts)


def parse_timestamp(value: Any) -> datetime | None:
    if value is None:
        return None
    if isinstance(value, (int, float)):
        seconds = value / 1000 if value > 10_000_000_000 else value
        try:
            return datetime.fromtimestamp(seconds, tz=timezone.utc)
        except (OSError, OverflowError, ValueError):
            return None
    if isinstance(value, str):
        try:
            parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
            if parsed.tzinfo is None:
                parsed = parsed.replace(tzinfo=timezone.utc)
            return parsed.astimezone(timezone.utc)
        except ValueError:
            return None
    return None


def timestamp_caption(item: TimelineItem) -> str:
    parts: list[str] = []
    if item.timestamp:
        parts.append(item.timestamp.strftime("%Y-%m-%d %H:%M:%S UTC"))
    if item.elapsed_seconds is not None:
        parts.append(f"+{format_duration(item.elapsed_seconds)}")
    return " · ".join(parts)


def format_duration(value: Any) -> str:
    try:
        seconds = max(0, int(round(float(value))))
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
    try:
        return datetime.strptime(value, "%Y%m%d_%H%M%S").strftime("%Y-%m-%d %H:%M:%S")
    except ValueError:
        return value


def safe_repo_path(repo_root: Path, value: Any) -> Path | None:
    if not isinstance(value, str) or not value:
        return None
    candidate = Path(value)
    resolved = candidate.resolve() if candidate.is_absolute() else (repo_root / candidate).resolve()
    try:
        resolved.relative_to(repo_root)
    except ValueError:
        return None
    return resolved


def load_runs(runs_dir: Path) -> tuple[list[dict[str, Any]], list[str]]:
    runs: list[dict[str, Any]] = []
    errors: list[str] = []
    for run_path in sorted(runs_dir.glob("*.json"), reverse=True):
        try:
            data = json.loads(run_path.read_text())
            if not isinstance(data, dict) or not isinstance(data.get("agents"), dict):
                raise ValueError("expected an object containing an 'agents' object")
            data["_path"] = run_path
            data.setdefault("timestamp", run_path.stem)
            runs.append(data)
        except (OSError, json.JSONDecodeError, ValueError) as error:
            errors.append(f"{run_path.name}: {error}")
    return runs, errors


def all_task_results(run: dict[str, Any]) -> list[tuple[str, str, dict[str, Any]]]:
    rows: list[tuple[str, str, dict[str, Any]]] = []
    for agent_name, agent_data in run.get("agents", {}).items():
        tasks = agent_data.get("tasks", {}) if isinstance(agent_data, dict) else {}
        for task_name, result in tasks.items():
            if isinstance(result, dict):
                rows.append((agent_name, task_name, result))
    return rows


def numeric_total(rows: Iterable[tuple[str, str, dict[str, Any]]], key: str) -> float:
    total = 0.0
    for _, _, result in rows:
        value = result.get(key, 0)
        if isinstance(value, (int, float)) and not isinstance(value, bool):
            total += value
    return total


def summarize_run(run: dict[str, Any]) -> dict[str, Any]:
    rows = all_task_results(run)
    return {
        "Run": format_run_timestamp(str(run.get("timestamp", ""))),
        "Agents": ", ".join(run.get("agents", {}).keys()),
        "Tasks": len(rows),
        "Verus passed": sum(result.get("verus_passed") is True for _, _, result in rows),
        "Cheat check passed": sum(
            result.get("cheat_checker_passed") is True for _, _, result in rows
        ),
        "Timed out": sum(result.get("timed_out") is True for _, _, result in rows),
        "Cost": f"${numeric_total(rows, 'total_costs'):.2f}",
        "Duration": format_duration(numeric_total(rows, "duration_seconds")),
    }


def result_status(result: dict[str, Any]) -> str:
    if result.get("timed_out") is True:
        return "Timed out"
    if result.get("verus_passed") is True and result.get("cheat_checker_passed") is True:
        return "Passed"
    return "Failed"


def status_label(value: Any) -> str:
    if value is True:
        return "✅ Passed"
    if value is False:
        return "❌ Failed"
    return "— Unknown"


def load_jsonl(session_path: Path) -> tuple[list[dict[str, Any]], list[str]]:
    events: list[dict[str, Any]] = []
    errors: list[str] = []
    try:
        with session_path.open(errors="replace") as session_file:
            for line_number, line in enumerate(session_file, start=1):
                if not line.strip():
                    continue
                try:
                    event = json.loads(line)
                    if isinstance(event, dict):
                        events.append(event)
                    else:
                        errors.append(f"Line {line_number}: expected a JSON object")
                except json.JSONDecodeError as error:
                    errors.append(f"Line {line_number}: {error.msg}")
    except OSError as error:
        errors.append(str(error))
    return events, errors


def normalize_pi(events: list[dict[str, Any]]) -> list[TimelineItem]:
    tool_results: dict[str, dict[str, Any]] = {}
    for event in events:
        message = event.get("message", {})
        if event.get("type") == "message" and message.get("role") == "toolResult":
            call_id = message.get("toolCallId")
            if call_id:
                tool_results[str(call_id)] = message

    items: list[TimelineItem] = []
    paired_results: set[str] = set()
    for event in events:
        event_type = event.get("type", "event")
        timestamp = parse_timestamp(event.get("timestamp"))
        if event_type != "message":
            if event_type in {"session", "model_change", "thinking_level_change"}:
                items.append(
                    TimelineItem(
                        kind="event",
                        title=event_type.replace("_", " ").title(),
                        timestamp=timestamp,
                        details={key: value for key, value in event.items() if key != "timestamp"},
                    )
                )
            continue

        message = event.get("message", {})
        role = message.get("role", "unknown")
        content = message.get("content", [])
        if role == "toolResult":
            call_id = str(message.get("toolCallId", ""))
            if call_id in paired_results:
                continue
            items.append(
                TimelineItem(
                    kind="tool",
                    title=str(message.get("toolName", "Tool result")),
                    timestamp=timestamp,
                    output=content_text(content),
                    status="error" if message.get("isError") else "completed",
                )
            )
            continue

        if not isinstance(content, list):
            content = []
        text_blocks = [block.get("text", "") for block in content if isinstance(block, dict) and block.get("type") == "text"]
        thinking_blocks = [
            block.get("thinking", "")
            for block in content
            if isinstance(block, dict) and block.get("type") == "thinking"
        ]
        body = "\n\n".join(value for value in text_blocks if value)
        thinking = "\n\n".join(value for value in thinking_blocks if value)
        if body or thinking or role == "user":
            items.append(
                TimelineItem(
                    kind="message",
                    title=role.title(),
                    timestamp=timestamp,
                    role=role,
                    body=body,
                    thinking=thinking,
                )
            )

        for block in content:
            if not isinstance(block, dict) or block.get("type") != "toolCall":
                continue
            call_id = str(block.get("id", ""))
            result = tool_results.get(call_id, {})
            if call_id:
                paired_results.add(call_id)
            items.append(
                TimelineItem(
                    kind="tool",
                    title=str(block.get("name", "Tool call")),
                    timestamp=timestamp,
                    input=block.get("arguments"),
                    output=content_text(result.get("content")),
                    status="error" if result.get("isError") else ("completed" if result else "unknown"),
                )
            )
    return items


def normalize_opencode(events: list[dict[str, Any]]) -> list[TimelineItem]:
    items: list[TimelineItem] = []
    for event in events:
        event_type = event.get("type", "event")
        timestamp = parse_timestamp(event.get("timestamp"))
        part = event.get("part", {})
        if event_type == "text":
            items.append(
                TimelineItem(
                    kind="message",
                    title="Assistant",
                    timestamp=timestamp,
                    role="assistant",
                    body=str(part.get("text", "")),
                )
            )
        elif event_type == "tool_use":
            state = part.get("state", {})
            output = state.get("output")
            if output is None and state.get("error") is not None:
                output = state.get("error")
            items.append(
                TimelineItem(
                    kind="tool",
                    title=str(part.get("tool", "Tool call")),
                    timestamp=timestamp,
                    input=state.get("input"),
                    output=output,
                    status=str(state.get("status", "unknown")),
                )
            )
    return items


def normalize_copilot(events: list[dict[str, Any]]) -> list[TimelineItem]:
    completions: dict[str, dict[str, Any]] = {}
    starts: set[str] = set()
    for event in events:
        data = event.get("data", {})
        call_id = data.get("toolCallId")
        if event.get("type") == "tool.execution_complete" and call_id:
            completions[str(call_id)] = data
        elif event.get("type") == "tool.execution_start" and call_id:
            starts.add(str(call_id))

    items: list[TimelineItem] = []
    for event in events:
        event_type = event.get("type", "event")
        timestamp = parse_timestamp(event.get("timestamp"))
        data = event.get("data", {})
        if event_type in {"user.message", "assistant.message", "system.message"}:
            role = event_type.split(".", maxsplit=1)[0]
            items.append(
                TimelineItem(
                    kind="message",
                    title=role.title(),
                    timestamp=timestamp,
                    role=role,
                    body=str(data.get("content", "")),
                )
            )
            if event_type == "assistant.message":
                for request in data.get("toolRequests", []):
                    call_id = str(request.get("toolCallId", ""))
                    if call_id in starts:
                        continue
                    items.append(
                        TimelineItem(
                            kind="tool",
                            title=str(request.get("name", "Tool call")),
                            timestamp=timestamp,
                            input=request.get("arguments"),
                            status="unknown",
                        )
                    )
        elif event_type == "tool.execution_start":
            call_id = str(data.get("toolCallId", ""))
            completion = completions.get(call_id, {})
            items.append(
                TimelineItem(
                    kind="tool",
                    title=str(data.get("toolName", "Tool call")),
                    timestamp=timestamp,
                    input=data.get("arguments"),
                    output=completion.get("result"),
                    status=(
                        "completed"
                        if completion.get("success") is True
                        else "error"
                        if completion.get("success") is False
                        else "unknown"
                    ),
                )
            )
        elif event_type == "tool.execution_complete" or event_type in {
            "assistant.turn_start",
            "assistant.turn_end",
        }:
            continue
        elif event_type.startswith("session."):
            if event_type in {
                "session.error",
                "session.task_complete",
                "session.compaction_start",
                "session.compaction_complete",
                "session.model_change",
                "session.shutdown",
            }:
                body = str(data.get("summary") or data.get("message") or "")
                status = None
                if event_type == "session.error":
                    status = "error"
                elif data.get("success") is True:
                    status = "completed"
                elif data.get("success") is False:
                    status = "error"
                items.append(
                    TimelineItem(
                        kind="event",
                        title=event_type.replace(".", " ").title(),
                        timestamp=timestamp,
                        body=body,
                        status=status,
                        details=data,
                    )
                )
    return items


def normalize_generic(events: list[dict[str, Any]]) -> list[TimelineItem]:
    return [
        TimelineItem(
            kind="event",
            title=str(event.get("type", "Event")),
            timestamp=parse_timestamp(event.get("timestamp")),
            details=event,
        )
        for event in events
    ]


def normalize_session(events: list[dict[str, Any]], agent_name: str) -> list[TimelineItem]:
    agent = agent_name.split("/", maxsplit=1)[0]
    if agent == "copilot":
        items = normalize_copilot(events)
    elif agent == "opencode":
        items = normalize_opencode(events)
    elif agent.startswith("pi"):
        items = normalize_pi(events)
    else:
        items = normalize_generic(events)

    timestamps = [item.timestamp for item in items if item.timestamp is not None]
    if timestamps:
        start = min(timestamps)
        for item in items:
            if item.timestamp is not None:
                item.elapsed_seconds = (item.timestamp - start).total_seconds()
    return items


def render_payload(label: str, value: Any, show_full: bool) -> None:
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

    status_icon = {"completed": "✅", "error": "❌"}.get(item.status, "")
    label = " ".join(part for part in [status_icon, item.title, f"· {caption}" if caption else ""] if part)
    with st.expander(label):
        if item.body:
            st.markdown(item.body)
        render_payload("Input", item.input, show_full)
        render_payload("Output", item.output, show_full)
        if item.details is not None and not item.body:
            render_payload("Details", item.details, show_full)


def render_run_metrics(run: dict[str, Any]) -> None:
    rows = all_task_results(run)
    metrics = st.columns(6)
    metrics[0].metric("Tasks", len(rows))
    metrics[1].metric(
        "Verus passed", f"{sum(result.get('verus_passed') is True for _, _, result in rows)}/{len(rows)}"
    )
    metrics[2].metric(
        "Cheat check passed",
        f"{sum(result.get('cheat_checker_passed') is True for _, _, result in rows)}/{len(rows)}",
    )
    metrics[3].metric("Timed out", sum(result.get("timed_out") is True for _, _, result in rows))
    metrics[4].metric("Total cost", f"${numeric_total(rows, 'total_costs'):.2f}")
    metrics[5].metric("Total duration", format_duration(numeric_total(rows, "duration_seconds")))


def render_task_metrics(result: dict[str, Any]) -> None:
    st.subheader("Selected task")
    metrics = st.columns(6)
    metrics[0].metric("Verus", status_label(result.get("verus_passed")))
    metrics[1].metric("Cheat check", status_label(result.get("cheat_checker_passed")))
    metrics[2].metric("Timed out", "Yes" if result.get("timed_out") else "No")
    metrics[3].metric("Cost", f"${float(result.get('total_costs') or 0):.4f}")
    metrics[4].metric("Turns / tools", f"{result.get('total_turns', 0)} / {result.get('total_tool_calls', 0)}")
    metrics[5].metric("Duration", format_duration(result.get("duration_seconds")))


def task_table(tasks: dict[str, Any], repo_root: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for task_name, result in sorted(tasks.items()):
        solution = safe_repo_path(repo_root, result.get("solution_file"))
        rows.append(
            {
                "Task": task_name,
                "Status": result_status(result),
                "Verus": status_label(result.get("verus_passed")),
                "Cheat check": status_label(result.get("cheat_checker_passed")),
                "Timeout": "Yes" if result.get("timed_out") else "No",
                "Cost": f"${float(result.get('total_costs') or 0):.4f}",
                "Duration": format_duration(result.get("duration_seconds")),
                "Turns": result.get("total_turns", 0),
                "Tool calls": result.get("total_tool_calls", 0),
                "Solution": "Available" if solution and solution.is_file() else "Missing",
            }
        )
    return rows


def render_conversation(repo_root: Path, agent_name: str, result: dict[str, Any]) -> None:
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
    query = first.text_input("Search conversation", placeholder="Message, tool, command, error…")
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
    st.caption(f"Showing {len(visible_items)} of {len(items)} timeline items · {session_path.relative_to(repo_root)}")
    if not visible_items:
        st.info("No conversation items match the current filters.")
        return
    for item in visible_items:
        render_timeline_item(item, show_thinking=show_thinking, show_full=show_full)


def render_solution(repo_root: Path, task_name: str, result: dict[str, Any]) -> None:
    solution_path = safe_repo_path(repo_root, result.get("solution_file"))
    if solution_path is None or not solution_path.is_file():
        if result.get("timed_out"):
            st.warning("The task timed out and no solution file was produced.")
        else:
            st.warning("No solution file is available for this task.")
        return

    try:
        solution = solution_path.read_text(errors="replace")
    except OSError as error:
        st.error(f"Could not read the solution: {error}")
        return

    original_path = safe_repo_path(repo_root, f"tasks/{task_name}")
    st.caption(str(solution_path.relative_to(repo_root)))
    if original_path is None or not original_path.is_file():
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
    diff_tab, original_tab, solution_tab = st.tabs(["Diff", "Original", "Solution"])
    with diff_tab:
        if diff:
            st.code(diff, language="diff", line_numbers=True)
        else:
            st.success("The original and solution files are identical.")
    with original_tab:
        st.caption(str(original_path.relative_to(repo_root)))
        st.code(original, language="rust", line_numbers=True)
    with solution_tab:
        st.caption(str(solution_path.relative_to(repo_root)))
        st.code(solution, language="rust", line_numbers=True)


def main() -> None:
    st.set_page_config(page_title="Benchmark Run Explorer", page_icon="🧪", layout="wide")
    repo_root = Path.cwd().resolve()
    runs_dir = repo_root / "runs"

    st.title("Benchmark Run Explorer")
    st.caption(f"Reading benchmark artifacts from {repo_root}")
    if not runs_dir.is_dir():
        st.error("No runs/ directory was found. Start Streamlit from the benchmark repository root.")
        st.stop()

    runs, run_errors = load_runs(runs_dir)
    for error in run_errors:
        st.warning(error)
    if not runs:
        st.info("No valid run JSON files were found in runs/.")
        st.stop()

    with st.expander("All runs overview"):
        st.dataframe([summarize_run(run) for run in runs], hide_index=True, width="stretch")

    selected_run = st.sidebar.selectbox(
        "Run",
        runs,
        format_func=lambda run: format_run_timestamp(str(run.get("timestamp", "Unknown"))),
    )
    agent_names = sorted(selected_run.get("agents", {}).keys())
    selected_agent = st.sidebar.selectbox("Agent / model", agent_names)
    agent_data = selected_run["agents"][selected_agent]
    tasks = agent_data.get("tasks", {}) if isinstance(agent_data, dict) else {}

    statuses = st.sidebar.multiselect(
        "Task status", ["Passed", "Failed", "Timed out"], default=["Passed", "Failed", "Timed out"]
    )
    task_query = st.sidebar.text_input("Filter tasks")
    filtered_tasks = [
        task_name
        for task_name, result in sorted(tasks.items())
        if result_status(result) in statuses and task_query.lower() in task_name.lower()
    ]
    if not filtered_tasks:
        st.warning("No tasks match the current sidebar filters.")
        st.stop()
    selected_task = st.sidebar.selectbox("Task", filtered_tasks)
    selected_result = tasks[selected_task]

    st.header(format_run_timestamp(str(selected_run.get("timestamp", ""))))
    st.caption(selected_agent)
    render_run_metrics(selected_run)
    render_task_metrics(selected_result)
    st.caption(selected_task)

    results_tab, conversation_tab, solution_tab = st.tabs(["Results", "Conversation", "Solution"])
    with results_tab:
        st.dataframe(task_table(tasks, repo_root), hide_index=True, width="stretch")
    with conversation_tab:
        render_conversation(repo_root, selected_agent, selected_result)
    with solution_tab:
        render_solution(repo_root, selected_task, selected_result)


if __name__ == "__main__":
    main()
