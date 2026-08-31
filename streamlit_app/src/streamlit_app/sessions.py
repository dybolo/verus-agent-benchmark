"""Read agent session logs and normalize their provider-specific events into timelines."""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


@dataclass
class TimelineItem:
    """One message, tool call, or status event shown in a conversation timeline."""

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
        """Return the item contents as lower-case text for conversation filtering."""
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
    """Convert a session payload into readable text without failing on arbitrary values."""
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    try:
        return json.dumps(value, ensure_ascii=False, indent=2)
    except (TypeError, ValueError):
        return str(value)


def content_text(content: Any) -> str:
    """Extract readable text from a provider's message-content payload."""
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
    """Parse an ISO timestamp or Unix timestamp into a UTC datetime."""
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


def load_jsonl(session_path: Path) -> tuple[list[dict[str, Any]], list[str]]:
    """Read a JSONL session file and return valid object events plus parse errors."""
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
    """Normalize Pi session events, pairing tool calls with their results."""
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
            if call_id not in paired_results:
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
        body = "\n\n".join(
            block.get("text", "")
            for block in content
            if isinstance(block, dict) and block.get("type") == "text" and block.get("text")
        )
        thinking = "\n\n".join(
            block.get("thinking", "")
            for block in content
            if isinstance(block, dict) and block.get("type") == "thinking" and block.get("thinking")
        )
        if body or thinking or role == "user":
            items.append(
                TimelineItem(
                    kind="message", title=role.title(), timestamp=timestamp, role=role,
                    body=body, thinking=thinking,
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
                    kind="tool", title=str(block.get("name", "Tool call")), timestamp=timestamp,
                    input=block.get("arguments"), output=content_text(result.get("content")),
                    status="error" if result.get("isError") else ("completed" if result else "unknown"),
                )
            )
    return items


def normalize_opencode(events: list[dict[str, Any]]) -> list[TimelineItem]:
    """Normalize OpenCode text and tool-use events."""
    items: list[TimelineItem] = []
    for event in events:
        event_type = event.get("type", "event")
        timestamp = parse_timestamp(event.get("timestamp"))
        part = event.get("part", {})
        if event_type == "text":
            items.append(
                TimelineItem("message", "Assistant", timestamp, role="assistant", body=str(part.get("text", "")))
            )
        elif event_type == "tool_use":
            state = part.get("state", {})
            output = state.get("output")
            if output is None:
                output = state.get("error")
            items.append(
                TimelineItem(
                    "tool", str(part.get("tool", "Tool call")), timestamp,
                    input=state.get("input"), output=output, status=str(state.get("status", "unknown")),
                )
            )
    return items


def normalize_copilot(events: list[dict[str, Any]]) -> list[TimelineItem]:
    """Normalize Copilot messages and tool-execution events."""
    completions = {
        str(event.get("data", {}).get("toolCallId")): event.get("data", {})
        for event in events
        if event.get("type") == "tool.execution_complete" and event.get("data", {}).get("toolCallId")
    }
    starts = {
        str(event.get("data", {}).get("toolCallId"))
        for event in events
        if event.get("type") == "tool.execution_start" and event.get("data", {}).get("toolCallId")
    }
    items: list[TimelineItem] = []
    for event in events:
        event_type = event.get("type", "event")
        timestamp = parse_timestamp(event.get("timestamp"))
        data = event.get("data", {})
        if event_type in {"user.message", "assistant.message", "system.message"}:
            role = event_type.split(".", maxsplit=1)[0]
            items.append(TimelineItem("message", role.title(), timestamp, role=role, body=str(data.get("content", ""))))
            if event_type == "assistant.message":
                for request in data.get("toolRequests", []):
                    if str(request.get("toolCallId", "")) not in starts:
                        items.append(TimelineItem("tool", str(request.get("name", "Tool call")), timestamp, input=request.get("arguments"), status="unknown"))
        elif event_type == "tool.execution_start":
            completion = completions.get(str(data.get("toolCallId", "")), {})
            status = "completed" if completion.get("success") is True else "error" if completion.get("success") is False else "unknown"
            items.append(TimelineItem("tool", str(data.get("toolName", "Tool call")), timestamp, input=data.get("arguments"), output=completion.get("result"), status=status))
        elif event_type.startswith("session.") and event_type in {
            "session.error", "session.task_complete", "session.compaction_start",
            "session.compaction_complete", "session.model_change", "session.shutdown",
        }:
            status = "error" if event_type == "session.error" else "completed" if data.get("success") is True else "error" if data.get("success") is False else None
            items.append(TimelineItem("event", event_type.replace(".", " ").title(), timestamp, body=str(data.get("summary") or data.get("message") or ""), status=status, details=data))
    return items


def codex_status(item: dict[str, Any], event_type: str) -> str:
    """Translate Codex item states into the viewer's shared status values."""
    status = str(item.get("status", ""))
    if status in {"failed", "error"}:
        return "error"
    if status == "completed" or event_type == "item.completed":
        return "completed"
    return status or "unknown"


def normalize_codex(events: list[dict[str, Any]]) -> list[TimelineItem]:
    """Normalize events emitted by ``codex exec --json``.

    Item start, update, and completion records repeat the full item. Only the last
    version of each item is rendered so commands and file edits do not appear twice.
    """
    last_item_event: dict[str, int] = {}
    for index, event in enumerate(events):
        item = event.get("item")
        if isinstance(item, dict) and item.get("id"):
            last_item_event[str(item["id"])] = index

    items: list[TimelineItem] = []
    for index, event in enumerate(events):
        event_type = str(event.get("type", "event"))
        timestamp = parse_timestamp(event.get("received_at") or event.get("timestamp"))
        item = event.get("item")

        if isinstance(item, dict):
            item_id = item.get("id")
            if item_id and last_item_event.get(str(item_id)) != index:
                continue
            item_type = str(item.get("type", "item"))
            status = codex_status(item, event_type)
            if item_type == "agent_message":
                items.append(
                    TimelineItem(
                        "message", "Assistant", timestamp,
                        role="assistant", body=str(item.get("text", "")),
                    )
                )
            elif item_type == "command_execution":
                items.append(
                    TimelineItem(
                        "tool", "Command", timestamp,
                        input=item.get("command"), output=item.get("aggregated_output"),
                        status=status,
                        details={"exit_code": item.get("exit_code")},
                    )
                )
            elif item_type == "file_change":
                items.append(
                    TimelineItem(
                        "tool", "File changes", timestamp,
                        input=item.get("changes"), status=status,
                    )
                )
            elif item_type == "web_search":
                items.append(
                    TimelineItem(
                        "tool", "Web search", timestamp,
                        input=item.get("action") or item.get("query"), status=status,
                    )
                )
            elif item_type == "todo_list":
                items.append(
                    TimelineItem(
                        "event", "Todo list", timestamp,
                        status=status, details=item.get("items"),
                    )
                )
            elif item_type == "error":
                items.append(
                    TimelineItem(
                        "event", "Error", timestamp,
                        body=str(item.get("message", "")), status="error",
                    )
                )
            else:
                items.append(
                    TimelineItem(
                        "event", item_type.replace("_", " ").title(), timestamp,
                        status=status, details=item,
                    )
                )
            continue

        if event_type in {"session.started", "thread.started", "turn.started", "turn.completed"}:
            details = {
                key: value
                for key, value in event.items()
                if key not in {"type", "timestamp", "received_at"}
            }
            items.append(
                TimelineItem(
                    "event", event_type.replace(".", " ").title(), timestamp,
                    status="completed" if event_type == "turn.completed" else None,
                    details=details or None,
                )
            )
    return items


def normalize_generic(events: list[dict[str, Any]]) -> list[TimelineItem]:
    """Represent unrecognized provider events without discarding their details."""
    return [
        TimelineItem("event", str(event.get("type", "Event")), parse_timestamp(event.get("timestamp")), details=event)
        for event in events
    ]


def normalize_session(events: list[dict[str, Any]], agent_name: str) -> list[TimelineItem]:
    """Choose a provider normalizer and calculate elapsed time for each item."""
    agent = agent_name.split("/", maxsplit=1)[0]
    if agent == "copilot":
        items = normalize_copilot(events)
    elif agent == "codex":
        items = normalize_codex(events)
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
