import json
import os
from datetime import datetime

from stats_protocol import (
    Stats,
    ToolCallType,
    calculate_price,
    empty_tool_call_counts,
)


def _timestamp(value):
    if isinstance(value, (int, float)):
        return datetime.fromtimestamp(value).astimezone()
    if isinstance(value, str):
        return datetime.fromisoformat(value.replace("Z", "+00:00"))
    return None


def _session_file(session_dir: str) -> str:
    if not os.path.isdir(session_dir):
        return session_dir
    direct = os.path.join(session_dir, "session.jsonl")
    if os.path.isfile(direct):
        return direct
    jsonl_files = sorted(
        os.path.join(session_dir, name)
        for name in os.listdir(session_dir)
        if name.endswith(".jsonl")
    )
    if not jsonl_files:
        raise FileNotFoundError(f"no .jsonl files found in {session_dir}")
    return jsonl_files[0]


def _tool_call_type(tool_name: str) -> ToolCallType:
    """Map Codex item/tool names to the three benchmark categories."""
    match tool_name.lower():
        case (
            "read"
            | "read_file"
            | "grep"
            | "rg"
            | "find"
            | "glob"
            | "view"
        ):
            return ToolCallType.READ
        case (
            "commandexecution"
            | "command_execution"
            | "bash"
            | "shell"
            | "exec_command"
        ):
            return ToolCallType.SHELL_COMMAND
        case "filechange" | "file_change" | "apply_patch" | "edit" | "write":
            return ToolCallType.PATCH
        case "task" | "todowrite" | "task_complete":
            return ToolCallType.Other
        case _:
            raise ValueError(f"unknown Codex tool type {tool_name!r}")


def _record_tool_call(tool_call_ids, tool_calls_by_type, call_id, tool_name):
    """Record one uniquely identified, classified tool invocation."""
    if not call_id or not tool_name or call_id in tool_call_ids:
        return
    category = _tool_call_type(tool_name)
    tool_call_ids.add(call_id)
    tool_calls_by_type[category] += 1


def compute_statistics(session_dir: str) -> Stats:
    path = _session_file(session_dir)
    first_ts = None
    last_ts = None
    turn_ids = set()
    tool_call_ids = set()
    tool_calls_by_type = empty_tool_call_counts()
    assistant_turns = 0
    duration_seconds = None
    model_name = "gpt-5.6-luna"
    final_usage = None

    with open(path, encoding="utf-8") as session:
        for line in session:
            if not line.strip():
                continue
            event = json.loads(line)
            # `received_at` is added by the model launcher.
            event_ts = _timestamp(event.get("received_at", event.get("timestamp")))
            if event_ts is not None:
                first_ts = event_ts if first_ts is None else min(first_ts, event_ts)
                last_ts = event_ts if last_ts is None else max(last_ts, event_ts)

            payload = event.get("payload", {})
            payload_type = payload.get("type") if isinstance(payload, dict) else None

            # Counted Codex messages:
            # - response_item/custom_tool_call: an internal-format invocation.
            # - event_msg/item_started (item_completed is a compatibility
            #   fallback): an internal-format command or file invocation.
            # - item.started (item.completed is a compatibility fallback): a
            #   public codex-exec command_execution or file_change invocation.
            # - event_msg/token_count or turn.completed: cumulative token usage;
            #   only the last such message is used.
            match event.get("type"):
                case "turn_context" if isinstance(payload, dict):
                    if payload.get("turn_id"):
                        turn_ids.add(payload["turn_id"])
                    model_name = payload.get("model") or model_name
                case "response_item" if isinstance(payload, dict):
                    match payload.get("type"):
                        case "custom_tool_call":
                            _record_tool_call(
                                tool_call_ids,
                                tool_calls_by_type,
                                payload.get("call_id") or payload.get("id"),
                                payload.get("name", ""),
                            )
                        case _:
                            pass
                case "event_msg" if isinstance(payload, dict):
                    match payload_type:
                        case "task_complete":
                            duration_ms = payload.get("duration_ms")
                            if duration_ms is not None:
                                duration_seconds = duration_ms / 1000
                        case "agent_message":
                            assistant_turns += 1
                        case "token_count":
                            final_usage = payload.get("info", {}).get(
                                "total_token_usage"
                            )
                        case "item_started" | "item_completed":
                            item = payload.get("item", {})
                            item_type = str(item.get("type", "")).lower()
                            match item_type:
                                case "agentmessage" | "agent_message" | "message":
                                    if payload_type == "item_completed":
                                        assistant_turns += 1
                                case (
                                    "commandexecution"
                                    | "command_execution"
                                    | "filechange"
                                    | "file_change"
                                ):
                                    _record_tool_call(
                                        tool_call_ids,
                                        tool_calls_by_type,
                                        item.get("id"),
                                        item_type,
                                    )
                                case (
                                    "toolcall"
                                    | "tool_call"
                                    | "functioncall"
                                    | "function_call"
                                ):
                                    _record_tool_call(
                                        tool_call_ids,
                                        tool_calls_by_type,
                                        item.get("call_id") or item.get("id"),
                                        item.get("name") or item.get("tool") or "",
                                    )
                                case _:
                                    pass
                        case _:
                            pass
                case "turn.started":
                    turn_ids.add(
                        event.get("id")
                        or event.get("turn_id")
                        or str(len(turn_ids))
                    )
                    model_name = event.get("model") or model_name
                case "item.started" | "item.completed":
                    item = event.get("item", {})
                    item_type = str(item.get("type", "")).lower()
                    match item_type:
                        case "agent_message" | "message":
                            if event.get("type") == "item.completed":
                                assistant_turns += 1
                        case "command_execution" | "file_change":
                            _record_tool_call(
                                tool_call_ids,
                                tool_calls_by_type,
                                item.get("id"),
                                item_type,
                            )
                        case "tool_call":
                            _record_tool_call(
                                tool_call_ids,
                                tool_calls_by_type,
                                item.get("call_id") or item.get("id"),
                                item.get("name") or item.get("tool") or "",
                            )
                        case _:
                            pass
                case "turn.completed":
                    final_usage = event.get("usage") or event.get("result", {}).get(
                        "usage"
                    )
                    model_name = event.get("model") or model_name
                case _:
                    pass

    # Some `codex exec --json` versions omit event timestamps and only report
    # usage in turn.completed. There is then no reliable duration to derive.
    if duration_seconds is None and first_ts is not None and last_ts is not None:
        duration_seconds = (last_ts - first_ts).total_seconds()
    if duration_seconds is None:
        duration_seconds = 0.0

    usage = final_usage or {}
    input_tokens = usage.get("input_tokens", usage.get("inputTokens", 0))
    cached_input_tokens = usage.get(
        "cached_input_tokens", usage.get("cachedInputTokens", 0)
    )
    cache_write_input_tokens = usage.get(
        "cache_write_input_tokens", usage.get("cacheWriteInputTokens", 0)
    )
    output_tokens = usage.get("output_tokens", usage.get("outputTokens", 0))

    # Codex reports input_tokens as total input, with cached_input_tokens as a
    # subset. Charge uncached input at the normal rate and the cached subset at
    # the discounted rate.
    uncached_input_tokens = max(
        input_tokens - cached_input_tokens - cache_write_input_tokens, 0
    )
    total_cost = calculate_price(
        model_name,
        uncached_input_tokens,
        cached_input_tokens,
        cache_write_input_tokens,
        output_tokens,
    )

    return Stats(
        total_costs=round(total_cost, 8),
        total_input_tokens=input_tokens,
        total_output_tokens=output_tokens,
        total_turns=assistant_turns or len(turn_ids),
        total_tool_calls=sum(tool_calls_by_type.values()),
        tool_calls_by_type=tool_calls_by_type,
        duration_seconds=duration_seconds,
        session_file=os.path.relpath(path),
    )
