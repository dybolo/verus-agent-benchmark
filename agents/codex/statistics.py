import json
import os
from datetime import datetime

from stats_protocol import Stats, calculate_price


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


def compute_statistics(session_dir: str) -> Stats:
    path = _session_file(session_dir)
    first_ts = None
    last_ts = None
    turn_ids = set()
    tool_call_ids = set()
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

            if event.get("type") == "turn_context" and isinstance(payload, dict):
                if payload.get("turn_id"):
                    turn_ids.add(payload["turn_id"])
                model_name = payload.get("model") or model_name
            elif event.get("type") == "response_item" and isinstance(payload, dict):
                if payload.get("type") == "custom_tool_call":
                    call_id = payload.get("call_id") or payload.get("id")
                    if call_id and payload.get("status") in (None, "completed"):
                        tool_call_ids.add(call_id)
            elif event.get("type") == "event_msg" and isinstance(payload, dict):
                if payload_type == "task_complete":
                    duration_ms = payload.get("duration_ms")
                    if duration_ms is not None:
                        duration_seconds = duration_ms / 1000
                elif payload_type == "agent_message":
                    assistant_turns += 1
                elif payload_type == "token_count":
                    # token_count events are cumulative; use only the last one.
                    final_usage = payload.get("info", {}).get("total_token_usage")
                elif payload_type == "item_completed":
                    # Recent Codex CLI versions wrap completed items in
                    # event_msg rather than emitting item.completed directly.
                    item = payload.get("item", {})
                    item_type = str(item.get("type", "")).lower()
                    if item_type in ("agentmessage", "agent_message", "message"):
                        assistant_turns += 1
                    elif item_type in (
                        "commandexecution",
                        "command_execution",
                        "toolcall",
                        "tool_call",
                        "functioncall",
                        "function_call",
                    ):
                        call_id = item.get("id")
                        if call_id:
                            tool_call_ids.add(call_id)

            # Also accept the public codex exec JSONL event names.
            event_type = event.get("type")
            if event_type == "turn.started":
                turn_ids.add(event.get("id") or event.get("turn_id") or str(len(turn_ids)))
                model_name = event.get("model") or model_name
            elif event_type == "item.completed":
                item = event.get("item", {})
                if item.get("type") in ("agent_message", "message"):
                    assistant_turns += 1
                elif item.get("type") in ("command_execution", "tool_call"):
                    tool_call_ids.add(item.get("id") or str(len(tool_call_ids)))
            elif event_type == "turn.completed":
                final_usage = event.get("usage") or event.get("result", {}).get("usage")
                model_name = event.get("model") or model_name

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
    output_tokens = usage.get("output_tokens", usage.get("outputTokens", 0))

    # Codex reports input_tokens as total input, with cached_input_tokens as a
    # subset. Charge uncached input at the normal rate and the cached subset at
    # the discounted rate.
    uncached_input_tokens = max(input_tokens - cached_input_tokens, 0)
    total_cost = calculate_price(
        model_name,
        uncached_input_tokens,
        cached_input_tokens,
        0,
        output_tokens,
    )

    return Stats(
        total_costs=round(total_cost, 8),
        total_turns=assistant_turns or len(turn_ids),
        total_tool_calls=len(tool_call_ids),
        duration_seconds=duration_seconds,
        session_file=os.path.relpath(path),
    )
