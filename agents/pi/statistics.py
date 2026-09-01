import json
import os
from datetime import datetime

from stats_protocol import Stats, calculate_price


def _usage_cost(model, usage):
    return calculate_price(
        model,
        usage.get("input", 0),
        usage.get("cacheRead", 0),
        usage.get("cacheWrite", 0),
        usage.get("output", 0),
    )


def parse_timestamp(ts_str):
    return datetime.fromisoformat(ts_str.replace("Z", "+00:00"))


def compute_statistics(session_dir: str) -> Stats:
    if os.path.isdir(session_dir):
        jsonl_files = sorted(f for f in os.listdir(session_dir) if f.endswith(".jsonl"))
        if not jsonl_files:
            raise FileNotFoundError(f"no .jsonl files found in {session_dir}")
        path = os.path.join(session_dir, jsonl_files[0])
    else:
        path = session_dir

    cost_total = 0.0
    tool_call_count = 0
    assistant_msg_count = 0
    first_ts = None
    last_ts = None

    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            event = json.loads(line)

            ts = event.get("timestamp")
            if ts:
                dt = parse_timestamp(ts)
                if first_ts is None or dt < first_ts:
                    first_ts = dt
                if last_ts is None or dt > last_ts:
                    last_ts = dt

            etype = event.get("type")
            if etype == "message":
                msg = event.get("message", {})
                role = msg.get("role")
                usage = msg.get("usage")
                if usage:
                    cost_total += _usage_cost(msg.get("model"), usage)
                if role == "assistant":
                    assistant_msg_count += 1
                    content = msg.get("content", [])
                    for block in content:
                        if isinstance(block, dict) and block.get("type") == "toolCall":
                            tool_call_count += 1

    if first_ts is None or last_ts is None:
        raise RuntimeError("could not determine session timestamps")

    duration_seconds = (last_ts - first_ts).total_seconds()

    return Stats(
        total_costs=round(cost_total, 8),
        total_turns=assistant_msg_count,
        total_tool_calls=tool_call_count,
        duration_seconds=duration_seconds,
        session_file=os.path.relpath(path),
    )
