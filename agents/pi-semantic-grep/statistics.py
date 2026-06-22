import json
import os
from datetime import datetime

from stats_protocol import Stats


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

    # Detailed token and cost breakdown (available for inspection)
    input_tokens = 0
    output_tokens = 0
    cache_read_tokens = 0
    cache_write_tokens = 0
    total_tokens = 0
    cost_input = 0.0
    cost_output = 0.0
    cost_cache_read = 0.0
    cost_cache_write = 0.0
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
                    input_tokens += usage.get("input", 0)
                    output_tokens += usage.get("output", 0)
                    cache_read_tokens += usage.get("cacheRead", 0)
                    cache_write_tokens += usage.get("cacheWrite", 0)
                    total_tokens += usage.get("totalTokens", 0)
                    cost = usage.get("cost", {})
                    cost_input += cost.get("input", 0)
                    cost_output += cost.get("output", 0)
                    cost_cache_read += cost.get("cacheRead", 0)
                    cost_cache_write += cost.get("cacheWrite", 0)
                    cost_total += cost.get("total", 0)
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
    )
