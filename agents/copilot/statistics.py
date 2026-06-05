#!/usr/bin/env python3

import json
import sys
from datetime import datetime


def parse_timestamp(ts_str):
    return datetime.fromisoformat(ts_str.replace("Z", "+00:00"))


def main():
    if len(sys.argv) < 2:
        print(json.dumps({"error": "usage: statistics.py <session.jsonl>"}))
        sys.exit(1)

    path = sys.argv[1]

    shutdown = None
    tool_call_count = 0
    turn_count = 0
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
            if etype == "session.shutdown":
                shutdown = event
            elif etype == "tool.execution_start":
                tool_call_count += 1
            elif etype == "assistant.turn_start":
                turn_count += 1

    if shutdown is None:
        print(json.dumps({"error": "no session.shutdown event found"}))
        sys.exit(1)

    data = shutdown["data"]
    model_metrics = data.get("modelMetrics", {})
    metrics = {}
    for model_name, model_data in model_metrics.items():
        metrics = model_data.get("usage", {}).copy()
        metrics["requests"] = model_data.get("requests", {}).get("count", 0)
        metrics["cost"] = model_data.get("requests", {}).get("cost", 0)
        break

    total_duration_ms = data.get("totalApiDurationMs", 0)
    if total_duration_ms == 0 and first_ts and last_ts:
        total_duration_ms = (last_ts - first_ts).total_seconds() * 1000

    result = {
        "input_tokens": metrics.get("inputTokens", 0),
        "output_tokens": metrics.get("outputTokens", 0),
        "cache_read_tokens": metrics.get("cacheReadTokens", 0),
        "cache_write_tokens": metrics.get("cacheWriteTokens", 0),
        "reasoning_tokens": metrics.get("reasoningTokens", 0),
        "total_tokens": metrics.get("inputTokens", 0) + metrics.get("outputTokens", 0) + metrics.get("cacheReadTokens", 0) + metrics.get("cacheWriteTokens", 0),
        "total_requests": metrics.get("requests", 0),
        "total_cost": metrics.get("cost", 0),
        "total_turns": turn_count,
        "total_tool_calls": tool_call_count,
        "duration_seconds": total_duration_ms / 1000,
    }

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
