#!/usr/bin/env python3

import json
import os
import sys


def main():
    if len(sys.argv) < 2:
        print("usage: statistics.py <session-dir>", file=sys.stderr)
        sys.exit(1)

    session_dir = sys.argv[1]
    jsonl_path = os.path.join(session_dir, "session.jsonl")

    if not os.path.isfile(jsonl_path):
        print(f"no session.jsonl found at {jsonl_path}", file=sys.stderr)
        sys.exit(1)

    input_tokens = 0
    output_tokens = 0
    cache_read_tokens = 0
    cache_write_tokens = 0
    reasoning_tokens = 0
    total_cost_actual = 0.0
    total_requests = 0
    turn_count = 0
    tool_call_count = 0
    first_ts = None
    last_ts = None

    with open(jsonl_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            event = json.loads(line)

            ts = event.get("timestamp")
            if ts is not None:
                if first_ts is None or ts < first_ts:
                    first_ts = ts
                if last_ts is None or ts > last_ts:
                    last_ts = ts

            etype = event.get("type")

            if etype == "step_finish":
                part = event.get("part", {})
                tokens = part.get("tokens", {})
                input_tokens += tokens.get("input", 0)
                output_tokens += tokens.get("output", 0)
                reasoning_tokens += tokens.get("reasoning", 0)
                cache = tokens.get("cache", {})
                cache_read_tokens += cache.get("read", 0)
                cache_write_tokens += cache.get("write", 0)
                total_cost_actual += part.get("cost", 0)
                total_requests += 1
                turn_count += 1

            elif etype == "tool_use":
                part = event.get("part", {})
                state = part.get("state", {})
                if state.get("status") == "completed":
                    tool_call_count += 1

    if first_ts is None or last_ts is None:
        print("could not determine session timestamps", file=sys.stderr)
        sys.exit(1)

    duration_seconds = (last_ts - first_ts) / 1000

    result = {
        "input_tokens": input_tokens,
        "output_tokens": output_tokens,
        "cache_read_tokens": cache_read_tokens,
        "cache_write_tokens": cache_write_tokens,
        "reasoning_tokens": reasoning_tokens,
        "total_tokens": input_tokens + output_tokens + cache_read_tokens + cache_write_tokens,
        "total_requests": total_requests,
        "total_cost": round(total_cost_actual, 8),
        "total_turns": turn_count,
        "total_tool_calls": tool_call_count,
        "duration_seconds": duration_seconds,
    }

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
