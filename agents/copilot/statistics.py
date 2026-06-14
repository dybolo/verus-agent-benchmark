#!/usr/bin/env python3

import glob
import json
import os
import sys
from datetime import datetime

MODEL_PRICING = {
    "gpt-4.1":              {"input": 2.00, "cachedInput": 0.50,  "output": 8.00},
    "gpt-5-mini":           {"input": 0.25, "cachedInput": 0.025, "output": 2.00},
    "gpt-5.2":              {"input": 1.75, "cachedInput": 0.175, "output": 14.00},
    "gpt-5.2-codex":        {"input": 1.75, "cachedInput": 0.175, "output": 14.00},
    "gpt-5.3-codex":        {"input": 1.75, "cachedInput": 0.175, "output": 14.00},
    "gpt-5.4":              {"input": 2.50, "cachedInput": 0.25,  "output": 15.00},
    "gpt-5.4-mini":         {"input": 0.75, "cachedInput": 0.075, "output": 4.50},
    "gpt-5.4-nano":         {"input": 0.20, "cachedInput": 0.02,  "output": 1.25},
    "gpt-5.5":              {"input": 5.00, "cachedInput": 0.50,  "output": 30.00},
    "claude-haiku-4.5":     {"input": 1.00, "cachedInput": 0.10,  "cacheWrite": 1.25, "output": 5.00},
    "claude-sonnet-4":      {"input": 3.00, "cachedInput": 0.30,  "cacheWrite": 3.75, "output": 15.00},
    "claude-sonnet-4.5":    {"input": 3.00, "cachedInput": 0.30,  "cacheWrite": 3.75, "output": 15.00},
    "claude-sonnet-4.6":    {"input": 3.00, "cachedInput": 0.30,  "cacheWrite": 3.75, "output": 15.00},
    "claude-opus-4.5":      {"input": 5.00, "cachedInput": 0.50,  "cacheWrite": 6.25, "output": 25.00},
    "claude-opus-4.6":      {"input": 5.00, "cachedInput": 0.50,  "cacheWrite": 6.25, "output": 25.00},
    "claude-opus-4.7":      {"input": 5.00, "cachedInput": 0.50,  "cacheWrite": 6.25, "output": 25.00},
    "claude-opus-4.8":      {"input": 5.00, "cachedInput": 0.50,  "cacheWrite": 6.25, "output": 25.00},
    "gemini-2.5-pro":       {"input": 1.25, "cachedInput": 0.125, "output": 10.00},
    "gemini-3-flash":       {"input": 0.50, "cachedInput": 0.05,  "output": 3.00},
    "gemini-3.1-pro":       {"input": 2.00, "cachedInput": 0.20,  "output": 12.00},
    "grok-code-fast-1":     {"input": 0.20, "cachedInput": 0.02,  "output": 1.50},
    "raptor-mini":          {"input": 0.25, "cachedInput": 0.025, "output": 2.00},
    "goldeneye":            {"input": 1.25, "cachedInput": 0.125, "output": 10.00},
}


def parse_timestamp(ts_str):
    return datetime.fromisoformat(ts_str.replace("Z", "+00:00"))


def main():
    if len(sys.argv) < 2:
        print("usage: statistics.py <session-dir>", file=sys.stderr)
        sys.exit(1)

    session_dir = sys.argv[1]
    if os.path.isdir(session_dir):
        pattern = os.path.join(session_dir, "session-state", "*", "*.jsonl")
        jsonl_files = sorted(glob.glob(pattern))
        if not jsonl_files:
            print(f"no .jsonl files found in {session_dir}", file=sys.stderr)
            sys.exit(1)
        path = jsonl_files[0]
    else:
        path = session_dir

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
        print("no session.shutdown event found in session: could not retrieve copilot session stats", file=sys.stderr)
        sys.exit(1)

    data = shutdown["data"]
    model_metrics = data.get("modelMetrics", {})

    input_tokens = 0
    output_tokens = 0
    cache_read_tokens = 0
    cache_write_tokens = 0
    reasoning_tokens = 0
    total_requests = 0
    cost_input = 0.0
    cost_output = 0.0
    cost_cache_read = 0.0
    cost_cache_write = 0.0

    for model_name, model_data in model_metrics.items():
        pricing = MODEL_PRICING.get(model_name)
        usage = model_data.get("usage", {})
        requests_data = model_data.get("requests", {})

        input_tokens += usage.get("inputTokens", 0)
        output_tokens += usage.get("outputTokens", 0)
        cache_read_tokens += usage.get("cacheReadTokens", 0)
        cache_write_tokens += usage.get("cacheWriteTokens", 0)
        reasoning_tokens += usage.get("reasoningTokens", 0)
        total_requests += requests_data.get("count", 0)

        if pricing:
            cost_input += input_tokens * pricing["input"] / 1_000_000
            cost_output += output_tokens * pricing["output"] / 1_000_000
            cost_cache_read += cache_read_tokens * pricing.get("cachedInput", 0) / 1_000_000
            cost_cache_write += cache_write_tokens * pricing.get("cacheWrite", 0) / 1_000_000

    total_duration_ms = data.get("totalApiDurationMs", 0)
    if total_duration_ms == 0 and first_ts and last_ts:
        total_duration_ms = (last_ts - first_ts).total_seconds() * 1000

    result = {
        "input_tokens": input_tokens,
        "output_tokens": output_tokens,
        "cache_read_tokens": cache_read_tokens,
        "cache_write_tokens": cache_write_tokens,
        "reasoning_tokens": reasoning_tokens,
        "total_tokens": input_tokens + output_tokens + cache_read_tokens + cache_write_tokens,
        "total_requests": total_requests,
        "cost_input": round(cost_input, 8),
        "cost_output": round(cost_output, 8),
        "cost_cache_read": round(cost_cache_read, 8),
        "cost_cache_write": round(cost_cache_write, 8),
        "total_cost": round(cost_input + cost_output + cost_cache_read + cost_cache_write, 8),
        "total_turns": turn_count,
        "total_tool_calls": tool_call_count,
        "duration_seconds": total_duration_ms / 1000,
    }

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
