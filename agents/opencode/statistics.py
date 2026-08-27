import json
import os

from stats_protocol import Stats

# USD per one million tokens. ChatGPT subscription sessions do not include a
# billable API price in OpenCode's `cost` field, so use the equivalent API
# pricing when calculating comparable benchmark costs.
MODEL_PRICING = {
    "gpt-5.6-luna": {"input": 0.20, "cached_input": 0.02, "output": 1.20},
    "gpt-5.6-terra": {"input": 2.00, "cached_input": 0.20, "output": 12.00},
}


def _model_name(session_dir: str) -> str | None:
    """Infer the model from the benchmark session layout."""
    path = session_dir if os.path.isdir(session_dir) else os.path.dirname(session_dir)
    # sessions/<agent>/<model>/<run>/<task>/
    parts = os.path.normpath(path).split(os.sep)
    try:
        sessions_index = len(parts) - 1 - parts[::-1].index("sessions")
    except ValueError:
        return None
    if len(parts) > sessions_index + 2:
        return parts[sessions_index + 2]
    return None


def compute_statistics(session_dir: str) -> Stats:
    jsonl_path = (
        session_dir
        if os.path.isfile(session_dir)
        else os.path.join(session_dir, "session.jsonl")
    )

    if not os.path.isfile(jsonl_path):
        raise FileNotFoundError(f"no session.jsonl found at {jsonl_path}")

    # Detailed token and cost breakdown (available for inspection)
    input_tokens = 0
    output_tokens = 0
    cache_read_tokens = 0
    cache_write_tokens = 0
    reasoning_tokens = 0
    total_cost_actual = 0.0
    total_cost_estimated = 0.0
    total_requests = 0
    turn_count = 0
    tool_call_count = 0
    first_ts = None
    last_ts = None
    pricing = MODEL_PRICING.get(_model_name(session_dir))

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
                reported_cost = part.get("cost")
                if isinstance(reported_cost, (int, float)) and reported_cost > 0:
                    total_cost_actual += reported_cost
                elif pricing:
                    # OpenCode's input token count excludes cache reads; cache
                    # reads are reported separately in `tokens.cache.read`.
                    total_cost_estimated += (
                        tokens.get("input", 0) * pricing["input"]
                        + cache.get("read", 0) * pricing["cached_input"]
                        + cache.get("write", 0) * pricing["cached_input"]
                        + tokens.get("output", 0) * pricing["output"]
                    ) / 1_000_000
                total_requests += 1
                turn_count += 1

            elif etype == "tool_use":
                part = event.get("part", {})
                state = part.get("state", {})
                if state.get("status") == "completed":
                    tool_call_count += 1

    if first_ts is None or last_ts is None:
        raise RuntimeError("could not determine session timestamps")

    duration_seconds = (last_ts - first_ts) / 1000

    # total_tokens = input_tokens + output_tokens + cache_read_tokens + cache_write_tokens

    return Stats(
        total_costs=round(total_cost_actual + total_cost_estimated, 8),
        total_turns=turn_count,
        total_tool_calls=tool_call_count,
        duration_seconds=duration_seconds,
        session_file=os.path.relpath(jsonl_path),
    )
