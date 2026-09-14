import json
import os

from stats_protocol import (
    Stats,
    ToolCallType,
    calculate_price,
    empty_tool_call_counts,
)


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


def _tool_call_type(tool_name: str) -> ToolCallType:
    """Map OpenCode tool names to the three benchmark categories."""
    match tool_name:
        case "read" | "grep" | "rg" | "find" | "glob" | "view":
            return ToolCallType.READ
        case "bash":
            return ToolCallType.SHELL_COMMAND
        case "apply_patch" | "edit" | "write":
            return ToolCallType.PATCH
        case "task" | "todowrite" | "task_complete" | "skill":
            return ToolCallType.Other
        case _:
            raise ValueError(f"unknown OpenCode tool type {tool_name!r}")


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
    total_cost = 0.0
    total_requests = 0
    turn_count = 0
    tool_call_ids = set()
    tool_calls_by_type = empty_tool_call_counts()
    first_ts = None
    last_ts = None
    model_name = _model_name(session_dir)

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

            # Counted OpenCode messages:
            # - step_finish.part.tokens: token usage for one model request.
            # - tool_use: one attempted tool invocation, regardless of the
            #   state.status outcome, deduplicated by part.callID.
            match event.get("type"):
                case "step_finish":
                    part = event.get("part", {})
                    tokens = part.get("tokens", {})
                    # OpenCode reports visible output and reasoning as separate,
                    # additive generated-token buckets. Both are billed at the
                    # model's output rate and must be included in output totals.
                    step_output_tokens = tokens.get("output", 0) + tokens.get(
                        "reasoning", 0
                    )
                    input_tokens += tokens.get("input", 0)
                    output_tokens += step_output_tokens
                    cache = tokens.get("cache", {})
                    cache_read_tokens += cache.get("read", 0)
                    cache_write_tokens += cache.get("write", 0)
                    # OpenCode reports input and cache tokens as separate buckets.
                    total_cost += calculate_price(
                        model_name,
                        tokens.get("input", 0),
                        cache.get("read", 0),
                        cache.get("write", 0),
                        step_output_tokens,
                    )
                    total_requests += 1
                    turn_count += 1
                case "tool_use":
                    part = event.get("part", {})
                    category = _tool_call_type(part.get("tool", ""))
                    call_id = part.get("callID") or part.get("id")
                    if (
                        call_id
                        and call_id not in tool_call_ids
                    ):
                        tool_call_ids.add(call_id)
                        tool_calls_by_type[category] += 1
                case _:
                    pass

    if first_ts is None or last_ts is None:
        raise RuntimeError("could not determine session timestamps")

    duration_seconds = (last_ts - first_ts) / 1000

    return Stats(
        total_costs=round(total_cost, 8),
        total_input_tokens=input_tokens + cache_read_tokens + cache_write_tokens,
        total_output_tokens=output_tokens,
        total_turns=turn_count,
        total_tool_calls=sum(tool_calls_by_type.values()),
        tool_calls_by_type=tool_calls_by_type,
        duration_seconds=duration_seconds,
        session_file=os.path.relpath(jsonl_path),
    )
