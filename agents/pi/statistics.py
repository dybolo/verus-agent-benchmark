import json
import os
from datetime import datetime

from stats_protocol import (
    Stats,
    ToolCallType,
    calculate_price,
    empty_tool_call_counts,
)


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


def _tool_call_type(tool_name: str) -> ToolCallType:
    """Map Pi tool names to the three benchmark categories.

    Agent-control tools do not operate on the task environment and are not
    included in the tool-call metric.
    """
    match tool_name:
        case "read" | "grep" | "find" | "glob" | "ls":
            return ToolCallType.READ
        case "bash":
            return ToolCallType.SHELL_COMMAND
        case "edit" | "write" | "apply_patch":
            return ToolCallType.PATCH
        case "task" | "todowrite" | "task_complete" | "skill":
            return ToolCallType.Other
        case _:
            raise ValueError(f"unknown Pi tool type {tool_name!r}")


def compute_statistics(session_dir: str) -> Stats:
    if os.path.isdir(session_dir):
        jsonl_files = sorted(f for f in os.listdir(session_dir) if f.endswith(".jsonl"))
        if not jsonl_files:
            raise FileNotFoundError(f"no .jsonl files found in {session_dir}")
        path = os.path.join(session_dir, jsonl_files[0])
    else:
        path = session_dir

    cost_total = 0.0
    input_tokens = 0
    output_tokens = 0
    tool_call_ids = set()
    tool_calls_by_type = empty_tool_call_counts()
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

            # Counted Pi messages:
            # - message.message.usage: token usage for one model response.
            # - assistant message content blocks with type=toolCall: one tool
            #   invocation, deduplicated by the block's call id.
            match event.get("type"):
                case "message":
                    msg = event.get("message", {})
                    role = msg.get("role")
                    if role == "assistant":
                        assistant_msg_count += 1
                        usage = msg.get("usage")
                        if usage:
                            cost_total += _usage_cost(msg.get("model"), usage)
                            input_tokens += (
                                usage.get("input", 0)
                                + usage.get("cacheRead", 0)
                                + usage.get("cacheWrite", 0)
                            )
                            output_tokens += usage.get("output", 0)
                        for block in msg.get("content", []):
                            if not isinstance(block, dict):
                                continue
                            match block.get("type"):
                                case "toolCall":
                                    category = _tool_call_type(
                                        block.get("name", "")
                                    )
                                    call_id = block.get("id")
                                    if (
                                        call_id
                                        and call_id not in tool_call_ids
                                    ):
                                        tool_call_ids.add(call_id)
                                        tool_calls_by_type[category] += 1
                                case _:
                                    pass
                case _:
                    pass

    if first_ts is None or last_ts is None:
        raise RuntimeError("could not determine session timestamps")

    duration_seconds = (last_ts - first_ts).total_seconds()

    return Stats(
        total_costs=round(cost_total, 8),
        total_input_tokens=input_tokens,
        total_output_tokens=output_tokens,
        total_turns=assistant_msg_count,
        total_tool_calls=sum(tool_calls_by_type.values()),
        tool_calls_by_type=tool_calls_by_type,
        duration_seconds=duration_seconds,
        session_file=os.path.relpath(path),
    )
