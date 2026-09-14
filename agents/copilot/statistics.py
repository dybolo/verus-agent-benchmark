import glob
import json
import os
from datetime import datetime

from stats_protocol import (
    Stats,
    ToolCallType,
    calculate_price,
    empty_tool_call_counts,
)


def parse_timestamp(ts_str):
    return datetime.fromisoformat(ts_str.replace("Z", "+00:00"))


def _tool_call_type(tool_name: str) -> ToolCallType:
    """Map Copilot tool names to the three benchmark categories."""
    match tool_name:
        case (
            "read"
            | "view"
            | "grep"
            | "rg"
            | "find"
            | "glob"
            | "read_bash"
            | "sql"
        ):
            return ToolCallType.READ
        case "bash" | "shell" | "stop_bash":
            return ToolCallType.SHELL_COMMAND
        case "apply_patch" | "edit" | "write":
            return ToolCallType.PATCH
        case (
            "task"
            | "todowrite"
            | "task_complete"
            | "list_agents"
            | "read_agent"
            | "write_agent"
        ):
            return ToolCallType.Other
        case _:
            raise ValueError(f"unknown Copilot tool type {tool_name!r}")


def _output_event_data(event):
    """Return the payload for either a top-level or wrapped output event."""
    data = event.get("data")
    return data if isinstance(data, dict) else event


def _model_call_usage(data):
    """Return the model and mutually exclusive token buckets for one call."""
    response_chunk = data.get("responseChunk", {})
    copilot_usage = response_chunk.get("copilot_usage", {})
    token_details = copilot_usage.get("token_details", [])
    model = data.get("model")
    model_call = data.get("modelCall", {})
    if not model and isinstance(model_call, dict):
        model = model_call.get("model")
    if not model:
        model = response_chunk.get("model")

    token_counts = {"input": 0, "cache_read": 0, "cache_write": 0, "output": 0}
    for detail in token_details:
        token_type = detail.get("token_type")
        if token_type in token_counts:
            token_counts[token_type] += detail.get("token_count", 0)

    if not token_details:
        usage = response_chunk.get("usage", {})
        details = usage.get("prompt_tokens_details", {})
        token_counts["cache_read"] = details.get("cached_tokens", 0)
        token_counts["cache_write"] = details.get(
            "cache_write_tokens", details.get("cache_creation_tokens", 0)
        )
        token_counts["input"] = max(
            usage.get("prompt_tokens", 0)
            - token_counts["cache_read"]
            - token_counts["cache_write"],
            0,
        )
        token_counts["output"] = usage.get("completion_tokens", 0)

    return model, token_counts


def _otel_attribute(attributes, name, *aliases, default=0):
    for key in (name, *aliases):
        if key in attributes:
            return attributes[key]
    return default


def _compute_otel_model_calls(path: str):
    """Read model calls from Copilot's streaming OTel JSONL file.

    Only chat spans contain per-request usage. invoke_agent spans contain
    cumulative usage and would double-count tokens. Calls are keyed by response
    id so they can be merged with model.model_call_success messages.
    """
    model_calls = {}

    with open(path, encoding="utf-8") as f:
        for line_number, line in enumerate(f, start=1):
            if not line.strip():
                continue
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue

            # Counted OTel messages: span events whose operation is chat and
            # which contain non-zero per-response token usage.
            match event.get("type"):
                case "span":
                    attributes = event.get("attributes", {})
                    if not isinstance(attributes, dict):
                        continue
                    if attributes.get("gen_ai.operation.name") != "chat":
                        continue
                case _:
                    continue

            model = (
                attributes.get("gen_ai.response.model")
                or attributes.get("gen_ai.request.model")
            )
            input_tokens = _otel_attribute(
                attributes, "gen_ai.usage.input_tokens"
            )
            cache_read_tokens = _otel_attribute(
                attributes,
                "gen_ai.usage.cache_read.input_tokens",
                "gen_ai.usage.cache_read_input_tokens",
            )
            cache_write_tokens = _otel_attribute(
                attributes,
                "gen_ai.usage.cache_creation.input_tokens",
                "gen_ai.usage.cache_creation_input_tokens",
            )
            output_tokens = _otel_attribute(
                attributes, "gen_ai.usage.output_tokens"
            )

            # Some instrumentation-only chat spans have a model name but no
            # response id or usage attributes. They are not model responses
            # and contribute no token usage.
            if not any(
                (
                    input_tokens,
                    cache_read_tokens,
                    cache_write_tokens,
                    output_tokens,
                )
            ):
                continue

            response_id = attributes.get("gen_ai.response.id")
            call_key = response_id or f"otel:{line_number}"
            model_calls[call_key] = (
                model,
                {
                    "input": max(
                        input_tokens - cache_read_tokens - cache_write_tokens, 0
                    ),
                    "cache_read": cache_read_tokens,
                    "cache_write": cache_write_tokens,
                    "output": output_tokens,
                },
            )

    return model_calls


def _compute_statistics_w_otel(
    path: str, otel_path: str | None = None
) -> Stats:
    """Read Copilot's programmatic session and optional OTel JSONL output."""
    tool_call_ids = set()
    tool_calls_by_type = empty_tool_call_counts()
    turn_count = 0
    first_ts = None
    last_ts = None
    result = None
    session_model_calls = {}

    with open(path) as f:
        for line_number, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                # The benchmark can terminate Copilot while it is appending
                # its final event. Earlier complete events and OTel spans are
                # still valid and should remain usable.
                continue
            ts = event.get("timestamp")
            if ts:
                dt = parse_timestamp(ts)
                if first_ts is None or dt < first_ts:
                    first_ts = dt
                if last_ts is None or dt > last_ts:
                    last_ts = dt

            # Counted Copilot messages:
            # - tool.execution_start: one attempted tool invocation,
            #   deduplicated by data.toolCallId.
            # - model.model_call_success: token usage for one model response.
            # - result: duration metadata only, not token usage.
            match event.get("type"):
                case "tool.execution_start":
                    data = _output_event_data(event)
                    category = _tool_call_type(data.get("toolName", ""))
                    call_id = data.get("toolCallId") or event.get("id")
                    if (
                        call_id
                        and call_id not in tool_call_ids
                    ):
                        tool_call_ids.add(call_id)
                        tool_calls_by_type[category] += 1
                case "assistant.turn_start":
                    turn_count += 1
                case "model.model_call_success":
                    data = _output_event_data(event)
                    model, token_counts = _model_call_usage(data)
                    response_chunk = data.get("responseChunk", {})
                    response_id = response_chunk.get("id") or response_chunk.get(
                        "response_id"
                    )
                    call_key = response_id or f"session:{line_number}"
                    session_model_calls[call_key] = (model, token_counts)
                case "result":
                    result = _output_event_data(event)
                case _:
                    pass

    # Merge both per-response sources. Either stream may be truncated, so an
    # unconditional preference loses valid calls. Session records win only for
    # duplicate response ids because they carry the same usage and often a more
    # specific model name.
    model_calls = {}
    if otel_path and os.path.isfile(otel_path):
        model_calls.update(_compute_otel_model_calls(otel_path))
    model_calls.update(session_model_calls)

    total_cost = 0.0
    total_input_tokens = 0
    total_output_tokens = 0
    for model, token_counts in model_calls.values():
        total_cost += calculate_price(
            model,
            token_counts["input"],
            token_counts["cache_read"],
            token_counts["cache_write"],
            token_counts["output"],
        )
        total_input_tokens += (
            token_counts["input"]
            + token_counts["cache_read"]
            + token_counts["cache_write"]
        )
        total_output_tokens += token_counts["output"]

    usage = result.get("usage", {}) if result else {}
    duration_ms = usage.get("totalApiDurationMs", usage.get("sessionDurationMs", 0))
    if not duration_ms and first_ts and last_ts:
        duration_ms = (last_ts - first_ts).total_seconds() * 1000

    return Stats(
        total_costs=round(total_cost, 8),
        total_input_tokens=total_input_tokens,
        total_output_tokens=total_output_tokens,
        total_turns=turn_count,
        total_tool_calls=sum(tool_calls_by_type.values()),
        tool_calls_by_type=tool_calls_by_type,
        duration_seconds=duration_ms / 1000,
        session_file=os.path.relpath(path),
    )


def _legacy_compute_statistics(path: str) -> Stats:
    """Read a legacy Copilot session-state JSONL file."""
    shutdown = None
    tool_call_ids = set()
    tool_calls_by_type = empty_tool_call_counts()
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

            # Counted legacy Copilot messages:
            # - tool.execution_start: one attempted tool invocation.
            # - assistant.turn_start: one assistant/model turn.
            # - session.shutdown: cumulative token usage, used once.
            match event.get("type"):
                case "session.shutdown":
                    shutdown = event
                case "tool.execution_start":
                    data = _output_event_data(event)
                    category = _tool_call_type(data.get("toolName", ""))
                    call_id = data.get("toolCallId") or event.get("id")
                    if (
                        call_id
                        and call_id not in tool_call_ids
                    ):
                        tool_call_ids.add(call_id)
                        tool_calls_by_type[category] += 1
                case "assistant.turn_start":
                    turn_count += 1
                case _:
                    pass

    if shutdown is None:
        raise RuntimeError("no session.shutdown event found in session: could not retrieve copilot session stats")

    data = shutdown["data"]
    model_metrics = data.get("modelMetrics", {})

    # Detailed token and cost breakdown (available for inspection)
    input_tokens = 0
    output_tokens = 0
    cache_read_tokens = 0
    cache_write_tokens = 0
    reasoning_tokens = 0
    total_requests = 0
    total_cost = 0.0

    for model_name, model_data in model_metrics.items():
        usage = model_data.get("usage", {})
        requests_data = model_data.get("requests", {})

        input_tokens += usage.get("inputTokens", 0)
        output_tokens += usage.get("outputTokens", 0)
        cache_read_tokens += usage.get("cacheReadTokens", 0)
        cache_write_tokens += usage.get("cacheWriteTokens", 0)
        reasoning_tokens += usage.get("reasoningTokens", 0)
        total_requests += requests_data.get("count", 0)

        # Shutdown inputTokens is total input; cache counters are subsets.
        total_cost += calculate_price(
            model_name,
            max(
                usage.get("inputTokens", 0)
                - usage.get("cacheReadTokens", 0)
                - usage.get("cacheWriteTokens", 0),
                0,
            ),
            usage.get("cacheReadTokens", 0),
            usage.get("cacheWriteTokens", 0),
            usage.get("outputTokens", 0),
        )

    total_duration_ms = data.get("totalApiDurationMs", 0)
    if total_duration_ms == 0 and first_ts and last_ts:
        total_duration_ms = (last_ts - first_ts).total_seconds() * 1000

    return Stats(
        total_costs=round(total_cost, 8),
        total_input_tokens=input_tokens,
        total_output_tokens=output_tokens,
        total_turns=turn_count,
        total_tool_calls=sum(tool_calls_by_type.values()),
        tool_calls_by_type=tool_calls_by_type,
        duration_seconds=total_duration_ms / 1000,
        session_file=os.path.relpath(path),
    )


def compute_statistics(session_dir: str) -> Stats:
    """Dispatch to the current session+OTel or legacy statistics format."""
    if not os.path.isdir(session_dir):
        return _legacy_compute_statistics(session_dir)

    output_path = os.path.join(session_dir, "session.jsonl")
    if os.path.isfile(output_path):
        otel_path = os.path.join(session_dir, "otel.jsonl")
        return _compute_statistics_w_otel(output_path, otel_path)

    pattern = os.path.join(session_dir, "session-state", "*", "*.jsonl")
    jsonl_files = sorted(glob.glob(pattern))
    if jsonl_files:
        return _legacy_compute_statistics(jsonl_files[0])

    # A provider can fail before Copilot creates its session event log
    # (for example, while the custom proxy is starting). Keep the agent failure
    # as the primary result instead of raising a second statistics error.
    return Stats(session_file="")
