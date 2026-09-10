import glob
import json
import os
from datetime import datetime

from stats_protocol import Stats, calculate_price


def parse_timestamp(ts_str):
    return datetime.fromisoformat(ts_str.replace("Z", "+00:00"))


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


def _compute_otel_usage(path: str):
    """Sum completed LLM calls from Copilot's streaming OTel JSONL file.

    Copilot writes a chat span when each model request completes.  Only chat
    spans are counted: invoke_agent spans contain cumulative usage and would
    double-count the same tokens.  A timeout can leave the final JSONL line
    incomplete, so malformed lines are ignored while retaining earlier calls.
    """
    total_cost = 0.0
    total_input_tokens = 0
    total_output_tokens = 0
    chat_span_count = 0

    with open(path, encoding="utf-8") as f:
        for line in f:
            if not line.strip():
                continue
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue

            attributes = event.get("attributes", {})
            if not isinstance(attributes, dict):
                continue
            if (
                event.get("type") != "span"
                or attributes.get("gen_ai.operation.name") != "chat"
            ):
                continue

            chat_span_count += 1
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

            # OTel specifies both cache counters as subsets of input_tokens.
            uncached_input_tokens = max(
                input_tokens - cache_read_tokens - cache_write_tokens, 0
            )
            total_cost += calculate_price(
                model,
                uncached_input_tokens,
                cache_read_tokens,
                cache_write_tokens,
                output_tokens,
            )
            total_input_tokens += input_tokens
            total_output_tokens += output_tokens

    if not chat_span_count:
        return None
    return total_cost, total_input_tokens, total_output_tokens


def _compute_output_statistics(path: str, otel_path: str | None = None) -> Stats:
    """Read Copilot's programmatic JSONL output when it is available."""
    tool_call_count = 0
    turn_count = 0
    first_ts = None
    last_ts = None
    result = None
    total_cost = 0.0
    total_input_tokens = 0
    total_output_tokens = 0

    with open(path) as f:
        for line in f:
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

            etype = event.get("type")
            if etype == "tool.execution_start":
                tool_call_count += 1
            elif etype == "assistant.turn_start":
                turn_count += 1
            elif etype == "model.model_call_success":
                model, token_counts = _model_call_usage(_output_event_data(event))
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
            elif etype == "result":
                result = _output_event_data(event)

    if otel_path and os.path.isfile(otel_path):
        otel_usage = _compute_otel_usage(otel_path)
        if otel_usage is not None:
            total_cost, total_input_tokens, total_output_tokens = otel_usage

    usage = result.get("usage", {}) if result else {}
    duration_ms = usage.get("totalApiDurationMs", usage.get("sessionDurationMs", 0))
    if not duration_ms and first_ts and last_ts:
        duration_ms = (last_ts - first_ts).total_seconds() * 1000

    return Stats(
        total_costs=round(total_cost, 8),
        total_input_tokens=total_input_tokens,
        total_output_tokens=total_output_tokens,
        total_turns=turn_count,
        total_tool_calls=tool_call_count,
        duration_seconds=duration_ms / 1000,
        session_file=os.path.relpath(path),
    )


def compute_statistics(session_dir: str) -> Stats:
    if os.path.isdir(session_dir):
        output_path = os.path.join(session_dir, "session.jsonl")
        if os.path.isfile(output_path):
            otel_path = os.path.join(session_dir, "otel.jsonl")
            return _compute_output_statistics(output_path, otel_path)

        pattern = os.path.join(session_dir, "session-state", "*", "*.jsonl")
        jsonl_files = sorted(glob.glob(pattern))
        if not jsonl_files:
            # A provider can fail before Copilot creates its session event log
            # (for example, while the custom proxy is starting). Keep the
            # agent failure as the primary result instead of raising a second,
            # misleading statistics error.
            return Stats(session_file="")
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

        total_cost += calculate_price(
            model_name,
            usage.get("inputTokens", 0),
            usage.get("cacheReadTokens", 0),
            usage.get("cacheWriteTokens", 0),
            usage.get("outputTokens", 0),
        )

    total_duration_ms = data.get("totalApiDurationMs", 0)
    if total_duration_ms == 0 and first_ts and last_ts:
        total_duration_ms = (last_ts - first_ts).total_seconds() * 1000

    return Stats(
        total_costs=round(total_cost, 8),
        total_input_tokens=input_tokens + cache_read_tokens + cache_write_tokens,
        total_output_tokens=output_tokens,
        total_turns=turn_count,
        total_tool_calls=tool_call_count,
        duration_seconds=total_duration_ms / 1000,
        session_file=os.path.relpath(path),
    )
