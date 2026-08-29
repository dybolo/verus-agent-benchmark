import glob
import json
import os
from datetime import datetime

from stats_protocol import Stats

MODEL_PRICING = {
    "gpt-5.6-luna":         {"input": 0.20, "cachedInput": 0.02,  "cacheWrite": 0.25, "output": 1.20},
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


def _output_event_data(event):
    """Return the payload for either a top-level or wrapped output event."""
    data = event.get("data")
    return data if isinstance(data, dict) else event


def _model_call_cost(data):
    """Calculate the cost of one model call from Copilot's usage details."""
    response_chunk = data.get("responseChunk", {})
    copilot_usage = response_chunk.get("copilot_usage", {})
    token_details = copilot_usage.get("token_details", [])
    model = data.get("model")
    model_call = data.get("modelCall", {})
    if not model and isinstance(model_call, dict):
        model = model_call.get("model")
    if not model:
        model = response_chunk.get("model")

    pricing = MODEL_PRICING.get(model)
    if pricing:
        prices = pricing
    else:
        billing = data.get("modelInfo", {}).get("billing", {})
        default_prices = billing.get("token_prices", {}).get("default", {})
        if not default_prices:
            return 0.0
        discount = billing.get("auto_discount", 0.0)
        prices = {
            "input": default_prices.get("input_price", 0) / 100 * (1 - discount),
            "cachedInput": default_prices.get("cache_read_price", 0) / 100 * (1 - discount),
            "cacheWrite": default_prices.get("cache_write_price", 0) / 100 * (1 - discount),
            "output": default_prices.get("output_price", 0) / 100 * (1 - discount),
        }

    token_counts = {"input": 0, "cache_read": 0, "cache_write": 0, "output": 0}
    for detail in token_details:
        token_type = detail.get("token_type")
        if token_type in token_counts:
            token_counts[token_type] += detail.get("token_count", 0)

    if not token_details:
        usage = response_chunk.get("usage", {})
        details = usage.get("prompt_tokens_details", {})
        token_counts["cache_read"] = details.get("cached_tokens", 0)
        token_counts["input"] = max(usage.get("prompt_tokens", 0) - token_counts["cache_read"], 0)
        token_counts["output"] = usage.get("completion_tokens", 0)

    return (
        token_counts["input"] * prices["input"]
        + token_counts["cache_read"] * prices.get("cachedInput", 0)
        + token_counts["cache_write"] * prices.get("cacheWrite", 0)
        + token_counts["output"] * prices["output"]
    ) / 1_000_000


def _otel_attribute(attributes, name, *aliases, default=0):
    for key in (name, *aliases):
        if key in attributes:
            return attributes[key]
    return default


def _compute_otel_cost(path: str):
    """Sum completed LLM calls from Copilot's streaming OTel JSONL file.

    Copilot writes a chat span when each model request completes.  Only chat
    spans are counted: invoke_agent spans contain cumulative usage and would
    double-count the same tokens.  A timeout can leave the final JSONL line
    incomplete, so malformed lines are ignored while retaining earlier calls.
    """
    total_cost = 0.0
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
            pricing = MODEL_PRICING.get(model)
            if pricing is None:
                # Copilot documents this as the monetary cost of this chat
                # span. Prefer fixed benchmark pricing whenever the model is
                # known so costs remain comparable across agent harnesses.
                reported_cost = attributes.get("github.copilot.cost", 0)
                if isinstance(reported_cost, (int, float)):
                    total_cost += reported_cost
                continue

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
            total_cost += (
                uncached_input_tokens * pricing["input"]
                + cache_read_tokens * pricing.get("cachedInput", 0)
                + cache_write_tokens * pricing.get("cacheWrite", 0)
                + output_tokens * pricing["output"]
            ) / 1_000_000

    return total_cost if chat_span_count else None


def _compute_output_statistics(path: str, otel_path: str | None = None) -> Stats:
    """Read Copilot's programmatic JSONL output when it is available."""
    tool_call_count = 0
    turn_count = 0
    first_ts = None
    last_ts = None
    result = None
    total_cost = 0.0

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
                total_cost += _model_call_cost(_output_event_data(event))
            elif etype == "result":
                result = _output_event_data(event)

    if otel_path and os.path.isfile(otel_path):
        otel_cost = _compute_otel_cost(otel_path)
        if otel_cost is not None:
            total_cost = otel_cost

    usage = result.get("usage", {}) if result else {}
    duration_ms = usage.get("totalApiDurationMs", usage.get("sessionDurationMs", 0))
    if not duration_ms and first_ts and last_ts:
        duration_ms = (last_ts - first_ts).total_seconds() * 1000

    return Stats(
        total_costs=round(total_cost, 8),
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

    # total_tokens = input_tokens + output_tokens + cache_read_tokens + cache_write_tokens
    # total_cost = cost_input + cost_output + cost_cache_read + cost_cache_write

    return Stats(
        total_costs=round(cost_input + cost_output + cost_cache_read + cost_cache_write, 8),
        total_turns=turn_count,
        total_tool_calls=tool_call_count,
        duration_seconds=total_duration_ms / 1000,
        session_file=os.path.relpath(path),
    )
