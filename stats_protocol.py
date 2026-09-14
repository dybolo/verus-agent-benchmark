from dataclasses import dataclass, field
from enum import Enum
from typing import Protocol, runtime_checkable


# USD per one million tokens. Keep benchmark pricing here so every agent uses
# the same rates independently of costs reported by the agent itself.
MODEL_PRICING = {
    "claude-sonnet-4.6": {
        "input": 3.00,
        "cached_input": 0.30,
        "cached_write": 3.75,
        "output": 15.00,
    },
    "gpt-5.6-luna": {
        "input": 0.20,
        "cached_input": 0.02,
        "cached_write": 0.25,
        "output": 1.20,
    },
}

MODEL_ALIASES = {
    # Pi records Bedrock's inference profile ID in its session events.
    "global.anthropic.claude-sonnet-4-6": "claude-sonnet-4.6",
}


class ToolCallType(str, Enum):
    READ = "read"
    SHELL_COMMAND = "shell_command"
    PATCH = "patch"
    Other = "other"


def empty_tool_call_counts() -> dict[ToolCallType, int]:
    """Return the exhaustive cross-agent tool-call categories."""
    return {tool_call_type: 0 for tool_call_type in ToolCallType}


def calculate_price(
    model: str,
    input: int,
    cached_input: int,
    cached_write: int,
    output: int,
) -> float:
    """Calculate a model call's USD price from mutually exclusive token counts."""
    pricing = MODEL_PRICING.get(MODEL_ALIASES.get(model, model))
    if pricing is None:
        raise ValueError(f"no fixed pricing configured for model {model!r}")

    return (
        input * pricing["input"]
        + cached_input * pricing["cached_input"]
        + cached_write * pricing["cached_write"]
        + output * pricing["output"]
    ) / 1_000_000


@dataclass
class Stats:
    total_costs: float = 0.0
    total_input_tokens: int = 0
    total_output_tokens: int = 0
    total_turns: int = 0
    total_tool_calls: int = 0
    tool_calls_by_type: dict[ToolCallType, int] = field(
        default_factory=empty_tool_call_counts
    )
    duration_seconds: float = 0.0
    session_file: str = ""


@runtime_checkable
class StatsFn(Protocol):
    def __call__(self, session_dir: str) -> Stats: ...
