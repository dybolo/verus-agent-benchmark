from dataclasses import dataclass
from typing import Protocol, runtime_checkable


@dataclass
class Stats:
    total_costs: float = 0.0
    total_turns: int = 0
    total_tool_calls: int = 0
    duration_seconds: float = 0.0
    session_file: str = ""


@runtime_checkable
class StatsFn(Protocol):
    def __call__(self, session_dir: str) -> Stats: ...
