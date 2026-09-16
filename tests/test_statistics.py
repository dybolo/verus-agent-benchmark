import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def load_statistics(agent):
    path = ROOT / "agents" / agent / "statistics.py"
    spec = importlib.util.spec_from_file_location(f"test_{agent}_statistics", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.compute_statistics


def write_jsonl(path, events):
    path.write_text(
        "".join(json.dumps(event) + "\n" for event in events), encoding="utf-8"
    )


class StatisticsTest(unittest.TestCase):
    def assert_tool_counts(self, stats, read, shell_command, patch, other):
        expected = {
            "read": read,
            "shell_command": shell_command,
            "patch": patch,
            "other": other,
        }
        self.assertEqual(stats.tool_calls_by_type, expected)
        self.assertEqual(stats.total_tool_calls, sum(expected.values()))

    def test_pi_counts_assistant_usage_and_tool_call_blocks(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "session.jsonl"
            write_jsonl(
                path,
                [
                    {
                        "type": "message",
                        "timestamp": "2026-09-01T00:00:00Z",
                        "message": {
                            "role": "assistant",
                            "model": "gpt-5.6-luna",
                            "usage": {
                                "input": 10,
                                "cacheRead": 2,
                                "cacheWrite": 0,
                                "output": 3,
                            },
                            "content": [
                                {"type": "toolCall", "id": "r", "name": "read"},
                                {"type": "toolCall", "id": "s", "name": "bash"},
                                {"type": "toolCall", "id": "p", "name": "edit"},
                                {"type": "toolCall", "id": "ignored", "name": "task"},
                            ],
                        },
                    },
                    {
                        "type": "message",
                        "timestamp": "2026-09-01T00:00:01Z",
                        "message": {"role": "user", "content": []},
                    },
                ],
            )
            stats = load_statistics("pi")(str(path))

        self.assertEqual(stats.total_input_tokens, 12)
        self.assertEqual(stats.total_output_tokens, 3)
        self.assert_tool_counts(stats, 1, 1, 1, 1)

    def test_opencode_counts_tool_use_regardless_of_status(self):
        with tempfile.TemporaryDirectory() as directory:
            task_dir = (
                Path(directory)
                / "sessions"
                / "opencode"
                / "gpt-5.6-luna"
                / "run"
                / "task"
            )
            task_dir.mkdir(parents=True)
            path = task_dir / "session.jsonl"
            events = [
                {
                    "type": "step_finish",
                    "timestamp": 1_000,
                    "part": {
                        "tokens": {
                            "input": 10,
                            "output": 3,
                            "reasoning": 2,
                            "cache": {"read": 4, "write": 0},
                        }
                    },
                },
                {"type": "other", "timestamp": 2_000},
            ]
            for call_id, tool, status in (
                ("r", "read", "error"),
                ("s", "bash", "completed"),
                ("p", "apply_patch", "error"),
                ("ignored", "todowrite", "completed"),
            ):
                events.append(
                    {
                        "type": "tool_use",
                        "timestamp": 1_500,
                        "part": {
                            "type": "tool",
                            "tool": tool,
                            "callID": call_id,
                            "state": {"status": status},
                        },
                    }
                )
            write_jsonl(path, events)
            stats = load_statistics("opencode")(str(path))

        self.assertEqual(stats.total_input_tokens, 14)
        self.assertEqual(stats.total_output_tokens, 5)
        self.assert_tool_counts(stats, 1, 1, 1, 1)

    def test_codex_counts_started_commands_and_file_changes_once(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "session.jsonl"
            events = [
                {"type": "session.started", "received_at": "2026-09-01T00:00:00Z"},
                {"type": "turn.started", "id": "turn", "received_at": "2026-09-01T00:00:00Z"},
            ]
            for event_type in ("item.started", "item.completed"):
                events.extend(
                    [
                        {
                            "type": event_type,
                            "item": {"id": "s", "type": "command_execution"},
                            "received_at": "2026-09-01T00:00:01Z",
                        },
                        {
                            "type": event_type,
                            "item": {"id": "p", "type": "file_change"},
                            "received_at": "2026-09-01T00:00:01Z",
                        },
                    ]
                )
            events.append(
                {
                    "type": "turn.completed",
                    "usage": {
                        "input_tokens": 100,
                        "cached_input_tokens": 40,
                        "output_tokens": 10,
                    },
                    "received_at": "2026-09-01T00:00:02Z",
                }
            )
            write_jsonl(path, events)
            stats = load_statistics("codex")(str(path))

        self.assertEqual(stats.total_input_tokens, 100)
        self.assertEqual(stats.total_output_tokens, 10)
        self.assert_tool_counts(stats, 0, 1, 1, 0)

    def test_copilot_merges_session_and_otel_calls_by_response_id(self):
        with tempfile.TemporaryDirectory() as directory:
            session_path = Path(directory) / "session.jsonl"
            otel_path = Path(directory) / "otel.jsonl"
            session_events = []
            for call_id, tool in (
                ("r", "view"),
                ("s", "bash"),
                ("p", "apply_patch"),
                ("ignored", "task_complete"),
            ):
                session_events.append(
                    {
                        "type": "tool.execution_start",
                        "timestamp": "2026-09-01T00:00:00Z",
                        "data": {"toolCallId": call_id, "toolName": tool},
                    }
                )
            session_events.append(
                {
                    "type": "model.model_call_success",
                    "timestamp": "2026-09-01T00:00:01Z",
                    "data": {
                        "responseChunk": {
                            "id": "response-a",
                            "model": "gpt-5.6-luna",
                            "usage": {
                                "prompt_tokens": 100,
                                "completion_tokens": 10,
                                "prompt_tokens_details": {"cached_tokens": 40},
                            },
                        }
                    },
                }
            )
            write_jsonl(session_path, session_events)

            def span(response_id, input_tokens, output_tokens, cached_tokens):
                return {
                    "type": "span",
                    "attributes": {
                        "gen_ai.operation.name": "chat",
                        "gen_ai.response.id": response_id,
                        "gen_ai.response.model": "gpt-5.6-luna",
                        "gen_ai.usage.input_tokens": input_tokens,
                        "gen_ai.usage.output_tokens": output_tokens,
                        "gen_ai.usage.cache_read.input_tokens": cached_tokens,
                    },
                }

            write_jsonl(
                otel_path,
                [span("response-a", 100, 10, 40), span("response-b", 200, 20, 128)],
            )
            stats = load_statistics("copilot")(directory)

        self.assertEqual(stats.total_input_tokens, 300)
        self.assertEqual(stats.total_output_tokens, 30)
        self.assert_tool_counts(stats, 1, 1, 1, 1)


if __name__ == "__main__":
    unittest.main()
