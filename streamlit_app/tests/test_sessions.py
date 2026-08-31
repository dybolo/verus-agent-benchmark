from __future__ import annotations

import unittest

from streamlit_app.sessions import (
    normalize_codex,
    normalize_opencode,
    normalize_session,
)


class SessionNormalizationTests(unittest.TestCase):
    def test_codex_pairs_item_updates_and_uses_received_at(self) -> None:
        events = [
            {"type": "session.started", "received_at": "2026-08-29T10:00:00Z"},
            {
                "type": "item.started",
                "item": {
                    "id": "item_1",
                    "type": "command_execution",
                    "command": "cargo test",
                    "aggregated_output": "",
                    "status": "in_progress",
                },
                "received_at": "2026-08-29T10:00:01Z",
            },
            {
                "type": "item.completed",
                "item": {
                    "id": "item_1",
                    "type": "command_execution",
                    "command": "cargo test",
                    "aggregated_output": "all tests passed",
                    "exit_code": 0,
                    "status": "completed",
                },
                "received_at": "2026-08-29T10:00:03Z",
            },
            {
                "type": "item.completed",
                "item": {"id": "item_2", "type": "agent_message", "text": "Done."},
                "received_at": "2026-08-29T10:00:04Z",
            },
        ]

        items = normalize_codex(events)

        self.assertEqual([item.kind for item in items], ["event", "tool", "message"])
        self.assertEqual(items[1].input, "cargo test")
        self.assertEqual(items[1].output, "all tests passed")
        self.assertEqual(items[1].status, "completed")
        self.assertEqual(items[2].body, "Done.")

    def test_codex_normalizes_file_web_todo_and_error_items(self) -> None:
        events = [
            {
                "type": "item.completed",
                "item": {
                    "id": "file",
                    "type": "file_change",
                    "changes": [{"path": "answer.rs", "kind": "update"}],
                    "status": "failed",
                },
            },
            {
                "type": "item.completed",
                "item": {
                    "id": "web", "type": "web_search", "query": "Verus guide",
                    "action": {"type": "search", "query": "Verus guide"},
                },
            },
            {
                "type": "item.updated",
                "item": {
                    "id": "todo", "type": "todo_list",
                    "items": [{"text": "Verify", "completed": True}],
                },
            },
            {
                "type": "item.completed",
                "item": {"id": "error", "type": "error", "message": "bad config"},
            },
        ]

        items = normalize_codex(events)

        self.assertEqual([item.title for item in items], ["File changes", "Web search", "Todo list", "Error"])
        self.assertEqual(items[0].status, "error")
        self.assertEqual(items[1].input["query"], "Verus guide")
        self.assertEqual(items[2].details[0]["completed"], True)
        self.assertEqual(items[3].body, "bad config")

    def test_opencode_uses_tool_error_when_output_is_missing(self) -> None:
        events = [
            {
                "type": "tool_use",
                "part": {"tool": "shell", "state": {"output": None, "error": "failed"}},
            }
        ]

        items = normalize_opencode(events)

        self.assertEqual(items[0].output, "failed")

    def test_normalize_session_calculates_elapsed_time(self) -> None:
        events = [
            {"type": "text", "timestamp": 1, "part": {"text": "first"}},
            {"type": "text", "timestamp": 3, "part": {"text": "second"}},
        ]

        items = normalize_session(events, "opencode/model")

        self.assertEqual([item.elapsed_seconds for item in items], [0.0, 2.0])


if __name__ == "__main__":
    unittest.main()
