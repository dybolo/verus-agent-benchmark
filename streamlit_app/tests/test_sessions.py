from __future__ import annotations

import unittest

from streamlit_app.sessions import normalize_opencode, normalize_session


class SessionNormalizationTests(unittest.TestCase):
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
