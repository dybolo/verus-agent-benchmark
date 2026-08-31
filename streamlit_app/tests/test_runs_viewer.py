from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from streamlit_app.runs_viewer import original_task_path


class OriginalTaskPathTests(unittest.TestCase):
    def test_resolves_regular_and_full_file_tasks(self) -> None:
        with tempfile.TemporaryDirectory() as temp_directory:
            repo_root = Path(temp_directory)
            tasks = repo_root / "tasks"
            full_tasks = repo_root / "full_tasks"
            tasks.mkdir()
            full_tasks.mkdir()
            regular = tasks / "function.rs"
            full = full_tasks / "module_full.rs"
            regular.write_text("regular")
            full.write_text("full")

            self.assertEqual(original_task_path(repo_root, "function.rs"), regular.resolve())
            self.assertEqual(original_task_path(repo_root, "module_full.rs"), full.resolve())

    def test_prefers_regular_task_and_rejects_missing_or_unsafe_paths(self) -> None:
        with tempfile.TemporaryDirectory() as temp_directory:
            repo_root = Path(temp_directory)
            tasks = repo_root / "tasks"
            full_tasks = repo_root / "full_tasks"
            tasks.mkdir()
            full_tasks.mkdir()
            regular = tasks / "same.rs"
            regular.write_text("regular")
            (full_tasks / "same.rs").write_text("full")

            self.assertEqual(original_task_path(repo_root, "same.rs"), regular.resolve())
            self.assertIsNone(original_task_path(repo_root, "missing.rs"))
            self.assertIsNone(original_task_path(repo_root, "../outside.rs"))


if __name__ == "__main__":
    unittest.main()
