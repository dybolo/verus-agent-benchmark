from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "update_task_missing_lines.py"
SPEC = importlib.util.spec_from_file_location("update_task_missing_lines", SCRIPT)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"could not load {SCRIPT}")
MISSING_LINES = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MISSING_LINES
SPEC.loader.exec_module(MISSING_LINES)


class MissingCodeLineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.metadata_path = (
            ROOT / "streamlit_app" / "src" / "streamlit_app" / "task_metadata.csv"
        )
        cls.fieldnames, cls.rows = MISSING_LINES.read_metadata(cls.metadata_path)
        cls.results = MISSING_LINES.calculate_all_missing_lines(cls.rows, ROOT)

    def test_diff_counts_only_unmatched_non_empty_source_lines(self) -> None:
        source = ["same", "removed", "old version", "", "tail"]
        task = ["same", "new version", "tail", "task-only addition"]

        self.assertEqual(MISSING_LINES.count_missing_code_lines(source, task), 1)

    def test_calculates_every_metadata_task(self) -> None:
        self.assertEqual(len(self.results), 92)
        self.assertEqual(
            {row["task_id"] for row in self.rows},
            {result.task_id for result in self.results},
        )
        self.assertTrue(all(result.missing_code_lines > 0 for result in self.results))

    def test_uses_the_directory_selected_by_proof_style(self) -> None:
        by_task = {result.task_id: result for result in self.results}

        self.assertEqual(by_task["cuckoo_delete"].task_path.parent, ROOT / "tasks")
        self.assertEqual(by_task["context_full"].task_path.parent, ROOT / "full_tasks")

    def test_representative_missing_line_counts(self) -> None:
        by_task = {result.task_id: result for result in self.results}

        self.assertEqual(by_task["cuckoo_delete"].missing_code_lines, 19)
        self.assertEqual(by_task["wait"].missing_code_lines, 11)
        self.assertEqual(by_task["free_free_block_mt"].missing_code_lines, 55)
        self.assertEqual(by_task["context_full"].missing_code_lines, 21)

    def test_checked_in_metadata_is_current(self) -> None:
        self.assertIn(MISSING_LINES.MISSING_CODE_LINES_COLUMN, self.fieldnames)
        self.assertTrue(MISSING_LINES.metadata_is_current(self.rows, self.results))

    def test_writing_metadata_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            metadata_path = Path(directory) / "task_metadata.csv"
            MISSING_LINES.write_metadata(
                metadata_path, self.fieldnames, self.rows, self.results
            )
            first = metadata_path.read_bytes()
            fields, rows = MISSING_LINES.read_metadata(metadata_path)
            MISSING_LINES.write_metadata(metadata_path, fields, rows, self.results)
            second = metadata_path.read_bytes()

        self.assertEqual(first, second)


if __name__ == "__main__":
    unittest.main()
