from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "update_task_method_sizes.py"
SPEC = importlib.util.spec_from_file_location("update_task_method_sizes", SCRIPT)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"could not load {SCRIPT}")
METHOD_SIZES = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = METHOD_SIZES
SPEC.loader.exec_module(METHOD_SIZES)


class MethodSizeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.metadata_path = (
            ROOT / "streamlit_app" / "src" / "streamlit_app" / "task_metadata.csv"
        )
        cls.fieldnames, cls.rows = METHOD_SIZES.read_metadata(cls.metadata_path)
        cls.sizes = METHOD_SIZES.calculate_all_sizes(cls.rows, ROOT)

    def test_manifest_covers_every_metadata_task(self) -> None:
        metadata_ids = {row["task_id"] for row in self.rows}

        self.assertEqual(len(metadata_ids), 92)
        self.assertEqual(metadata_ids, set(METHOD_SIZES.TASK_SPECS))
        self.assertTrue(all(size.method_lines > 0 for size in self.sizes))

    def test_composite_and_duplicate_name_tasks_use_hard_coded_ranges(self) -> None:
        by_task = {size.task_id: size for size in self.sizes}

        self.assertEqual(by_task["wait"].method_lines, 84)
        self.assertEqual(by_task["wait"].targets, ("wake_one", "wake_all", "enqueue"))
        self.assertEqual(by_task["cuckoo_inductive"].method_lines, 76)
        self.assertEqual(by_task["helping_full"].method_lines, 171)
        self.assertEqual(by_task["linked_list_take"].method_lines, 37)
        self.assertEqual(by_task["linked_list_take_"].method_lines, 52)

    def test_checked_in_metadata_is_current(self) -> None:
        self.assertIn("method_lines", self.fieldnames)
        self.assertTrue(METHOD_SIZES.metadata_is_current(self.rows, self.sizes))

    def test_writing_metadata_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            metadata_path = Path(directory) / "task_metadata.csv"
            METHOD_SIZES.write_metadata(
                metadata_path, self.fieldnames, self.rows, self.sizes
            )
            first = metadata_path.read_bytes()
            fields, rows = METHOD_SIZES.read_metadata(metadata_path)
            METHOD_SIZES.write_metadata(metadata_path, fields, rows, self.sizes)
            second = metadata_path.read_bytes()

        self.assertEqual(first, second)


if __name__ == "__main__":
    unittest.main()
