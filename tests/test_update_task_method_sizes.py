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
        self.assertTrue(all(size.missing_code_lines > 0 for size in self.sizes))

    def test_diff_counts_only_unmatched_target_source_lines(self) -> None:
        source = ["same", "removed", "old version", "", "tail", "unrelated"]
        task = ["same", "new version", "tail", "task-only addition"]
        target = METHOD_SIZES.Target("example", 1, 5)

        self.assertEqual(
            METHOD_SIZES.count_missing_code_lines(source, task, (target,)), 1
        )

    def test_composite_and_duplicate_name_tasks_use_hard_coded_ranges(self) -> None:
        by_task = {size.task_id: size for size in self.sizes}

        self.assertEqual(by_task["wait"].method_lines, 84)
        self.assertEqual(by_task["wait"].targets, ("wake_one", "wake_all", "enqueue"))
        self.assertEqual(by_task["cuckoo_inductive"].method_lines, 76)
        self.assertEqual(by_task["helping_full"].method_lines, 171)
        self.assertEqual(by_task["helping_full"].atomic_operations, 10)
        self.assertEqual(by_task["linked_list_take"].method_lines, 37)
        self.assertEqual(by_task["linked_list_take_"].method_lines, 52)

    def test_missing_lines_are_scoped_to_task_targets(self) -> None:
        by_task = {size.task_id: size for size in self.sizes}

        self.assertEqual(by_task["rwlock_readguard_drop"].missing_code_lines, 7)
        self.assertEqual(by_task["rwlock_writeguard_drop"].missing_code_lines, 19)
        self.assertEqual(by_task["rwlock_upgradableguard_drop"].missing_code_lines, 11)
        self.assertEqual(by_task["fifo_dequeue"].missing_code_lines, 8)
        self.assertEqual(by_task["cuckoo_delete"].missing_code_lines, 19)
        self.assertEqual(by_task["wait"].missing_code_lines, 11)
        self.assertEqual(by_task["free_free_block_mt"].missing_code_lines, 55)
        self.assertEqual(by_task["context_full"].missing_code_lines, 21)

    def test_uses_the_directory_selected_by_proof_style(self) -> None:
        rows = {row["task_id"]: row for row in self.rows}

        self.assertEqual(
            METHOD_SIZES.task_path_for(rows["cuckoo_delete"], ROOT).parent,
            ROOT / "tasks",
        )
        self.assertEqual(
            METHOD_SIZES.task_path_for(rows["context_full"], ROOT).parent,
            ROOT / "full_tasks",
        )

    def test_every_atomic_operation_task_has_an_atomic_operation(self) -> None:
        proof_styles = {row["task_id"]: row["proof_style"] for row in self.rows}

        self.assertTrue(
            all(
                size.atomic_operations > 0
                for size in self.sizes
                if proof_styles[size.task_id] == "atomic-operation"
            )
        )

    def test_checked_in_metadata_is_current(self) -> None:
        self.assertIn("method_lines", self.fieldnames)
        self.assertIn("atomic_operations", self.fieldnames)
        self.assertIn("missing_code_lines", self.fieldnames)
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
