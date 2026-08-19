from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

import pandas as pd

from streamlit_app.data import (
    cohort_attempts,
    discover_cohorts,
    flatten_runs,
    load_runs,
    load_task_metadata,
)
from streamlit_app.paths import app_data_path, repository_root

REPO_ROOT = Path(__file__).resolve().parents[2]


class LoadingTests(unittest.TestCase):
    def test_flatten_runs_derives_outcomes(self) -> None:
        runs = [
            {
                "timestamp": "test",
                "agents": {
                    "agent/model": {
                        "tasks": {
                            "valid.rs": {
                                "verus_passed": True,
                                "cheat_checker_passed": True,
                                "timed_out": True,
                            },
                            "timed-out.rs": {"timed_out": True},
                            "rejected.rs": {"verus_passed": True},
                            "failed.rs": {},
                        }
                    }
                },
            }
        ]
        metadata = pd.DataFrame(columns=["task_id", "proof_style", "source_module"])

        attempts = flatten_runs(runs, metadata)

        self.assertEqual(
            attempts.set_index("task_id")["outcome"].to_dict(),
            {
                "valid": "Valid repair",
                "timed-out": "Timed out without a valid repair",
                "rejected": "Verus passed, Lynette rejected",
                "failed": "Verification failed",
            },
        )
        self.assertTrue(attempts.set_index("task_id").loc["valid", "strict_success"])

    def test_load_runs_reports_malformed_files(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            runs_dir = Path(directory)
            (runs_dir / "valid.json").write_text(
                json.dumps({"timestamp": "valid", "agents": {}})
            )
            (runs_dir / "bad.json").write_text("not json")
            (runs_dir / "wrong.json").write_text(json.dumps({"timestamp": "wrong"}))
            runs, errors = load_runs(runs_dir)
        self.assertEqual([run["timestamp"] for run in runs], ["valid"])
        self.assertEqual(len(errors), 2)

    def test_sidecar_covers_all_manifest_tasks(self) -> None:
        metadata, errors = load_task_metadata(
            app_data_path("task_metadata.csv"), REPO_ROOT / "tasks"
        )
        self.assertEqual(errors, [])
        self.assertEqual(len(metadata), 75)
        self.assertEqual(metadata["task_id"].nunique(), 75)
        self.assertEqual(
            metadata["proof_style"].value_counts().to_dict(),
            {"atomic-operation": 42, "tokenized_state_machine!": 33},
        )

    def test_default_real_cohort_is_four_conditions_on_fifty_tasks(self) -> None:
        runs, run_errors = load_runs(REPO_ROOT / "runs")
        metadata, metadata_errors = load_task_metadata(
            app_data_path("task_metadata.csv"), REPO_ROOT / "tasks"
        )
        self.assertEqual(run_errors, [])
        self.assertEqual(metadata_errors, [])
        attempts = flatten_runs(runs, metadata)
        cohorts = discover_cohorts(attempts)
        self.assertTrue(cohorts)
        default = cohorts[0]
        self.assertEqual(len(default.task_ids), 50)
        self.assertEqual(len(default.conditions), 4)
        selected = cohort_attempts(attempts, default)
        self.assertEqual(len(selected), 200)
        styles = selected.drop_duplicates("task_id")["proof_style"].value_counts().to_dict()
        self.assertEqual(
            styles,
            {"tokenized_state_machine!": 30, "atomic-operation": 20},
        )

    def test_package_resolves_the_repository_and_bundled_metadata(self) -> None:
        self.assertEqual(repository_root(), REPO_ROOT)
        self.assertTrue(app_data_path("task_metadata.csv").is_file())


if __name__ == "__main__":
    unittest.main()
