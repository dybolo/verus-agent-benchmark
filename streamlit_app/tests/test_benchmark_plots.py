from __future__ import annotations

import unittest
from pathlib import Path

import matplotlib

matplotlib.use("Agg")

from streamlit_app.data import (
    cohort_attempts,
    discover_cohorts,
    flatten_runs,
    load_runs,
    load_task_metadata,
)
from streamlit_app.paths import app_data_path
from streamlit_app.plots import (
    caterpillar,
    csv_bytes,
    exclusive_solves_matrix,
    figure_bytes,
    harness_comparisons,
    harness_model_interaction,
    harness_resource_usage,
    outcome_composition,
    quality_cost,
)

REPO_ROOT = Path(__file__).resolve().parents[2]
class PlotSmokeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        runs, _ = load_runs(REPO_ROOT / "runs")
        metadata, _ = load_task_metadata(
            app_data_path("task_metadata.csv"),
            [REPO_ROOT / "tasks", REPO_ROOT / "full_tasks"],
        )
        attempts = flatten_runs(runs, metadata)
        cls.selected = cohort_attempts(attempts, discover_cohorts(attempts)[0])
        cls.comparisons = harness_comparisons(cls.selected)

    def test_all_six_plots_render_and_export(self) -> None:
        results = [
            outcome_composition(self.selected, 10, 5),
            quality_cost(self.selected, 10, 5, "log"),
            caterpillar(self.selected, 12, 5),
            exclusive_solves_matrix(self.selected, 10, 5),
            harness_resource_usage(self.selected, 12, 5),
            harness_model_interaction(self.selected, 10, 5),
        ]
        for result in results:
            with self.subTest(columns=list(result.data.columns)):
                self.assertFalse(result.data.empty)
                self.assertTrue(figure_bytes(result.figure, "png").startswith(b"\x89PNG"))
                self.assertTrue(figure_bytes(result.figure, "pdf").startswith(b"%PDF"))
                self.assertIn(b"<svg", figure_bytes(result.figure, "svg")[:1000])
                self.assertIn(b"\n", csv_bytes(result.data))

    def test_outcome_bars_use_solid_fills(self) -> None:
        result = outcome_composition(self.selected, 10, 5)
        self.assertTrue(result.figure.axes[0].patches)
        self.assertTrue(all(not patch.get_hatch() for patch in result.figure.axes[0].patches))

    def test_caterpillar_contains_expected_current_taxonomy(self) -> None:
        result = caterpillar(self.selected, 12, 5)
        counts = result.data.groupby("proof_style")["task_id"].nunique().to_dict()
        self.assertEqual(
            counts,
            {"atomic-operation": 20, "tokenized_state_machine!": 30},
        )

    def test_caterpillar_uses_source_file_group_headers(self) -> None:
        result = caterpillar(self.selected, 12, 5)
        labels = [label for axis in result.figure.axes for label in axis.get_yticklabels()]
        source_headers = [label for label in labels if label.get_text().endswith(".rs")]

        self.assertTrue(source_headers)
        self.assertTrue(all(label.get_fontweight() == "bold" for label in source_headers))
        self.assertTrue(any(label.get_text().startswith("    ") for label in labels))

    def test_current_harness_comparison_is_qwen_pair(self) -> None:
        self.assertEqual(self.comparisons["comparison"].nunique(), 1)
        self.assertEqual(len(self.comparisons), 50)
        self.assertEqual(set(self.comparisons["harness_a"]), {"opencode"})
        self.assertEqual(set(self.comparisons["harness_b"]), {"pi"})

    def test_exclusive_solves_are_identified_within_model(self) -> None:
        result = exclusive_solves_matrix(self.selected, 10, 5)
        exclusive = result.data[result.data["status"] == "Exclusive solve"]
        self.assertFalse(exclusive.empty)
        self.assertTrue((exclusive["harness"] == exclusive["exclusive_solver"]).all())
        self.assertTrue((exclusive["solver_count"] == 1).all())

    def test_resource_usage_exports_all_three_metrics(self) -> None:
        result = harness_resource_usage(self.selected, 12, 5)
        self.assertEqual(
            set(result.data["metric"]),
            {"duration_seconds", "total_turns", "total_tool_calls"},
        )
        self.assertTrue({"total", "median", "q1", "q3"}.issubset(result.data.columns))

    def test_resource_usage_counts_timeouts_as_twenty_minutes(self) -> None:
        attempts = self.selected.copy()
        condition = attempts["condition"].iloc[0]
        condition_rows = attempts["condition"] == condition
        attempts.loc[condition_rows, "timed_out"] = True
        attempts.loc[condition_rows, "duration_seconds"] = 1

        result = harness_resource_usage(attempts, 12, 5)
        duration = result.data[
            (result.data["condition"] == condition)
            & (result.data["metric"] == "duration_seconds")
        ].iloc[0]

        self.assertEqual(duration["median"], 20)
        self.assertEqual(duration["q1"], 20)
        self.assertEqual(duration["q3"], 20)

    def test_interaction_warns_for_incomplete_factorial(self) -> None:
        result = harness_model_interaction(self.selected, 10, 5)
        self.assertIsNotNone(result.warning)


if __name__ == "__main__":
    unittest.main()
