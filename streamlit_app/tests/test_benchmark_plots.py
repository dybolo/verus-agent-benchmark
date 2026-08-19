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
    agreement_matrix,
    caterpillar,
    csv_bytes,
    disagreement_matrix,
    figure_bytes,
    harness_comparisons,
    harness_model_interaction,
    outcome_composition,
    quality_cost,
)

REPO_ROOT = Path(__file__).resolve().parents[2]
class PlotSmokeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        runs, _ = load_runs(REPO_ROOT / "runs")
        metadata, _ = load_task_metadata(app_data_path("task_metadata.csv"), REPO_ROOT / "tasks")
        attempts = flatten_runs(runs, metadata)
        cls.selected = cohort_attempts(attempts, discover_cohorts(attempts)[0])
        cls.comparisons = harness_comparisons(cls.selected)

    def test_all_six_plots_render_and_export(self) -> None:
        results = [
            outcome_composition(self.selected, 10, 5),
            quality_cost(self.selected, 10, 5, "log"),
            caterpillar(self.selected, 12, 5),
            disagreement_matrix(self.comparisons, 10, 5),
            agreement_matrix(self.comparisons, 10, 5),
            harness_model_interaction(self.selected, 10, 5),
        ]
        for result in results:
            with self.subTest(columns=list(result.data.columns)):
                self.assertFalse(result.data.empty)
                self.assertTrue(figure_bytes(result.figure, "png").startswith(b"\x89PNG"))
                self.assertTrue(figure_bytes(result.figure, "pdf").startswith(b"%PDF"))
                self.assertIn(b"<svg", figure_bytes(result.figure, "svg")[:1000])
                self.assertIn(b"\n", csv_bytes(result.data))

    def test_caterpillar_contains_expected_current_taxonomy(self) -> None:
        result = caterpillar(self.selected, 12, 5)
        counts = result.data.groupby("proof_style")["task_id"].nunique().to_dict()
        self.assertEqual(
            counts,
            {"atomic-operation": 20, "tokenized_state_machine!": 30},
        )

    def test_current_harness_comparison_is_qwen_pair(self) -> None:
        self.assertEqual(self.comparisons["comparison"].nunique(), 1)
        self.assertEqual(len(self.comparisons), 50)
        self.assertEqual(set(self.comparisons["harness_a"]), {"opencode"})
        self.assertEqual(set(self.comparisons["harness_b"]), {"pi"})

    def test_interaction_warns_for_incomplete_factorial(self) -> None:
        result = harness_model_interaction(self.selected, 10, 5)
        self.assertIsNotNone(result.warning)


if __name__ == "__main__":
    unittest.main()
