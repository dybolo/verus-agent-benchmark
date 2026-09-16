from __future__ import annotations

import unittest
from pathlib import Path

import matplotlib
import numpy as np

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
    task_normalized_harness_effect,
    token_usage_by_outcome,
    tool_calls_by_type,
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
        cls.attempts = attempts
        qwen_cohort = next(
            cohort
            for cohort in discover_cohorts(attempts)
            if {
                "opencode / bedrock-qwen3-coder-480b-a35b",
                "pi / bedrock-qwen3-coder-480b-a35b",
            }.issubset(cohort.conditions)
            and len(cohort.task_ids) == 50
        )
        cls.selected = cohort_attempts(attempts, qwen_cohort)
        cls.comparisons = harness_comparisons(cls.selected)

    def test_all_plots_render_and_export(self) -> None:
        results = [
            outcome_composition(self.selected, 10, 5),
            quality_cost(self.selected, 10, 5, "log"),
            caterpillar(self.selected, 12, 5),
            exclusive_solves_matrix(self.selected, 10, 5),
            harness_resource_usage(self.selected, 12, 5),
            harness_model_interaction(self.selected, 10, 5),
            task_normalized_harness_effect(self.selected, 10, 5),
            tool_calls_by_type(self.selected, 10, 5),
            token_usage_by_outcome(self.selected, 10, 5),
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

    def test_quality_cost_axis_marks_each_agent_cost(self) -> None:
        for scale in ("log", "linear"):
            with self.subTest(scale=scale):
                result = quality_cost(self.selected, 10, 5, scale)
                expected = result.data.dropna(subset=["mean_cost_per_attempt_usd"])
                if scale == "log":
                    expected = expected[expected["mean_cost_per_attempt_usd"] > 0]
                costs = np.sort(expected["mean_cost_per_attempt_usd"].unique())

                np.testing.assert_allclose(result.figure.axes[0].get_xticks(), costs)
                self.assertEqual(
                    [label.get_text() for label in result.figure.axes[0].get_xticklabels()],
                    [f"${cost:,.4f}".rstrip("0").rstrip(".") for cost in costs],
                )
                if scale == "log":
                    self.assertTrue(
                        all(not label.get_text() for label in result.figure.axes[0].xaxis.get_minorticklabels())
                    )

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

    def test_task_normalized_effect_compares_all_metrics_with_pi(self) -> None:
        cohort = next(
            cohort
            for cohort in discover_cohorts(self.attempts)
            if {
                "codex / gpt-5.6-luna",
                "copilot / gpt-5.6-luna",
                "opencode / gpt-5.6-luna",
                "pi / gpt-5.6-luna",
            }.issubset(cohort.conditions)
        )
        selected = cohort_attempts(self.attempts, cohort)
        result = task_normalized_harness_effect(selected, 10, 5)
        self.assertEqual(
            set(result.data["metric"]),
            {
                "total_input_tokens",
                "total_output_tokens",
                "total_tool_calls",
                "strict_success",
            },
        )
        self.assertEqual(set(result.data["reference_harness"]), {"pi"})
        self.assertEqual(len(result.figure.axes), 4)
        self.assertTrue(all(axis.get_xscale() == "log" for axis in result.figure.axes[:3]))
        self.assertEqual(result.figure.axes[3].get_xscale(), "linear")

        row = result.data[result.data["metric"] == "total_input_tokens"].iloc[0]
        harness_values = selected[
            (selected["model"] == row["model"]) & (selected["harness"] == row["harness"])
        ][["task_id", "total_input_tokens"]]
        pi_values = selected[
            (selected["model"] == row["model"]) & (selected["harness"] == "pi")
        ][["task_id", "total_input_tokens"]]
        paired = harness_values.merge(pi_values, on="task_id", suffixes=("_harness", "_pi"))
        expected = np.median(paired["total_input_tokens_harness"] / paired["total_input_tokens_pi"])
        self.assertAlmostEqual(row["estimate"], expected)
        self.assertLessEqual(row["ci_low"], row["estimate"])
        self.assertGreaterEqual(row["ci_high"], row["estimate"])

        repairs = result.data[result.data["metric"] == "strict_success"].iloc[0]
        harness_repairs = selected[
            (selected["model"] == repairs["model"]) & (selected["harness"] == repairs["harness"])
        ][["task_id", "strict_success"]]
        pi_repairs = selected[
            (selected["model"] == repairs["model"]) & (selected["harness"] == "pi")
        ][["task_id", "strict_success"]]
        paired_repairs = harness_repairs.merge(pi_repairs, on="task_id", suffixes=("_harness", "_pi"))
        expected_repairs = (
            paired_repairs["strict_success_harness"].astype(float)
            - paired_repairs["strict_success_pi"].astype(float)
        ).mean() * 100
        self.assertAlmostEqual(repairs["estimate"], expected_repairs)
        self.assertEqual(repairs["unit"], "percentage points")

    def test_task_normalized_effect_warns_when_tasks_are_unpaired(self) -> None:
        attempts = self.selected.copy()
        comparison = task_normalized_harness_effect(attempts, 10, 5).data.iloc[0]
        condition_rows = (attempts["model"] == comparison["model"]) & (
            attempts["harness"] == comparison["harness"]
        )
        task = attempts.loc[condition_rows, "task_id"].iloc[0]
        attempts = attempts[~(condition_rows & (attempts["task_id"] == task))]

        result = task_normalized_harness_effect(attempts, 10, 5)

        self.assertIsNotNone(result.warning)
        self.assertTrue((result.data["excluded_tasks"] >= 1).all())

    def test_resource_usage_exports_all_metrics(self) -> None:
        result = harness_resource_usage(self.selected, 12, 5)
        self.assertEqual(
            set(result.data["metric"]),
            {
                "duration_seconds",
                "total_input_tokens",
                "total_output_tokens",
                "total_tool_calls",
            },
        )
        self.assertTrue({"total", "median", "q1", "q3"}.issubset(result.data.columns))

    def test_token_usage_is_split_by_successful_outcome(self) -> None:
        result = token_usage_by_outcome(self.selected, 10, 5)

        self.assertEqual(
            set(result.data["metric"]),
            {"total_input_tokens", "total_output_tokens"},
        )
        self.assertEqual(set(result.data["successful"]), {True, False})
        self.assertEqual(len(result.figure.axes), 2)
        expected_attempts = (
            self.selected.groupby(["condition", "strict_success"], observed=True)
            .size()
            .to_dict()
        )
        for row in result.data.itertuples():
            self.assertEqual(row.attempts, expected_attempts.get((row.condition, row.successful), 0))

    def test_tool_calls_by_type_are_reported_per_attempted_task(self) -> None:
        result = tool_calls_by_type(self.selected, 10, 5)

        self.assertEqual(
            set(result.data["reported_tool_call_category"]),
            {"read", "shell", "patch", "other"},
        )
        self.assertEqual(result.figure.axes[0].get_ylabel(), "Reported tool-call category")
        self.assertEqual(
            [label.get_text() for label in result.figure.axes[0].get_yticklabels()],
            ["read", "shell", "patch", "other"],
        )
        expected_y = np.arange(4)
        for agent_dots in result.figure.axes[0].collections[1:]:
            np.testing.assert_array_equal(agent_dots.get_offsets()[:, 1], expected_y)
        for row in result.data.itertuples():
            expected = row.total_reported_calls / row.attempted_tasks
            self.assertAlmostEqual(row.calls_per_attempted_task, expected)

    def test_resource_usage_counts_timeouts_as_twenty_minutes(self) -> None:
        attempts = self.selected.copy()
        condition = attempts["condition"].iloc[0]
        condition_rows = attempts["condition"] == condition
        attempts.loc[condition_rows, "timed_out"] = True
        attempts.loc[condition_rows, "duration_seconds"] = 1

        result = harness_resource_usage(attempts, 12, 5)
        duration = result.data[
            (result.data["condition"] == condition) & (result.data["metric"] == "duration_seconds")
        ].iloc[0]

        self.assertEqual(duration["median"], 20)
        self.assertEqual(duration["q1"], 20)
        self.assertEqual(duration["q3"], 20)

    def test_interaction_warns_for_incomplete_factorial(self) -> None:
        result = harness_model_interaction(self.selected, 10, 5)
        self.assertIsNotNone(result.warning)


if __name__ == "__main__":
    unittest.main()
