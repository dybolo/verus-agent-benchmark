# pyright: basic

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import benchmark


class CheckpointTests(unittest.TestCase):
    def test_run_file_write_replaces_old_contents(self):
        with tempfile.TemporaryDirectory() as directory:
            run_file = os.path.join(directory, "run.json")
            agent = benchmark.AgentSpec("demo/model", "demo", "demo", "model.model")
            run = benchmark.Run.create([agent], ["task.rs"])
            run.stats_file = run_file
            run.save()
            run.tasks_by_agent[agent.name]["task.rs"].status = "completed"
            run.save()
            with open(run_file) as f:
                self.assertEqual(
                    json.load(f)["agents"][agent.name]["tasks"]["task.rs"]["status"],
                    "completed",
                )

    def test_only_nonfinal_tasks_are_selected_for_resume(self):
        self.assertFalse(benchmark.Task("done.rs", status="completed").is_pending)
        self.assertFalse(
            benchmark.Task("slow.rs", status="completed", timed_out=True).is_pending
        )
        self.assertTrue(benchmark.Task("lost.rs").is_pending)

    def test_rate_limited_run_resumes_without_a_real_subprocess(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tasks").mkdir()
            (root / "tasks" / "example.rs").write_text("// task\n")
            (root / "agents" / "demo").mkdir(parents=True)
            (root / "agents" / "demo" / "Dockerfile").write_text("FROM scratch\n")
            model = root / "agents" / "demo" / "demo.model"
            model.write_text("#!/bin/sh\n")
            model.chmod(0o755)
            (root / "prompt.txt").write_text("solve {task} and write {output}")

            calls = []
            limited = subprocess.CompletedProcess(
                ["docker"], 1, "", "429: usage limit exceeded"
            )
            successful = subprocess.CompletedProcess(["docker"], 0, "", "")

            def fake_run(command, **kwargs):
                calls.append(command)
                # Only the agent container needs to emulate a provider response.
                if command[:2] == ["docker", "run"]:
                    return (
                        limited
                        if len([c for c in calls if c[:2] == ["docker", "run"]]) == 1
                        else successful
                    )
                return successful

            original_cwd = os.getcwd()
            os.chdir(root)
            try:
                with patch.object(benchmark.subprocess, "run", side_effect=fake_run):
                    benchmark.run_tasks(max_workers=1)
                    runs_directory = root / "runs"
                    run_file = next(runs_directory.glob("*.json"))
                    first_run = json.loads(run_file.read_text())
                    self.assertNotIn("run_status", first_run)
                    self.assertEqual(
                        first_run["agents"]["demo/demo"]["tasks"]["example.rs"][
                            "status"
                        ],
                        "pending",
                    )

                    benchmark.run_tasks(max_workers=1, resume_id=run_file.stem)
                    resumed_run = json.loads(run_file.read_text())
                    self.assertNotIn("run_status", resumed_run)
                    self.assertEqual(
                        resumed_run["agents"]["demo/demo"]["tasks"]["example.rs"][
                            "status"
                        ],
                        "completed",
                    )
            finally:
                os.chdir(original_cwd)

            self.assertTrue(calls)
            self.assertTrue(
                all(
                    isinstance(command, list)
                    and command[0] == "docker"
                    or command[0] == "git"
                    for command in calls
                )
            )


if __name__ == "__main__":
    unittest.main()
