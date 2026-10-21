import io
import json
import os
import tempfile
import unittest
import urllib.error
import zipfile
from pathlib import Path
from unittest.mock import patch

import benchmark
import fetch_verus_release as releases


class VerusVersionTests(unittest.TestCase):
    def test_download_release_and_matching_toolchain(self):
        cases = [
            (version, endpoint, bundled)
            for version, endpoint in [(None, "latest"), ("release/test", "tags/release%2Ftest")]
            for bundled in [True, False]
        ]
        for version, endpoint, bundled in cases:
            with self.subTest(version=version, bundled=bundled), tempfile.TemporaryDirectory() as directory:
                release = {
                    "tag_name": version or "release/latest-test",
                    "assets": [{
                        "name": "verus-x86-linux.zip",
                        "browser_download_url": "https://example.com/verus.zip",
                    }],
                }

                def download(url, destination):
                    self.assertEqual(url, release["assets"][0]["browser_download_url"])
                    with zipfile.ZipFile(destination, "w") as archive:
                        archive.writestr("verus-release/verus", "binary")
                        if bundled:
                            archive.writestr("verus-release/vstd/vstd.rs", "// bundled vstd")

                def fetch_sources(version, target_dir):
                    target_dir.mkdir(parents=True)
                    (target_dir / "vstd.rs").write_text(f"// vstd from {version}")

                previous_cwd = os.getcwd()
                os.chdir(directory)
                try:
                    with (
                        patch.object(releases, "get_platform_info", return_value=("linux", "x86")),
                        patch.object(releases.urllib.request, "urlopen", return_value=io.BytesIO(json.dumps(release).encode())) as metadata,
                        patch.object(releases.urllib.request, "urlretrieve", side_effect=download),
                        patch.object(releases, "install_required_toolchain") as toolchain,
                        patch.object(releases, "fetch_vstd", side_effect=fetch_sources) as sources,
                    ):
                        releases.fetch_verus_release(version)
                        self.assertEqual(metadata.call_args.args[0].full_url,
                                         f"https://api.github.com/repos/verus-lang/verus/releases/{endpoint}")
                        self.assertEqual(Path(".verus/verus").read_text(), "binary")
                        self.assertTrue(os.access(".verus/verus", os.X_OK))
                        toolchain.assert_called_once_with(release)
                        if bundled:
                            sources.assert_not_called()
                            self.assertEqual(Path(".verus/vstd/vstd.rs").read_text(), "// bundled vstd")
                        else:
                            sources.assert_called_once_with(
                                version=release["tag_name"], target_dir=Path(".verus/vstd")
                            )
                            self.assertIn(release["tag_name"], Path(".verus/vstd/vstd.rs").read_text())
                finally:
                    os.chdir(previous_cwd)

    def test_unavailable_release_fails_before_download(self):
        with (
            patch.object(releases, "get_platform_info", return_value=("linux", "x86")),
            patch.object(releases.urllib.request, "urlopen", side_effect=urllib.error.HTTPError(
                "https://example.com", 404, "Not Found", {}, None)),
            patch.object(releases.urllib.request, "urlretrieve") as download,
        ):
            with self.assertRaisesRegex(RuntimeError, "Could not fetch Verus release missing"):
                releases.fetch_verus_release("missing")
            download.assert_not_called()

    def test_missing_platform_asset_fails_before_download(self):
        with (
            patch.object(releases, "get_platform_info", return_value=("linux", "x86")),
            patch.object(releases.urllib.request, "urlopen", return_value=io.BytesIO(b'{"assets": []}')),
            patch.object(releases.urllib.request, "urlretrieve") as download,
        ):
            with self.assertRaisesRegex(RuntimeError, "has no asset"):
                releases.fetch_verus_release("release/test")
            download.assert_not_called()

    def test_version_is_saved_and_old_runs_default_to_latest(self):
        run = benchmark.Run.create([], [], "tasks", verus_version="release/test")
        data = run.to_dict()
        self.assertEqual(benchmark.Run.from_dict(data, "run.json").verus_version, "release/test")
        del data["configuration"]["verus_version"]
        self.assertEqual(benchmark.Run.from_dict(data, "run.json").verus_version, "latest")

    def test_resume_uses_saved_version_and_rejects_a_different_version(self):
        run = benchmark.Run.create([], [], "tasks", verus_version="release/test")
        agent = benchmark.AgentSpec("demo/model", "demo", "demo", "model.model")
        run.agents = [agent]
        run.task_names = ["task.rs"]
        run.tasks_by_agent = {agent.name: {}}
        with (
            patch.object(benchmark, "resume_run", return_value=run),
            patch.object(benchmark, "build_base_image") as build,
            patch.object(benchmark, "build_agent_image"),
            patch("builtins.open", side_effect=RuntimeError("stop after build")),
        ):
            with self.assertRaisesRegex(RuntimeError, "stop after build"):
                benchmark.run_tasks(1, resume_id="test")
            build.assert_called_once_with("release/test")
            build.reset_mock()
            with self.assertRaisesRegex(ValueError, "does not match"):
                benchmark.run_tasks(1, resume_id="test", verus_version="release/other")
            build.assert_not_called()

    def test_build_passes_release_to_docker(self):
        with patch.object(benchmark.subprocess, "run") as docker:
            benchmark.build_base_image("release/test")
        command = docker.call_args.args[0]
        self.assertEqual(command[command.index("--build-arg") + 1], "VERUS_VERSION=release/test")

    def test_benchmark_cli_passes_version(self):
        with (
            patch("sys.argv", ["benchmark.py", "--verus-version", "release/test"]),
            patch.object(benchmark, "run_tasks") as run,
        ):
            benchmark.main()
        self.assertEqual(run.call_args.kwargs["verus_version"], "release/test")


if __name__ == "__main__":
    unittest.main()
