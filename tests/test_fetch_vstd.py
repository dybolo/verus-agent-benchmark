import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import fetch_verus_release as releases
import fetch_vstd


class FetchVstdTests(unittest.TestCase):
    def test_fetches_selected_tag_into_destination(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory) / "verus" / "vstd"
            destination.mkdir(parents=True)
            (destination / "stale.rs").write_text("stale")

            def git(command, **kwargs):
                if command[:2] == ["git", "sparse-checkout"]:
                    source = Path(kwargs["cwd"]) / "source" / "vstd"
                    source.mkdir(parents=True)
                    (source / "lib.rs").write_text("// matching source")
                    (source / "nested").mkdir()
                    (source / "nested" / "proof.rs").write_text("// proof")

            with patch.object(fetch_vstd.subprocess, "run", side_effect=git) as run:
                fetch_vstd.fetch_vstd("release/test", destination)

            clone = run.call_args_list[0].args[0]
            self.assertEqual(clone[clone.index("--branch") + 1], "release/test")
            self.assertIn("--single-branch", clone)
            self.assertEqual((destination / "lib.rs").read_text(), "// matching source")
            self.assertTrue((destination / "nested" / "proof.rs").is_file())
            self.assertFalse((destination / "stale.rs").exists())

    def test_git_failure_preserves_existing_destination(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory) / "vstd"
            destination.mkdir()
            (destination / "lib.rs").write_text("original")
            failure = subprocess.CalledProcessError(128, ["git"], stderr="tag not found")
            with patch.object(fetch_vstd.subprocess, "run", side_effect=failure):
                with self.assertRaisesRegex(RuntimeError, "release/missing: tag not found"):
                    fetch_vstd.fetch_vstd("release/missing", destination)
            self.assertEqual((destination / "lib.rs").read_text(), "original")

    def test_missing_sources_fail_without_creating_destination(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory) / "vstd"
            with patch.object(fetch_vstd.subprocess, "run"):
                with self.assertRaisesRegex(RuntimeError, "Missing source/vstd/lib.rs"):
                    fetch_vstd.fetch_vstd("release/test", destination)
            self.assertFalse(destination.exists())

    def test_missing_release_tag_does_not_fetch_default_branch(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(releases, "fetch_vstd") as fetch:
                with self.assertRaisesRegex(RuntimeError, "no tag_name"):
                    releases.ensure_vstd_sources({}, directory)
                fetch.assert_not_called()

    def test_fetch_failure_propagates(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(releases, "fetch_vstd", side_effect=RuntimeError("fetch failed")):
                with self.assertRaisesRegex(RuntimeError, "fetch failed"):
                    releases.ensure_vstd_sources({"tag_name": "release/test"}, directory)

    def test_empty_fetch_result_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(releases, "fetch_vstd"):
                with self.assertRaisesRegex(RuntimeError, "Missing vstd/lib.rs after fetching"):
                    releases.ensure_vstd_sources({"tag_name": "release/test"}, directory)


if __name__ == "__main__":
    unittest.main()
