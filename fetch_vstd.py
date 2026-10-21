#!/usr/bin/env python3.14

import argparse
import shutil
import subprocess
import tempfile
from pathlib import Path

def fetch_latest_vstd():
    """Fetch vstd from the default branch into .vstd."""
    fetch_vstd()


def fetch_vstd(version=None, target_dir=".vstd"):
    """Fetch vstd sources from a Git tag, or the default branch if omitted."""
    repo_url = "https://github.com/verus-lang/verus.git"
    target_dir = Path(target_dir)

    print(f"Fetching vstd sources from {version or 'the default branch'}...")

    with tempfile.TemporaryDirectory() as temp_dir:
        temp_path = Path(temp_dir)

        clone_cmd = ["git", "clone", "--depth", "1", "--filter=blob:none", "--sparse"]
        if version:
            clone_cmd.extend(["--branch", version, "--single-branch"])
        clone_cmd.extend([repo_url, temp_dir])

        try:
            subprocess.run(clone_cmd, check=True, capture_output=True, text=True)
            subprocess.run(
                ["git", "sparse-checkout", "set", "source/vstd"],
                cwd=temp_dir,
                check=True,
                capture_output=True,
                text=True,
            )
        except (OSError, subprocess.CalledProcessError) as e:
            detail = e.stderr if isinstance(e, subprocess.CalledProcessError) else str(e)
            raise RuntimeError(
                f"Could not fetch vstd sources from {version or 'the default branch'}: {detail}"
            ) from e

        source_vstd_path = temp_path / "source" / "vstd"
        if not (source_vstd_path / "lib.rs").is_file():
            raise RuntimeError(
                f"Missing source/vstd/lib.rs in {version or 'the default branch'}"
            )

        # Replace the destination only after fetching and validating the sources.
        target_dir.parent.mkdir(parents=True, exist_ok=True)
        if target_dir.exists():
            shutil.rmtree(target_dir)
        shutil.move(str(source_vstd_path), str(target_dir))

    print(f"Successfully fetched vstd to {target_dir}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Download Verus vstd sources")
    parser.add_argument("--version", help="Exact Git tag (default: repository default branch)")
    parser.add_argument("--target-dir", default=".vstd", help="Destination (default: .vstd)")
    args = parser.parse_args()
    try:
        fetch_vstd(args.version, args.target_dir)
    except RuntimeError as e:
        parser.exit(1, f"Error: {e}\n")
