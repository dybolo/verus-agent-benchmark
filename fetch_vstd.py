#!/usr/bin/env python3.14

import shutil
import subprocess
import tempfile
from pathlib import Path

def fetch_latest_vstd():
    repo_url = "https://github.com/verus-lang/verus.git"
    target_dir = Path(".vstd")

    # 1. Remove existing .vstd folder if it exists
    if target_dir.exists():
        print(f"Removing existing {target_dir} directory...")
        shutil.rmtree(target_dir)

    print("Fetching the latest vstd library from verus-lang/verus...")

    # 2. Use a temporary directory for the sparse clone process
    with tempfile.TemporaryDirectory() as temp_dir:
        temp_path = Path(temp_dir)

        # 3. Perform a sparse clone (super fast, no history)
        subprocess.run(
            ["git", "clone", "--depth", "1", "--filter=blob:none", "--sparse", repo_url, temp_dir],
            check=True,
            capture_output=True
        )

        # 4. Check out only the source/vstd directory
        subprocess.run(
            ["git", "sparse-checkout", "set", "source/vstd"],
            cwd=temp_dir,
            check=True,
            capture_output=True
        )

        # 5. Move it to the root of your project as .vstd
        source_vstd_path = temp_path / "source" / "vstd"
        shutil.move(str(source_vstd_path), str(target_dir))

    print(f"Successfully fetched vstd to ./{target_dir}")

if __name__ == "__main__":
    fetch_latest_vstd()
