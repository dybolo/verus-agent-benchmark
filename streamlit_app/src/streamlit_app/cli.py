"""Launch the Streamlit dashboard scripts through installed console commands."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path


def _run(application: str) -> int:
    """Start one dashboard script with the current Streamlit arguments."""
    app_path = Path(__file__).with_name(application)
    return subprocess.run(
        [sys.executable, "-m", "streamlit", "run", str(app_path), *sys.argv[1:]],
        check=False,
    ).returncode


def runs_viewer() -> None:
    """Launch the benchmark run viewer."""
    raise SystemExit(_run("runs_viewer.py"))


def plots_viewer() -> None:
    """Launch the evaluation plot dashboard."""
    raise SystemExit(_run("plots_viewer.py"))
