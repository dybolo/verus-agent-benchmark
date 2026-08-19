"""Resolve packaged data files and the benchmark repository location."""

from __future__ import annotations

from pathlib import Path


def app_data_path(name: str) -> Path:
    """Return the installed path for a resource bundled with this package."""
    return Path(__file__).with_name(name)


def repository_root() -> Path:
    """Locate the benchmark repository for editable and installed package use."""
    candidates = (Path.cwd().resolve(), *Path(__file__).resolve().parents)
    for candidate in candidates:
        if (candidate / "runs").is_dir() and (candidate / "tasks").is_dir():
            return candidate
    return Path.cwd().resolve()
