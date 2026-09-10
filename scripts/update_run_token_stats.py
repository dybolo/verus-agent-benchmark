#!/usr/bin/env python3
"""Backfill input/output token totals in selected benchmark run files."""

from __future__ import annotations

import argparse
import dataclasses
import importlib.util
import json
import os
import stat
import sys
import tempfile
from pathlib import Path
from types import ModuleType
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[1]
RUNS_DIR = ROOT / "runs"
SESSIONS_DIR = ROOT / "sessions"
TOKEN_FIELDS = ("total_input_tokens", "total_output_tokens")

sys.path.insert(0, str(ROOT))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Recompute token totals for one or more files in runs/."
    )
    parser.add_argument(
        "runs",
        nargs="+",
        metavar="RUN",
        help="run ID, JSON filename, or path to a JSON file directly under runs/",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="show the changes without writing any run files",
    )
    return parser.parse_args()


def resolve_run_file(value: str) -> Path:
    candidate = Path(value)
    if not candidate.is_absolute():
        candidate = (
            RUNS_DIR / candidate
            if len(candidate.parts) == 1
            else Path.cwd() / candidate
        )
    if candidate.suffix != ".json":
        candidate = candidate.with_suffix(".json")
    candidate = candidate.resolve()
    if candidate.parent != RUNS_DIR.resolve():
        raise ValueError(f"run file must be directly under {RUNS_DIR}: {value}")
    if not candidate.is_file():
        raise FileNotFoundError(f"run file not found: {candidate}")
    return candidate


def load_statistics_function(
    agent_dir: str, modules: dict[str, ModuleType]
) -> Callable[[str], Any]:
    if agent_dir not in modules:
        script = ROOT / "agents" / agent_dir / "statistics.py"
        if not script.is_file():
            raise FileNotFoundError(f"statistics module not found: {script}")
        spec = importlib.util.spec_from_file_location(
            f"agents_{agent_dir}_statistics", script
        )
        if spec is None or spec.loader is None:
            raise ImportError(f"could not load statistics module: {script}")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        modules[agent_dir] = module
    return modules[agent_dir].compute_statistics


def resolve_session_dir(session_file: str) -> Path:
    path = Path(session_file)
    if not path.is_absolute():
        path = ROOT / path
    path = path.resolve()
    if not path.is_file():
        raise FileNotFoundError(f"session file not found: {path}")
    if SESSIONS_DIR.resolve() not in path.parents:
        raise ValueError(f"session file is outside {SESSIONS_DIR}: {path}")
    return path.parent


def write_json_atomically(path: Path, data: dict[str, Any]) -> None:
    descriptor, temporary_name = tempfile.mkstemp(
        dir=path.parent, prefix=f".{path.name}.", suffix=".tmp"
    )
    try:
        os.fchmod(descriptor, stat.S_IMODE(path.stat().st_mode))
        with os.fdopen(descriptor, "w", encoding="utf-8") as output:
            json.dump(data, output, indent=2)
            output.write("\n")
        os.replace(temporary_name, path)
    except BaseException:
        try:
            os.unlink(temporary_name)
        except FileNotFoundError:
            pass
        raise


def update_run(path: Path, dry_run: bool, modules: dict[str, ModuleType]) -> None:
    with path.open(encoding="utf-8") as run_file:
        data = json.load(run_file)

    configurations = {
        agent["name"]: agent["agent_dir"]
        for agent in data.get("configuration", {}).get("agents", [])
    }
    changes = 0
    skipped = 0

    for agent_name, agent_data in data.get("agents", {}).items():
        agent_dir = configurations.get(agent_name, agent_name.split("/", 1)[0])
        compute_statistics = load_statistics_function(agent_dir, modules)
        for task_name, task_data in agent_data.get("tasks", {}).items():
            session_file = task_data.get("session_file")
            if not session_file:
                print(f"  skip {agent_name}/{task_name}: no session_file")
                skipped += 1
                continue

            try:
                session_dir = resolve_session_dir(session_file)
                stats = dataclasses.asdict(compute_statistics(str(session_dir)))
            except Exception as error:
                raise RuntimeError(
                    f"could not update {agent_name}/{task_name}: {error}"
                ) from error
            updates = {field: stats[field] for field in TOKEN_FIELDS}
            if all(task_data.get(field) == value for field, value in updates.items()):
                continue
            task_data.update(updates)
            changes += 1
            print(
                f"  {agent_name}/{task_name}: "
                f"input={updates['total_input_tokens']}, "
                f"output={updates['total_output_tokens']}"
            )

    action = "would update" if dry_run else "updated"
    if changes and not dry_run:
        write_json_atomically(path, data)
    print(f"{path.name}: {action} {changes} task(s); skipped {skipped}")


def main() -> int:
    args = parse_args()
    modules: dict[str, ModuleType] = {}
    try:
        paths = [resolve_run_file(value) for value in args.runs]
        for path in paths:
            update_run(path, args.dry_run, modules)
    except Exception as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
