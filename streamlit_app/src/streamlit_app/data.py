"""Load benchmark artifacts and shape them into tables used by the dashboards."""

from __future__ import annotations

import csv
import hashlib
import json
import math
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pandas as pd


@dataclass(frozen=True)
class Cohort:
    """A set of matching task attempts, one per harness/model condition."""
    signature: str
    task_ids: tuple[str, ...]
    entry_ids: tuple[str, ...]
    conditions: tuple[str, ...]
    latest_timestamp: str

    @property
    def label(self) -> str:
        """Return the human-readable label used by the cohort selector."""
        return (
            f"{len(self.task_ids)} tasks · {len(self.conditions)} conditions · "
            f"latest {self.latest_timestamp} · {self.signature}"
        )


def load_runs(runs_dir: Path) -> tuple[list[dict[str, Any]], list[str]]:
    """Load benchmark JSON files without modifying their contents on disk."""
    runs: list[dict[str, Any]] = []
    errors: list[str] = []
    for run_path in sorted(runs_dir.glob("*.json"), reverse=True):
        try:
            data = json.loads(run_path.read_text())
            if not isinstance(data, dict) or not isinstance(data.get("agents"), dict):
                raise TypeError("expected an object containing an 'agents' object")
            data["_path"] = run_path
            data.setdefault("timestamp", run_path.stem)
            runs.append(data)
        except (OSError, json.JSONDecodeError, TypeError, ValueError) as error:
            errors.append(f"{run_path.name}: {error}")
    return runs, errors


def all_task_results(run: dict[str, Any]) -> list[tuple[str, str, dict[str, Any]]]:
    """Return every ``(agent, task, result)`` record contained in one run."""
    rows: list[tuple[str, str, dict[str, Any]]] = []
    for agent_name, agent_data in run.get("agents", {}).items():
        tasks = agent_data.get("tasks", {}) if isinstance(agent_data, dict) else {}
        for task_name, result in tasks.items():
            if isinstance(result, dict):
                rows.append((agent_name, task_name, result))
    return rows


def numeric_total(rows: Iterable[tuple[str, str, dict[str, Any]]], key: str) -> float:
    """Sum numeric values for ``key`` across task result rows."""
    total = 0.0
    for _, _, result in rows:
        value = result.get(key, 0)
        if isinstance(value, (int, float)) and not isinstance(value, bool):
            total += value
    return total


def split_agent_name(agent_name: str) -> tuple[str, str]:
    """Split a ``harness/model`` name, handling names without a model."""
    harness, separator, model = agent_name.partition("/")
    if not separator:
        return agent_name, "unknown-model"
    return harness, model


def task_id(task_name: str) -> str:
    """Remove the Rust file extension from a task name when present."""
    return task_name.removesuffix(".rs")


def _numeric(value: Any) -> float:
    """Convert a numeric value to ``float``, treating every other value as missing."""
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        return float(value)
    return math.nan


def load_task_metadata(
    metadata_path: Path, task_dirs: Path | Iterable[Path] | None = None
) -> tuple[pd.DataFrame, list[str]]:
    """Load task taxonomy metadata and optionally check it against task directories."""
    required = {"task_id", "proof_style", "source_module"}
    errors: list[str] = []
    records: list[dict[str, str]] = []
    seen: set[str] = set()

    try:
        with metadata_path.open(newline="") as metadata_file:
            reader = csv.DictReader(metadata_file)
            fields = set(reader.fieldnames or [])
            missing_fields = required - fields
            if missing_fields:
                raise ValueError(f"missing columns: {', '.join(sorted(missing_fields))}")
            for line_number, record in enumerate(reader, start=2):
                identifier = (record.get("task_id") or "").strip()
                proof_style = (record.get("proof_style") or "").strip()
                source_module = (record.get("source_module") or "").strip()
                if not identifier or not proof_style or not source_module:
                    errors.append(f"{metadata_path.name}:{line_number}: incomplete metadata row")
                    continue
                if identifier in seen:
                    errors.append(f"{metadata_path.name}:{line_number}: duplicate task {identifier}")
                    continue
                seen.add(identifier)
                records.append(
                    {
                        "task_id": identifier,
                        "proof_style": proof_style,
                        "source_module": source_module,
                    }
                )
    except (OSError, ValueError) as error:
        errors.append(f"{metadata_path.name}: {error}")

    metadata = pd.DataFrame.from_records(
        records, columns=["task_id", "proof_style", "source_module"]
    )

    if task_dirs is not None:
        directories = [task_dirs] if isinstance(task_dirs, Path) else list(task_dirs)
        task_files = {
            path.stem
            for directory in directories
            if directory.is_dir()
            for path in directory.glob("*.rs")
        }
        metadata_ids = set(metadata["task_id"]) if not metadata.empty else set()
        for identifier in sorted(task_files - metadata_ids):
            errors.append(f"task metadata missing for {identifier}")
        for identifier in sorted(metadata_ids - task_files):
            errors.append(f"task metadata references missing task {identifier}")

    return metadata, errors


def flatten_runs(runs: Iterable[dict[str, Any]], metadata: pd.DataFrame) -> pd.DataFrame:
    """Turn nested run JSON data into one table row per agent task attempt."""
    metadata_by_task = (
        metadata.set_index("task_id").to_dict("index") if not metadata.empty else {}
    )
    records: list[dict[str, Any]] = []
    for run in runs:
        timestamp = str(run.get("timestamp", ""))
        run_path = run.get("_path")
        run_id = Path(run_path).stem if isinstance(run_path, Path) else timestamp
        for agent_name, agent_data in run.get("agents", {}).items():
            if not isinstance(agent_data, dict):
                continue
            harness, model = split_agent_name(str(agent_name))
            condition = f"{harness} / {model}"
            entry_id = f"{run_id}::{agent_name}"
            tasks = agent_data.get("tasks", {})
            if not isinstance(tasks, dict):
                continue
            for task_name, result in tasks.items():
                if not isinstance(result, dict):
                    continue
                identifier = task_id(str(task_name))
                task_metadata = metadata_by_task.get(identifier, {})
                strict_success = (
                    result.get("verus_passed") is True
                    and result.get("cheat_checker_passed") is True
                )
                if strict_success:
                    outcome = "Valid repair"
                elif result.get("timed_out") is True:
                    outcome = "Timed out without a valid repair"
                elif result.get("verus_passed") is True:
                    outcome = "Verus passed, Lynette rejected"
                else:
                    outcome = "Verification failed"
                records.append(
                    {
                        "entry_id": entry_id,
                        "run_id": run_id,
                        "timestamp": timestamp,
                        "agent_name": str(agent_name),
                        "harness": harness,
                        "model": model,
                        "condition": condition,
                        "task_id": identifier,
                        "task_file": str(task_name),
                        "strict_success": strict_success,
                        "outcome": outcome,
                        "timed_out": result.get("timed_out") is True,
                        "verus_passed": result.get("verus_passed") is True,
                        "cheat_checker_passed": result.get("cheat_checker_passed") is True,
                        "cost_usd": _numeric(result.get("total_costs")),
                        "duration_seconds": _numeric(result.get("duration_seconds")),
                        "total_input_tokens": _numeric(
                            result.get("total_input_tokens")
                        ),
                        "total_output_tokens": _numeric(
                            result.get("total_output_tokens")
                        ),
                        "total_turns": _numeric(result.get("total_turns")),
                        "total_tool_calls": _numeric(result.get("total_tool_calls")),
                        "proof_style": task_metadata.get("proof_style"),
                        "source_module": task_metadata.get("source_module"),
                    }
                )
    return pd.DataFrame.from_records(records)


def discover_cohorts(
    attempts: pd.DataFrame, allowed_harnesses: Iterable[str] = ("opencode", "pi", "codex", "copilot")
) -> list[Cohort]:
    """Group attempts with the same tasks and keep the latest run per condition."""
    if attempts.empty:
        return []

    allowed = set(allowed_harnesses)
    eligible = attempts[attempts["harness"].isin(allowed)]
    entries: list[dict[str, Any]] = []
    for entry_id, group in eligible.groupby("entry_id", sort=False):
        task_ids = tuple(sorted(group["task_id"].unique()))
        entries.append(
            {
                "entry_id": entry_id,
                "task_ids": task_ids,
                "condition": str(group["condition"].iloc[0]),
                "timestamp": str(group["timestamp"].iloc[0]),
            }
        )

    by_task_set: dict[tuple[str, ...], list[dict[str, Any]]] = {}
    for entry in entries:
        by_task_set.setdefault(entry["task_ids"], []).append(entry)

    cohorts: list[Cohort] = []
    for task_ids, matching_entries in by_task_set.items():
        latest_by_condition: dict[str, dict[str, Any]] = {}
        for entry in matching_entries:
            previous = latest_by_condition.get(entry["condition"])
            if previous is None or entry["timestamp"] > previous["timestamp"]:
                latest_by_condition[entry["condition"]] = entry
        selected = sorted(latest_by_condition.values(), key=lambda item: item["condition"])
        digest = hashlib.sha1("\n".join(task_ids).encode()).hexdigest()[:8]
        cohorts.append(
            Cohort(
                signature=digest,
                task_ids=task_ids,
                entry_ids=tuple(item["entry_id"] for item in selected),
                conditions=tuple(item["condition"] for item in selected),
                latest_timestamp=max(item["timestamp"] for item in selected),
            )
        )

    cohorts.sort(
        key=lambda cohort: (
            len(cohort.task_ids),
            len(cohort.conditions),
            cohort.latest_timestamp,
        ),
        reverse=True,
    )
    return cohorts


def cohort_attempts(attempts: pd.DataFrame, cohort: Cohort) -> pd.DataFrame:
    """Return a copy of the attempts included in ``cohort``."""
    return attempts[attempts["entry_id"].isin(cohort.entry_ids)].copy()
