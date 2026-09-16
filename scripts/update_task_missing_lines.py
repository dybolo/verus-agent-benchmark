#!/usr/bin/env python3
"""Update task metadata with the number of non-empty source lines each task omits."""

from __future__ import annotations

import csv
import difflib
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
METADATA_PATH = ROOT / "streamlit_app" / "src" / "streamlit_app" / "task_metadata.csv"
SOURCE_DIR = ROOT / "solutions" / "base"
TASKS_DIR = ROOT / "tasks"
FULL_TASKS_DIR = ROOT / "full_tasks"
MISSING_CODE_LINES_COLUMN = "missing_code_lines"


@dataclass(frozen=True)
class TaskMissingLines:
    task_id: str
    missing_code_lines: int
    source_path: Path
    task_path: Path


def read_metadata(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open(encoding="utf-8", newline="") as metadata_file:
        reader = csv.DictReader(metadata_file)
        fieldnames = list(reader.fieldnames or [])
        rows = list(reader)

    required = {"task_id", "proof_style", "source_module"}
    missing = required - set(fieldnames)
    if missing:
        raise ValueError(f"{path}: missing columns: {', '.join(sorted(missing))}")
    return fieldnames, rows


def count_code_lines(lines: list[str]) -> int:
    """Count non-empty lines, including comments and delimiter-only lines."""
    return sum(bool(line.strip()) for line in lines)


def count_missing_code_lines(source_lines: list[str], task_lines: list[str]) -> int:
    """Count source lines left unmatched by each edit block in a line diff.

    A replacement containing the same number of non-empty lines is an edit, not
    missing code. Blank-line changes and task-only insertions do not contribute.
    Disabling ``autojunk`` keeps matching deterministic for large Rust files with
    many repeated braces and attributes.
    """
    matcher = difflib.SequenceMatcher(
        None, source_lines, task_lines, autojunk=False
    )
    missing_lines = 0
    for operation, source_start, source_end, task_start, task_end in matcher.get_opcodes():
        if operation == "equal" or operation == "insert":
            continue
        source_count = count_code_lines(source_lines[source_start:source_end])
        replacement_count = count_code_lines(task_lines[task_start:task_end])
        missing_lines += max(source_count - replacement_count, 0)
    return missing_lines


def task_path_for(row: dict[str, str], root: Path) -> Path:
    task_id = row.get("task_id", "").strip()
    proof_style = row.get("proof_style", "").strip()
    directory = root / ("full_tasks" if proof_style == "full-file" else "tasks")
    return directory / f"{task_id}.rs"


def calculate_all_missing_lines(
    rows: list[dict[str, str]], root: Path = ROOT
) -> list[TaskMissingLines]:
    task_ids = [row.get("task_id", "").strip() for row in rows]
    empty_ids = [index + 2 for index, task_id in enumerate(task_ids) if not task_id]
    if empty_ids:
        raise ValueError(
            "metadata has empty task IDs on lines "
            + ", ".join(str(line) for line in empty_ids)
        )

    duplicate_ids = sorted(
        {task_id for task_id in task_ids if task_ids.count(task_id) > 1}
    )
    if duplicate_ids:
        raise ValueError(f"duplicate metadata task IDs: {', '.join(duplicate_ids)}")

    source_cache: dict[Path, list[str]] = {}
    results: list[TaskMissingLines] = []
    for row in rows:
        task_id = row["task_id"].strip()
        source_module = row.get("source_module", "").strip()
        if not source_module:
            raise ValueError(f"{task_id}: source_module is empty")

        source_path = root / "solutions" / "base" / source_module
        task_path = task_path_for(row, root)
        if not source_path.is_file():
            raise FileNotFoundError(f"{task_id}: source module not found: {source_path}")
        if not task_path.is_file():
            raise FileNotFoundError(f"{task_id}: task file not found: {task_path}")

        if source_path not in source_cache:
            source_cache[source_path] = source_path.read_text(encoding="utf-8").splitlines()
        source_lines = source_cache[source_path]
        task_lines = task_path.read_text(encoding="utf-8").splitlines()
        results.append(
            TaskMissingLines(
                task_id=task_id,
                missing_code_lines=count_missing_code_lines(source_lines, task_lines),
                source_path=source_path,
                task_path=task_path,
            )
        )
    return results


def metadata_is_current(
    rows: list[dict[str, str]], results: list[TaskMissingLines]
) -> bool:
    expected = {result.task_id: str(result.missing_code_lines) for result in results}
    return all(
        row.get(MISSING_CODE_LINES_COLUMN) == expected.get(row.get("task_id", "").strip())
        for row in rows
    )


def write_metadata(
    path: Path,
    fieldnames: list[str],
    rows: list[dict[str, str]],
    results: list[TaskMissingLines],
) -> None:
    output_fields = list(fieldnames)
    if MISSING_CODE_LINES_COLUMN not in output_fields:
        output_fields.append(MISSING_CODE_LINES_COLUMN)

    results_by_task = {result.task_id: result for result in results}
    output_rows: list[dict[str, str]] = []
    for row in rows:
        output_row = dict(row)
        task_id = row["task_id"].strip()
        output_row[MISSING_CODE_LINES_COLUMN] = str(
            results_by_task[task_id].missing_code_lines
        )
        output_rows.append(output_row)

    with path.open("w", encoding="utf-8", newline="") as metadata_file:
        writer = csv.DictWriter(
            metadata_file, fieldnames=output_fields, lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(output_rows)


def main() -> int:
    fieldnames, rows = read_metadata(METADATA_PATH)
    results = calculate_all_missing_lines(rows)
    write_metadata(METADATA_PATH, fieldnames, rows, results)
    print(f"Updated {len(results)} tasks in {METADATA_PATH}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
