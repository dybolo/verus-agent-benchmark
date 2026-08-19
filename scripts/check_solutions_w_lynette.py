#!/usr/bin/env python3
"""Check that each task's designated reference proof is Lynette-safe.

The reference files in solutions/base each contain solutions for several tasks.
This script copies just the designated proof body into a temporary copy of each
task, leaving all unrelated holes untouched, then invokes lynette on that pair.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from difflib import SequenceMatcher
from pathlib import Path
from typing import cast

ROOT = Path(__file__).resolve().parents[1]
TASKS_DIR = ROOT / "tasks"
BASE_SOLUTIONS_DIR = ROOT / "solutions" / "base"


# The corpus naming convention identifies a task's reference module and proof
# target.  `cuckoo_inductive` is the one task deliberately covering several
# transition proofs.
SPECIAL_TARGETS: dict[str, tuple[str, ...]] = {
    "cuckoo_inductive": (
        "delete_key_value_inductive",
        "update_key_value_inductive",
        "insert_key_value_inductive",
        "swing_inductive",
    ),
}


FUNCTION = re.compile(r"(?m)^[ \t]*(?:(?:pub(?:\([^)]*\))?[ \t]+)?(?:proof[ \t]+)?fn)[ \t]+([A-Za-z_]\w*)\b")
IMPL = re.compile(r"(?m)^[ \t]*(?:unsafe[ \t]+)?impl\b")


@dataclass(frozen=True)
class Function:
    name: str
    start: int
    body_start: int
    end: int
    header: str
    body: str
    owner: str | None


@dataclass(frozen=True)
class Entry:
    task_id: str
    base_file: str
    targets: tuple[str, ...]

    @property
    def task_file(self) -> str:
        return f"{self.task_id}.rs"


def manifest_entries() -> list[Entry]:
    base_files: dict[str, str] = {path.stem: path.name for path in BASE_SOLUTIONS_DIR.glob("*.rs")}
    entries: list[Entry] = []
    for task_file in sorted(TASKS_DIR.glob("*.rs")):
        task_id = task_file.stem
        matching_stems = [
            stem for stem in base_files
            if task_id == stem or task_id.startswith(f"{stem}_")
        ]
        if not matching_stems:
            raise RuntimeError(f"could not derive a reference module for {task_id}")
        source_stem = max(matching_stems, key=len)
        suffix = task_id.removeprefix(source_stem).removeprefix("_")
        if task_id in SPECIAL_TARGETS:
            targets = SPECIAL_TARGETS[task_id]
        elif suffix.endswith("_drop"):
            targets = ("drop",)
        else:
            target = suffix.rstrip("_")
            if not target:
                raise RuntimeError(f"could not derive a target function for {task_id}")
            targets = (target,)
        entries.append(Entry(task_id, base_files[source_stem], targets))
    if not entries:
        raise RuntimeError(f"no task files found in {TASKS_DIR}")
    return entries


def code_mask(source: str) -> str:
    """Replace comments with whitespace without changing source offsets."""
    masked: list[str] = list(source)
    index = 0
    in_string = False
    line_comment = False
    block_comment = 0
    while index < len(source):
        char = source[index]
        next_char = source[index + 1] if index + 1 < len(source) else ""
        if line_comment:
            if char == "\n":
                line_comment = False
            else:
                masked[index] = " "
            index += 1
            continue
        if block_comment:
            if char == "/" and next_char == "*":
                masked[index:index + 2] = "  "
                block_comment += 1
                index += 2
                continue
            if char == "*" and next_char == "/":
                masked[index:index + 2] = "  "
                block_comment -= 1
                index += 2
                continue
            if char != "\n":
                masked[index] = " "
            index += 1
            continue
        if in_string:
            if char == "\\":
                index += 2
                continue
            if char == '"':
                in_string = False
            index += 1
            continue
        if char == '"':
            in_string = True
            index += 1
            continue
        if char == "/" and next_char == "/":
            masked[index:index + 2] = "  "
            line_comment = True
            index += 2
            continue
        if char == "/" and next_char == "*":
            masked[index:index + 2] = "  "
            block_comment = 1
            index += 2
            continue
        index += 1
    return "".join(masked)


def closing_brace(source: str, body_start: int) -> int | None:
    """Return the offset after a balanced brace pair in comment-masked source."""
    depth = 0
    index = body_start
    in_string = False
    while index < len(source):
        char = source[index]
        if in_string:
            if char == "\\":
                index += 2
                continue
            if char == '"':
                in_string = False
            index += 1
            continue
        if char == '"':
            in_string = True
            index += 1
            continue
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return index + 1
        index += 1
    return None


def impl_blocks(masked_source: str) -> list[tuple[int, int, str]]:
    blocks: list[tuple[int, int, str]] = []
    for match in IMPL.finditer(masked_source):
        body_start = masked_source.find("{", match.end())
        semicolon = masked_source.find(";", match.end())
        if body_start < 0 or (0 <= semicolon < body_start):
            continue
        end = closing_brace(masked_source, body_start)
        if end is None:
            continue
        owner = re.sub(r"\s+", "", masked_source[match.start():body_start])
        blocks.append((match.start(), end, owner))
    return blocks


def function_blocks(source: str) -> list[Function]:
    """Find functions, excluding declarations inside comments and recording owners."""
    masked_source = code_mask(source)
    implementations = impl_blocks(masked_source)
    result: list[Function] = []
    for match in FUNCTION.finditer(masked_source):
        body_start = masked_source.find("{", match.end())
        semicolon = masked_source.find(";", match.end())
        if body_start < 0 or (0 <= semicolon < body_start):
            continue  # Trait declaration or extern function.
        end = closing_brace(masked_source, body_start)
        if end is None:
            continue
        enclosing = [
            implementation for implementation in implementations
            if implementation[0] <= match.start() and end <= implementation[1]
        ]
        owner = (
            min(enclosing, key=lambda implementation: implementation[1] - implementation[0])[2]
            if enclosing else None
        )
        result.append(
            Function(
                match.group(1), match.start(), body_start, end,
                source[match.start():body_start], source[body_start:end], owner,
            )
        )
    return result


def normalise(text: str) -> str:
    return re.sub(r"\s+", "", code_mask(text))


def choose_pair(entry: Entry, task_source: str, base_source: str) -> list[tuple[Function, Function]]:
    task_functions = function_blocks(task_source)
    base_functions = function_blocks(base_source)

    pairs: list[tuple[Function, Function]] = []
    for name in entry.targets:
        task_candidates = [function for function in task_functions if function.name == name]
        base_candidates = [function for function in base_functions if function.name == name]
        if not task_candidates or not base_candidates:
            raise RuntimeError(f"could not locate {name!r} for {entry.task_id}")
        owner_matched = [
            (task_function, base_function)
            for task_function in task_candidates
            for base_function in base_candidates
            if task_function.owner == base_function.owner
        ]
        candidate_pairs = owner_matched or [
            (task_function, base_function)
            for task_function in task_candidates
            for base_function in base_candidates
        ]
        task_function, base_function = max(
            candidate_pairs,
            key=lambda pair: SequenceMatcher(
                None,
                normalise(pair[0].header + pair[0].body),
                normalise(pair[1].header + pair[1].body),
            ).ratio(),
        )
        pairs.append((task_function, base_function))
    return pairs


def test_function_selection() -> None:
    """Exercise comment filtering and owner-aware method selection."""
    commented_source = """
    /* impl Ignored {
        fn drop(self) { ignored(); }
    } */
    impl Kept {
        fn drop(self) { kept(); }
    }
    """
    functions = function_blocks(commented_source)
    if [function.owner for function in functions] != ["implKept"]:
        raise AssertionError("commented function declaration was not ignored")
    if "kept" not in functions[0].body:
        raise AssertionError("real function body was not retained")

    task_source = """
    impl WriteGuard {
        fn drop(self) { incomplete(); }
    }
    """
    base_source = """
    /* impl WriteGuard {
        fn drop(&mut self) { commented_out(); }
    } */
    impl ReadGuard {
        fn drop(self) { incomplete(); }
    }
    impl WriteGuard {
        fn drop(self) { completed_write_guard(); }
    }
    """
    entry = Entry("rwlock_writeguard_drop", "rwlock.rs", ("drop",))
    pairs = choose_pair(entry, task_source, base_source)
    if len(pairs) != 1 or "completed_write_guard" not in pairs[0][1].body:
        raise AssertionError("same-named method was not selected by impl owner")


def reconstruct(entry: Entry, destination: Path) -> None:
    task_source = (ROOT / "tasks" / entry.task_file).read_text(encoding="utf-8")
    base_source = (ROOT / "solutions" / "base" / entry.base_file).read_text(encoding="utf-8")
    pairs = choose_pair(entry, task_source, base_source)
    # Replace from the end to keep the remaining offsets valid.
    for task_function, base_function in sorted(pairs, key=lambda pair: pair[0].body_start, reverse=True):
        task_source = (
            task_source[:task_function.body_start]
            + base_function.body
            + task_source[task_function.end:]
        )
    _ = destination.write_text(task_source, encoding="utf-8")


def check(entry: Entry, generated_dir: Path) -> tuple[str, int, str]:
    generated = generated_dir / entry.task_file
    command = [sys.executable, "lynette/lynette.py", f"tasks/{entry.task_file}", str(generated)]
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, check=False)
    return entry.task_id, result.returncode, (result.stdout + result.stderr).strip()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument("--task", action="append", dest="task_ids", help="check only this task ID (repeatable)")
    _ = parser.add_argument("--jobs", type=int, default=8, help="parallel Lynette checks (default: 8)")
    _ = parser.add_argument("--keep-generated", type=Path, metavar="DIR", help="keep reconstructed files in DIR")
    _ = parser.add_argument("--self-test", action="store_true", help="run parser and function-selection regression checks")
    args = parser.parse_args()
    jobs = cast(int, args.jobs)
    self_test = cast(bool, args.self_test)
    task_ids = cast("list[str] | None", args.task_ids)
    keep_generated = cast("Path | None", args.keep_generated)
    if jobs < 1:
        parser.error("--jobs must be positive")
    if self_test:
        test_function_selection()
        print("Self-test passed.")
        return 0

    entries = manifest_entries()
    if task_ids:
        wanted = set(task_ids)
        entries = [entry for entry in entries if entry.task_id in wanted]
        unknown = wanted - {entry.task_id for entry in entries}
        if unknown:
            parser.error(f"unknown task ID(s): {', '.join(sorted(unknown))}")

    temporary_dir: tempfile.TemporaryDirectory[str] | None = None
    generated_dir: Path
    if keep_generated:
        generated_dir = keep_generated.resolve()
        if generated_dir.exists() and any(generated_dir.iterdir()):
            parser.error(f"--keep-generated directory is not empty: {generated_dir}")
        generated_dir.mkdir(parents=True, exist_ok=True)
    else:
        temporary_dir = tempfile.TemporaryDirectory(prefix="lynette-base-check-")
        generated_dir = Path(temporary_dir.name)

    try:
        for entry in entries:
            reconstruct(entry, generated_dir / entry.task_file)

        def check_entry(entry: Entry) -> tuple[str, int, str]:
            return check(entry, generated_dir)

        with ThreadPoolExecutor(max_workers=jobs) as executor:
            results = list(executor.map(check_entry, entries))
    finally:
        if temporary_dir:
            temporary_dir.cleanup()

    failures = [(task_id, output) for task_id, status, output in results if status != 0]
    print(f"Checked {len(results)} task(s): {len(results) - len(failures)} passed, {len(failures)} failed.")
    for task_id, output in failures:
        print(f"\nFAIL {task_id}\n{output}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
