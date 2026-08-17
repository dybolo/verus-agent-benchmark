#!/usr/bin/env python
"""Remove Rust line and nested block comments and their resulting empty lines.

By default this reports the files that would change.  Pass --in-place to
rewrite them.  The optional path defaults to tasks and may be a single .rs
file or a directory searched recursively.
"""

from __future__ import annotations

import argparse
from pathlib import Path


def raw_string_end(source: str, start: int) -> int | None:
    """Return the exclusive end of a raw string beginning at `start` (the r)."""
    if source[start] != "r":
        return None
    cursor = start + 1
    while cursor < len(source) and source[cursor] == "#":
        cursor += 1
    if cursor == len(source) or source[cursor] != '"':
        return None
    terminator = '"' + source[start + 1 : cursor]
    end = source.find(terminator, cursor + 1)
    return None if end == -1 else end + len(terminator)


def quoted_char_end(source: str, start: int) -> int | None:
    """Return the end of a Rust character literal, excluding lifetimes."""
    cursor = start + 1
    if cursor >= len(source) or source[cursor] in "\r\n":
        return None
    if source[cursor] == "\\":
        cursor += 1
        if cursor >= len(source):
            return None
        if source[cursor] == "u" and cursor + 1 < len(source) and source[cursor + 1] == "{":
            close = source.find("}", cursor + 2)
            if close == -1:
                return None
            cursor = close + 1
        else:
            cursor += 1
    else:
        cursor += 1
    return cursor + 1 if cursor < len(source) and source[cursor] == "'" else None


def string_end(source: str, start: int) -> int:
    cursor = start + 1
    while cursor < len(source):
        if source[cursor] == "\\":
            cursor += 2
        elif source[cursor] == '"':
            return cursor + 1
        else:
            cursor += 1
    return len(source)


def strip_comments(source: str) -> str:
    output: list[str] = []
    cursor = 0
    length = len(source)
    while cursor < length:
        raw_end = raw_string_end(source, cursor)
        if raw_end is not None:
            output.append(source[cursor:raw_end])
            cursor = raw_end
        elif source[cursor] == '"':
            end = string_end(source, cursor)
            output.append(source[cursor:end])
            cursor = end
        elif source[cursor] == "'":
            end = quoted_char_end(source, cursor)
            if end is None:
                output.append("'")
                cursor += 1
            else:
                output.append(source[cursor:end])
                cursor = end
        elif source.startswith("//", cursor):
            end = source.find("\n", cursor)
            cursor = length if end == -1 else end
        elif source.startswith("/*", cursor):
            start = cursor
            cursor += 2
            depth = 1
            while cursor < length and depth:
                if source.startswith("/*", cursor):
                    depth += 1
                    cursor += 2
                elif source.startswith("*/", cursor):
                    depth -= 1
                    cursor += 2
                else:
                    cursor += 1
            comment = source[start:cursor]
            output.append("".join(character if character in "\r\n" else " " for character in comment))
        else:
            output.append(source[cursor])
            cursor += 1
    without_comments = "".join(output)
    original_lines = source.splitlines(keepends=True)
    stripped_lines = without_comments.splitlines(keepends=True)
    return "".join(
        stripped_line
        for original_line, stripped_line in zip(original_lines, stripped_lines)
        if stripped_line.strip() or not original_line.strip()
    )


def rust_files(target: Path) -> list[Path]:
    if target.is_file():
        return [target] if target.suffix == ".rs" else []
    return sorted(target.rglob("*.rs"))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", nargs="?", type=Path, default=Path("tasks"))
    parser.add_argument("--in-place", action="store_true", help="rewrite files instead of previewing")
    args = parser.parse_args()

    files = rust_files(args.path)
    if not files:
        parser.error(f"no Rust files found under {args.path}")
    changed = 0
    for file in files:
        original = file.read_text(encoding="utf-8")
        stripped = strip_comments(original)
        if original != stripped:
            changed += 1
            print(file)
            if args.in_place:
                file.write_text(stripped, encoding="utf-8")
    action = "Updated" if args.in_place else "Would update"
    print(f"{action} {changed} of {len(files)} Rust files.")


if __name__ == "__main__":
    main()
