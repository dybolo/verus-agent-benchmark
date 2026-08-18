#!/usr/bin/env python
"""Inline a modular Verus crate into one file accepted by `verus <file>`."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import cast

MODULE = re.compile(
    r"^(?P<i>[ \t]*)(?P<v>pub(?:\([^)]*\))?\s+)?mod\s+(?P<n>[A-Za-z_]\w*)\s*;[ \t]*(?://.*)?$",
    re.MULTILINE,
)

PROOF = re.compile(
    r"^[ \t]*(?:pub(?:\([^)]*\))?[ \t]+)?proof[ \t]+fn\b", re.MULTILINE
)


@dataclass
class Arguments:
    source: Path
    crate_root: Path | None


@dataclass(frozen=True)
class InlineContext:
    root: Path
    target: Path


def find_crate_root(source: Path) -> Path:
    for item in (source.parent, *source.parents):
        if (item / "Cargo.toml").is_file() and (item / "src/lib.rs").is_file():
            return item
    raise ValueError("could not find crate root; pass --crate-root")


def crate_entrypoint(root: Path) -> Path:
    """Return the library entrypoint for Cargo and flat Verus module trees."""
    cargo_entrypoint = root / "src/lib.rs"
    if cargo_entrypoint.is_file():
        return cargo_entrypoint
    flat_entrypoint = root / "lib.rs"
    if flat_entrypoint.is_file():
        return flat_entrypoint
    raise ValueError("crate root must contain src/lib.rs or lib.rs")


def child_module(parent: Path, name: str) -> Path | None:
    for candidate in (parent.parent / f"{name}.rs", parent.parent / name / "mod.rs"):
        if candidate.is_file():
            return candidate
    return None


def closing_brace(text: str, opening: int) -> int:
    depth, block_depth, i, state = 0, 0, opening, "code"
    while i < len(text):
        char, nxt = text[i], text[i + 1] if i + 1 < len(text) else ""
        if state == "code":
            if char == '"':
                state = "string"
            elif char == "'":
                state = "char"
            elif char == "/" and nxt == "/":
                state, i = "line", i + 1
            elif char == "/" and nxt == "*":
                state, block_depth, i = "block", 1, i + 1
            elif char == "{":
                depth += 1
            elif char == "}":
                depth -= 1
                if depth == 0:
                    return i
        elif state == "string":
            if char == "\\":
                i += 1
            elif char == '"':
                state = "code"
        elif state == "char":
            if char == "\\":
                i += 1
            elif char == "'":
                state = "code"
        elif state == "line" and char == "\n":
            state = "code"
        elif state == "block":
            if char == "/" and nxt == "*":
                block_depth, i = block_depth + 1, i + 1
            elif char == "*" and nxt == "/":
                block_depth, i = block_depth - 1, i + 1
                if block_depth == 0:
                    state = "code"
        i += 1
    raise ValueError("unmatched proof-function brace")


def proof_body_opening(text: str, start: int) -> int:
    """Find a proof-function body opening, skipping braces in its contract."""
    position = start
    while True:
        position = text.find("{", position)
        if position < 0:
            return -1
        line_start = text.rfind("\n", 0, position) + 1
        prefix = text[line_start:position].strip()
        # In the supported source layout, proof bodies start on their own line.
        # A contract may also contain a `match ... {` whose expression happens
        # to end in `)`, so accepting every such line would replace part of the
        # contract rather than only the proof body.
        if not prefix:
            return position
        position += 1


def leading_indent(text: str) -> str:
    return text[: len(text) - len(text.lstrip(" \t"))]


def externalize_proofs(text: str) -> str:
    """Keep proof contracts, replacing only `proof fn` bodies with trusted stubs."""
    out: list[str] = []
    cursor = 0
    for match in PROOF.finditer(text):
        opening, semicolon = (
            proof_body_opening(text, match.end()),
            text.find(";", match.end()),
        )
        if opening < 0 or 0 <= semicolon < opening:
            continue
        end = closing_brace(text, opening)
        line = text.rfind("\n", 0, match.start()) + 1
        indent = leading_indent(text[line:])
        nearby = "\n".join(text[:line].splitlines()[-5:])

        # Verus requires bodies for functions used to justify recursive specs.
        # Declarations already marked trusted must also retain their source form:
        # adding `external_body` changes how their theorem contracts are used.
        if (
            "via_fn" in nearby
            or "decreases_by" in nearby
            or "verus::trusted" in nearby
        ):
            continue

        out.append(text[cursor:line])
        if "external_body" not in nearby:
            out.append(f"{indent}#[verifier::external_body]\n")
        out.append(text[line:opening])
        out.append(f"{{\n{indent}    unimplemented!()\n{indent}}}")
        cursor = end + 1
    out.append(text[cursor:])
    return "".join(out)


def ensure_not_recursive(
    path: Path, context: InlineContext, ancestors: tuple[Path, ...]
) -> None:
    if path in ancestors:
        raise ValueError(
            "recursive module declaration: "
            + " -> ".join(
                str(ancestor.relative_to(context.root))
                for ancestor in (*ancestors, path)
            )
        )


def transform_source(path: Path, context: InlineContext, source: str) -> str:
    """Trust dependency proof bodies while preserving all other source verbatim."""
    if path == context.target:
        return source
    return externalize_proofs(source)


def inline(path: Path, context: InlineContext, ancestors: tuple[Path, ...] = ()) -> str:
    path = path.resolve()
    ensure_not_recursive(path, context, ancestors)
    source = transform_source(path, context, path.read_text())

    # Inline each local `mod name;` declaration by recursively expanding its source file.
    def replace(match: re.Match[str]) -> str:
        child = child_module(path, match.group("n"))
        if child is None:
            return match.group(0)

        body = inline(child, context, (*ancestors, path))
        return f"{match.group('i')}{match.group('v') or ''}mod {match.group('n')} {{\n{body}\n{match.group('i')}}}"

    source = MODULE.sub(replace, source)

    rel, label = (
        path.relative_to(context.root),
        "TARGET SOURCE" if path == context.target else "INLINED DEPENDENCY",
    )
    section = f"// ===== BEGIN {label}: {rel} =====\n{source.rstrip()}\n// ===== END {label}: {rel} ====="
    return section


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument("source", type=Path)
    _ = parser.add_argument("--crate-root", type=Path)
    parsed_args = parser.parse_args()

    args = Arguments(
        source=cast(Path, parsed_args.source),
        crate_root=cast(Path | None, parsed_args.crate_root),
    )

    source = args.source.resolve()
    if not source.is_file():
        parser.error(f"missing source: {source}")

    root = args.crate_root.resolve() if args.crate_root else find_crate_root(source)
    try:
        entrypoint = crate_entrypoint(root)
    except ValueError as error:
        parser.error(str(error))
    if root not in source.parents:
        parser.error("source must be below crate-root")

    solutions_base = Path(__file__).resolve().parents[1] / "solutions" / "base"
    output = (solutions_base / f"{source.stem}_standalone.rs").resolve()
    output.parent.mkdir(parents=True, exist_ok=True)

    _ = output.write_text(
        inline(entrypoint, InlineContext(root, source)) + "\n\nfn main() {}\n"
    )

    print(f"Wrote {output}")
    return subprocess.run(["verus", str(output)], check=False).returncode


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
