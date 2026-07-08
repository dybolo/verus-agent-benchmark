#!/usr/bin/env python3
"""
Unified Semantic Grep Tool
Combines indexing (ast-grep + embeddings) and searching in a single script.

Supplies code snippets relevant to a proof plan.

Usage:
    python semantic_grep_unified.py --index [--repo-path <path>] [--db-path <path>]
    python semantic_grep_unified.py --search <proof-plan> [--type proofs|specs] [--db-path <path>] [--num-results 10]
    python semantic_grep_unified.py --search [--type proofs|specs] [--db-path <path>]

The --search argument accepts a proof plan as input — a structured analysis of the
verification goal. The tool then returns code snippets relevant to that plan.
The proof plan should follow this template:
  - What needs to be shown
  - Assumptions
  - Key ideas
  - High-level strategy
  - Sub-goals
"""

import pdb
import sys
import re
import json
import argparse
import asyncio
import litellm
import yaml
from pathlib import Path
from typing import Optional, List, Dict, Any
from ast_grep_py import register_dynamic_language
from ast_grep_py import SgRoot


def log(*args, **kwargs):
    kwargs.setdefault('file', sys.stderr)
    print(*args, **kwargs)


class SemanticGrepConfig:
    """Configuration for the semantic grep tool."""

    def __init__(self,
        generation_model: str,
        repo_path: str = ".",
        patterns_file: Optional[str] = None,
        skip_descriptions: bool = False,
        tree_sitter_verus_path: Optional[str] = None
    ):
        self.repo_path = Path(repo_path).resolve()
        self.patterns_file = patterns_file or self._find_patterns_file()
        self.skip_descriptions = skip_descriptions
        self.tree_sitter_verus_path = Path(tree_sitter_verus_path) if tree_sitter_verus_path else None
        self.processed_chunks_file = self.repo_path / "ast-grep_chunks_processed.json"
        self.generation_model = generation_model

    def _find_patterns_file(self) -> str:
        """Look for patterns file in common locations."""
        candidates = [
            self.repo_path / "verus_patterns.yml",
            self.repo_path / "patterns.yml",
            Path(__file__).parent / "verus_patterns.yml",
        ]
        for candidate in candidates:
            if candidate.exists():
                return str(candidate)
        raise FileNotFoundError("Could not find patterns file (verus_patterns.yml or patterns.yml)")

    def validate(self):
        """Validate configuration."""
        if not self.repo_path.exists():
            raise ValueError(f"Repository path does not exist: {self.repo_path}")
        if not self.patterns_file or not Path(self.patterns_file).exists():
            raise ValueError(f"Patterns file does not exist: {self.patterns_file}")
        if not self.tree_sitter_verus_path or not self.tree_sitter_verus_path.exists():
            raise ValueError(f"Tree-sitter Verus library path does not exist: {self.tree_sitter_verus_path}")


class AstGrepChunker:
    """Handles code extraction using the ast-grep Python API."""

    def __init__(self, config: SemanticGrepConfig):
        self.config = config
        self._register_language()

    def _register_language(self):
        """Register the Verus custom language from the provided library path."""
        register_dynamic_language({
            "verus": {
                "library_path": str(self.config.tree_sitter_verus_path),
                "extensions": ["rs"],
            }
        })

    def _load_rules(self) -> List[Dict]:
        """Load rules from the patterns YAML file."""
        rules = []
        with open(self.config.patterns_file) as f:
            for doc in yaml.safe_load_all(f):
                if doc:
                    rules.append(doc)
        return rules

    def run(self) -> List[Dict]:
        """Run ast-grep via Python API to extract code chunks."""

        rules = self._load_rules()
        repo = self.config.repo_path

        chunks = []
        rs_files = sorted(repo.rglob("*.rs"))

        for _, file_path in enumerate(rs_files):
            rel_path = file_path.relative_to(repo)

            with open(file_path) as f:
                content = f.read()
            lines = content.split("\n")
            root = SgRoot(content, "verus").root()

            for rule in rules:
                config_dict = {"rule": rule["rule"]}
                matches = root.find_all(config=config_dict)
                for node in matches:
                    r = node.range()
                    ctx_start = max(0, r.start.line)
                    ctx_end = min(len(lines), r.end.line)
                    chunks.append({
                        "text": "\n".join(lines[ctx_start:ctx_end]),
                        "file": str(rel_path),
                        "range": {
                            "start": {"line": r.start.line},
                            "end": {"line": r.end.line},
                        },
                        "ruleId": rule["id"],
                        "language": rule.get("language", "verus"),
                    })

        log(f"✓ Extracted {len(chunks)} chunks")
        return chunks


class DescriptionGenerator:
    """Generates natural language descriptions for code chunks using LLM."""

    def __init__(self, model: str):
        self.model = model
        prompts_dir = Path(__file__).parent / "prompts"
        self.spec_prompt_template = (prompts_dir / "spec-prompt.txt").read_text()
        self.proof_prompt_template = (prompts_dir / "proof-prompt.txt").read_text()

    async def generate_description(self, code_text: str, kind: str) -> str:
        """Generate description for a code chunk."""

        prompt = (
            self.proof_prompt_template.format(code_text=code_text)
            if kind == "proof"
            else self.spec_prompt_template.format(code_text=code_text)
        )

        try:
            response = await litellm.acompletion(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
            )
            content = response.choices[0].message.content.strip()

            content = re.sub(r'[*_]{1,3}', '', content)
            content = re.sub(r'^#+\s*', '', content, flags=re.MULTILINE)
            content = re.sub(r'\n+', ' ', content)

            return content.strip()
        except Exception as e:
            log(f"Warning: Failed to generate description: {repr(e)}")
            return "[Error generating description]"

    async def generate_batch(self, chunks: List[Dict], max_concurrent: int = 10) -> None:
        """Generate descriptions for multiple chunks concurrently."""
        semaphore = asyncio.Semaphore(max_concurrent)

        async def bounded_request(chunk: Dict):
               async with semaphore:
                   try:
                       chunk["description"] = await self.generate_description(chunk["code"], chunk["kind"])
                   except Exception as e:
                       log(f"Error processing chunk {chunk['id']}: {e}")
                       chunk["description"] = "[Error generating description]"

        tasks = [bounded_request(chunk) for chunk in chunks]
        await asyncio.gather(*tasks, return_exceptions=True)


class SemanticGrep:
    """Main semantic grep tool combining all components."""

    def __init__(self, config: SemanticGrepConfig):
        self.config = config
        self.chunker = AstGrepChunker(config)
        self.description_gen = DescriptionGenerator(model=config.generation_model)

    def index(self):
        """Index a repository."""
        log("\n" + "="*60 + "")
        log("Semantic Grep Indexing")
        log(f"Repository: {self.config.repo_path}")
        log("" + "="*60 + "")

        try:
            self.config.validate()

            # Step 1: Extract chunks using ast-grep
            log("\n Running ast-grep scan...")
            chunks = self.chunker.run()
            if not chunks:
                log("Warning: No chunks extracted")
                return

            # Step 2: Process chunks first to classify them by kind (spec vs proof)
            log("\n Processing chunks...")
            processed_chunks = self._process_chunks(chunks)

            # Step 3: Generate descriptions based on chunk kind
            if not self.config.skip_descriptions:
                log("\n Generating natural language descriptions...")
                asyncio.run(self.description_gen.generate_batch(processed_chunks))

            # Save processed chunks
            with open(self.config.processed_chunks_file, "w") as f:
                json.dump(processed_chunks, f, indent=2)

            log("✓ Indexing complete!")
            log(f"Processed chunks saved to: {self.config.processed_chunks_file}")

        except Exception as e:
            log(f"Error during indexing: {e}")
            sys.exit(1)

    def _process_chunks(self, chunks: List[Dict]) -> List[Dict]:
        """Process raw chunks into processable format."""
        processed = []

        for i, chunk in enumerate(chunks):
            code_text = chunk.get("text", "")
            file_path = chunk.get("file", "unknown")
            range_info = chunk.get("range", {})
            start_line = range_info.get("start", {}).get("line", 0) + 1
            end_line = range_info.get("end", {}).get("line", 0) + 1

            processed.append({
                "id": f"chunk_{i}",
                "code": code_text,
                "description": "",
                "ruleId": chunk.get("ruleId", ""),
                "kind": (
                    "spec" if chunk.get("ruleId", "").startswith("capture-spec")
                    else "proof" if (chunk.get("ruleId", "").startswith("capture-proof")
                                      or chunk.get("ruleId", "") == "capture-functions-with-contracts")
                    else "unknown"
                ),
                "file": file_path,
                "language": chunk.get("language", "unknown"),
                "start_line": start_line,
                "end_line": end_line
            })

        return processed


def main():
    parser = argparse.ArgumentParser(
        description="Unified Semantic Grep: Index proof/spec verus code",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Index current directory
  python semantic_grep_unified.py

  # Index specific repository
  python semantic_grep_unified.py --repo-path /path/to/repo

  # Index without generating descriptions
  python semantic_grep_unified.py --skip-descriptions
        """
    )

    parser.add_argument("--repo-path", default=".", help="Path to repository (default: current directory)")
    parser.add_argument("--patterns", help="Path to ast-grep patterns file (auto-detected if not provided)")
    parser.add_argument("--tree-sitter-verus-path", required=True,
                        help="Path to the Verus tree-sitter shared library (.so / .dylib)")
    parser.add_argument("--skip-descriptions", action="store_true",
                        help="Skip LLM description generation (faster indexing)")
    parser.add_argument("--generation-model", default="openrouter/openai/gpt-5.4-nano",
                        help="Generation model to use (default: openrouter/openai/gpt-5.4-nano)")

    args = parser.parse_args()

    try:
        # Create configuration
        config = SemanticGrepConfig(
            repo_path=args.repo_path,
            patterns_file=args.patterns,
            skip_descriptions=args.skip_descriptions,
            tree_sitter_verus_path=args.tree_sitter_verus_path,
            generation_model=args.generation_model,
        )

        # Create semantic grep instance
        sg = SemanticGrep(config)
        sg.index()

    except KeyboardInterrupt:
        log("\nInterrupted by user")
        sys.exit(0)
    except Exception as e:
        log(f"Fatal error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
