#!/usr/bin/env python3
"""
Unified Semantic Grep Tool
Combines indexing (ast-grep + embeddings) and searching in a single script.

Usage:
    python semantic_grep_unified.py --index [--repo-path <path>] [--db-path <path>]
    python semantic_grep_unified.py --search <query> [--type proofs|specs] [--db-path <path>] [--num-results 10]
    python semantic_grep_unified.py --search [--type proofs|specs] [--db-path <path>]
"""

import pdb
import os
import sys
import re
import json
import argparse
import asyncio
import aiohttp
import chromadb
import yaml
import requests
from pathlib import Path
from typing import Optional, List, Dict, Any
from ast_grep_py import register_dynamic_language
from ast_grep_py import SgRoot


def log(*args, **kwargs):
    kwargs.setdefault('file', sys.stderr)
    print(*args, **kwargs)


class SemanticGrepConfig:
    """Configuration for the semantic grep tool."""

    def __init__(self, repo_path: str = ".", db_path: Optional[str] = None,
                 patterns_file: Optional[str] = None, skip_descriptions: bool = False,
                 tree_sitter_verus_path: Optional[str] = None):
        self.repo_path = Path(repo_path).resolve()
        self.db_path = Path(db_path) if db_path else self.repo_path / ".semantic_grep_db"
        self.patterns_file = patterns_file or self._find_patterns_file()
        self.skip_descriptions = skip_descriptions
        self.tree_sitter_verus_path = Path(tree_sitter_verus_path) if tree_sitter_verus_path else None

        self.chunks_file = self.repo_path / "ast-grep_chunks.json"
        self.processed_chunks_file = self.repo_path / "ast-grep_chunks_processed.json"
        self.collection_name = "code_chunks"

        # Embedding settings
        self.embedding_model = "openai/text-embedding-3-small"

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

        log("\n[1/4] Running ast-grep scan (Python API)...")

        rules = self._load_rules()
        repo = self.config.repo_path

        chunks = []
        rs_files = sorted(repo.rglob("*.rs"))

        for file_idx, file_path in enumerate(rs_files):
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
                    ctx_start = max(0, r.start.line - 50)
                    ctx_end = min(len(lines), r.end.line + 50)
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

        with open(self.config.chunks_file, "w") as f:
            json.dump(chunks, f, indent=2)

        return chunks


class DescriptionGenerator:
    """Generates natural language descriptions for code chunks using LLM."""

    def __init__(self, skip: bool = False):
        self.skip = skip
        self.api_key = os.getenv("OPENROUTER_API_KEY")

    async def generate_description(self, code_text: str, kind: str, session: aiohttp.ClientSession) -> str:
        """Generate description for a code chunk."""
        if self.skip:
            return "[Description generation skipped]"

        if not self.api_key:
            return "[OPENROUTER_API_KEY not set]"

        headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
        }

        spec_prompt = f"""Analyze this code and provide a concise natural language description of what it does.
Be specific about the intent and logic. Keep it to 2-3 sentences.
IMPORTANT: Output ONLY plain text. Do not use any markdown formatting, headings, bold text, or bullet points.
Code:
{code_text}
"""
        proof_prompt = f"""Analyze this code and provide a concise natural language proof plan that explains how the proof was done.
Be specific about the intent and logic. Keep it as short as you can.
IMPORTANT: Output ONLY plain text. Do not use any markdown formatting, headings, bold text, or bullet points.
Code:
{code_text}
"""

        payload = {
            "model": "openai/gpt-5.4-nano",
            "messages": [
                {
                    "role": "user",
                    "content": proof_prompt if kind == "proof" else spec_prompt
                }
            ],
        }

        try:
            async with session.post("https://openrouter.ai/api/v1/chat/completions",
                                    headers=headers, json=payload, timeout=30) as response:
                if response.status != 200:
                    return "[Error generating description]"
                data = await response.json()
                content = data["choices"][0]["message"]["content"].strip()

                # Basic cleanup: remove markdown bold/italics and hash headings
                content = re.sub(r'[*_]{1,3}', '', content)
                content = re.sub(r'^#+\s*', '', content, flags=re.MULTILINE)

                # Squish multiple newlines into a single space
                content = re.sub(r'\n+', ' ', content)

                return content.strip()
        except Exception as e:
            console.print(f"    [yellow]Warning: Failed to generate description: {e}[/yellow]")
            return "[Error generating description]"

    async def generate_batch(self, chunks: List[Dict], max_concurrent: int = 5) -> List[str]:
        """Generate descriptions for multiple chunks concurrently."""
        if self.skip:
            return ["[Skipped]"] * len(chunks)

        descriptions = [None] * len(chunks)
        semaphore = asyncio.Semaphore(max_concurrent)

        log("Generating descriptions...")

        async def bounded_request(index: int, code_text: str, kind: str, session: aiohttp.ClientSession):
               async with semaphore:
                   try:
                       desc = await self.generate_description(code_text, kind, session)
                       descriptions[index] = desc
                   except Exception as e:
                       log(f"Error proccessing chunk {index}: {e}")
                       descriptions[index] = "[Error generating description]"

        async with aiohttp.ClientSession() as session:
               tasks = [bounded_request(i, chunk["code"], chunk["kind"], session) for i, chunk in enumerate(chunks)]
               await asyncio.gather(*tasks, return_exceptions=True)

        return descriptions


class EmbeddingGenerator:
    """Generates embeddings for code chunks via API."""

    def __init__(self, model_name: str = "openai/text-embedding-3-small",
                 api_key: Optional[str] = None,
                 api_url: Optional[str] = None):
        self.model_name = model_name
        self.api_key = api_key or os.getenv("OPENROUTER_API_KEY")
        self.api_url = api_url or "https://openrouter.ai/api/v1/embeddings"

    def encode(self, texts: List[str]) -> List:
        """Encode texts to embeddings via API."""

        log(f"\nGenerating embeddings for {len(texts)} chunks...")

        headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
        }

        BATCH_SIZE = 128
        all_embeddings = []

        for i in range(0, len(texts), BATCH_SIZE):
            batch = texts[i:i + BATCH_SIZE]
            payload = {
                "input": batch,
                "model": self.model_name,
            }

            response = requests.post(self.api_url, headers=headers, json=payload, timeout=120)
            if response.status_code != 200:
                raise RuntimeError(f"Embedding API error ({response.status_code}): {response.text}")

            data = response.json()
            embeddings = [d["embedding"] for d in sorted(data["data"], key=lambda x: x["index"])]
            all_embeddings.extend(embeddings)

        return all_embeddings


class ChromaDBManager:
    """Manages ChromaDB operations."""

    def __init__(self, db_path: Path, collection_name: str = "code_chunks"):
        self.db_path = db_path
        self.collection_name = collection_name
        self.client = None
        self.collection = None

    def initialize(self, recreate: bool = False):
        """Initialize ChromaDB client and collection."""
        # Create DB directory if it doesn't exist
        self.db_path.parent.mkdir(parents=True, exist_ok=True)

        self.client = chromadb.PersistentClient(path=str(self.db_path))

        if recreate:
            try:
                self.client.delete_collection(self.collection_name)
            except:
                pass

        self.collection = self.client.get_or_create_collection(
            name=self.collection_name,
            metadata={"hnsw:space": "cosine"}
        )

    def store_chunks(self, processed_chunks: List[Dict], embeddings: List):
        """Store chunks with embeddings in ChromaDB."""
        log("\n[4/4] Storing vectors in ChromaDB...")

        documents = [chunk["content"] for chunk in processed_chunks]
        ids = [chunk["id"] for chunk in processed_chunks]

        metadatas = [
            {
                "file": chunk["file"],
                "start_line": chunk["start_line"],
                "end_line": chunk["end_line"],
                "language": chunk.get("language", "unknown"),
                "code": chunk["code"],
                "description": chunk["description"],
                # include original ast-grep rule id and the derived kind
                "ruleId": chunk.get("ruleId", ""),
                "kind": chunk.get("kind", "unknown"),
            }
            for chunk in processed_chunks
        ]

        self.collection.add(
            embeddings=embeddings,
            documents=documents,
            ids=ids,
            metadatas=metadatas
        )

        log(f"✓ Stored {len(processed_chunks)} chunks in ChromaDB")

    def search(self, query: str, embedder: Any, num_results: int = 3, filter_type: Optional[str] = None) -> Dict:
        """Search the ChromaDB collection.

        Args:
            query: The search query string
            embedder: Embedding generator with .encode() method
            num_results: Number of results to return
            filter_type: Optional filter - "proofs", "specs", or None for all
        """
        query_embedding = embedder.encode([query])

        # Build where clause for filtering by type
        where_clause = None
        if filter_type and filter_type.lower() == "proofs":
            where_clause = {"kind": "proof"}
        elif filter_type and filter_type.lower() == "specs":
            where_clause = {"kind": "spec"}

        results = self.collection.query(
            query_embeddings=query_embedding,
            n_results=num_results,
            where=where_clause
        )

        return results



class SemanticGrep:
    """Main semantic grep tool combining all components."""

    def __init__(self, config: SemanticGrepConfig):
        self.config = config
        self.chunker = AstGrepChunker(config)
        self.description_gen = DescriptionGenerator(skip=config.skip_descriptions)
        self.embedding_gen = EmbeddingGenerator(config.embedding_model)
        self.db_manager = ChromaDBManager(config.db_path, config.collection_name)

    def index(self):
        """Index a repository."""
        log("\n" + "="*60 + "")
        log("Semantic Grep Indexing")
        log(f"Repository: {self.config.repo_path}")
        log(f"Database: {self.config.db_path}")
        log("" + "="*60 + "")

        try:
            self.config.validate()

            # Step 1: Extract chunks using ast-grep
            chunks = self.chunker.run()
            if not chunks:
                log("Warning: No chunks extracted")
                return
            
            # Step 2: Process chunks first to classify them by kind (spec vs proof)
            processed_chunks = self._process_chunks(chunks)

            # Step 3: Generate descriptions based on chunk kind
            if not self.config.skip_descriptions and self.description_gen.api_key:
                log("\nGenerating natural language descriptions...")
                descriptions = asyncio.run(self.description_gen.generate_batch(processed_chunks))
                # Fill in the descriptions in processed chunks
                for i, desc in enumerate(descriptions):
                    processed_chunks[i]["description"] = desc
            else:
                for chunk in processed_chunks:
                    chunk["description"] = "[Skipped]"

            # Update content field to embed ONLY the natural language description
            # This ensures plan-to-plan semantic matching without code token dilution
            for chunk in processed_chunks:
                chunk["content"] = chunk["description"]

            # Save processed chunks
            with open(self.config.processed_chunks_file, "w") as f:
                json.dump(processed_chunks, f, indent=2)

            # Step 4: Generate embeddings
            documents = [chunk["content"] for chunk in processed_chunks]
            embeddings = self.embedding_gen.encode(documents)

            # Step 5: Store in ChromaDB
            self.db_manager.initialize(recreate=True)
            self.db_manager.store_chunks(processed_chunks, embeddings)

            log("\n" + "="*60 + "")
            log("✓ Indexing complete!")
            log(f"Database location: {self.config.db_path}")
            log("" + "="*60 + "\n")

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
                "content": code_text,  # Will be combined with description later
                "code": code_text,
                "description": "",  # Placeholder, will be filled by generate_batch or set to "[Skipped]"
                # preserve ast-grep rule id and add a simple classification
                "ruleId": chunk.get("ruleId", ""),
                "kind": (
                    "spec" if chunk.get("ruleId", "").startswith("capture-spec")
                    else "proof" if (chunk.get("ruleId", "").startswith("capture-proof")
                                      or chunk.get("ruleId", "") == "capture-asserts")
                    else "unknown"
                ),
                "file": file_path,
                "language": chunk.get("language", "unknown"),
                "start_line": start_line,
                "end_line": end_line
            })

        return processed

    def search(self, query: str, num_results: int = 3, filter_type: Optional[str] = None, text_output: bool = False):
        """Search for a query.

        Args:
            query: The search query string
            num_results: Number of results to return
            filter_type: Optional filter - "proofs", "specs", or None for all
            text_output: If True, output results as formatted text instead of JSON
        """
        try:
            # Initialize and load DB
            self.db_manager.initialize()

            if self.db_manager.collection.count() == 0:
                log("Error: Database is empty. Run --index first.")
                sys.exit(1)

            # Perform search with optional type filter
            results = self.db_manager.search(query, self.embedding_gen, num_results, filter_type)

            # Display results
            if text_output:
                self._display_results(query, results, filter_type)
            else:
                self._display_results_json(query, results, filter_type)

        except Exception as e:
            log(f"Error during search: {e}")
            sys.exit(1)

    def _display_results(self, query: str, results: Dict, filter_type: Optional[str] = None):
        """Display search results in a formatted table.

        Args:
            query: The search query that was executed
            results: Results from ChromaDB search
            filter_type: Optional type filter that was applied
        """
        filter_display = f" (type: {filter_type})" if filter_type else ""
        print(f"\n=== Search Results for: '{query}'{filter_display} ===\n")

        docs = results.get('documents', [[]])[0]
        ids = results.get('ids', [[]])[0]
        metadatas = results.get('metadatas', [[]])[0]
        distances = results.get('distances', [[0] * len(docs)])[0]

        if not docs:
            print("No results found.\n")
            return

        for i, (doc_id, metadata, distance) in enumerate(zip(ids, metadatas, distances)):
            similarity = 1 - (distance / 2)  # Convert distance to similarity

            print(f">> Match {i+1} | {doc_id} | Similarity: {similarity:.2%}")
            print(f"   File: {metadata.get('file')} (lines {metadata.get('start_line')}-{metadata.get('end_line')})")
            print(f"   Description: {metadata.get('description')}")

            code = metadata.get('code', '')
            code_lines = code.split('\n')[:5]  # Show first 5 lines
            code_preview = '\n'.join(f"    {line}" for line in code_lines)
            print(f"\n{code_preview}")

            if len(code.split('\n')) > 5:
                print(f"    ... ({len(code.split(chr(10)))} lines total)")

            print()

    def _display_results_json(self, query: str, results: Dict, filter_type: Optional[str] = None):
        """Display search results in JSON format for agent consumption.

        Args:
            query: The search query that was executed
            results: Results from ChromaDB search
            filter_type: Optional type filter that was applied
        """
        docs = results.get('documents', [[]])[0]
        ids = results.get('ids', [[]])[0]
        metadatas = results.get('metadatas', [[]])[0]
        distances = results.get('distances', [[0] * len(docs)])[0]

        result_list = []
        for i, (doc_id, metadata, distance) in enumerate(zip(ids, metadatas, distances)):
            similarity = 1 - (distance / 2)  # Convert distance to similarity

            result_list.append({
                "id": doc_id,
                "similarity": round(similarity, 4),
                "file": metadata.get('file'),
                "start_line": metadata.get('start_line'),
                "end_line": metadata.get('end_line'),
                "description": metadata.get('description'),
                "code": metadata.get('code'),
                "kind": metadata.get('kind')
            })

        output = {
            "query": query,
            "filter_type": filter_type,
            "num_results": len(result_list),
            "results": result_list
        }

        print(json.dumps(output, indent=2))


def main():
    parser = argparse.ArgumentParser(
        description="Unified Semantic Grep: Index code and search with natural language",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Index current directory
  python semantic_grep_unified.py --index

  # Index specific repository
  python semantic_grep_unified.py --index --repo-path /path/to/repo

  # Search (outputs JSON by default)
  python semantic_grep_unified.py --search "proof of memory safety"

  # Search with formatted text output
  python semantic_grep_unified.py --search "memory safety" --text

  # Search for only proofs
  python semantic_grep_unified.py --search "proof of memory safety" --type proofs

  # Search for only specs
  python semantic_grep_unified.py --search "invariant" --type specs
        """
    )

    parser.add_argument("--index", action="store_true", help="Index a repository")
    parser.add_argument("--search", metavar="QUERY",
                        help="Search for a query")
    parser.add_argument("--repo-path", default=".", help="Path to repository (default: current directory)")
    parser.add_argument("--db-path", help="Path to ChromaDB database (default: <repo-path>/.semantic_grep_db)")
    parser.add_argument("--patterns", help="Path to ast-grep patterns file (auto-detected if not provided)")
    parser.add_argument("--num-results", type=int, default=10, help="Number of results to return (default: 10)")
    parser.add_argument("--type", choices=["proofs", "specs"],
                        help="Filter results by type: 'proofs' or 'specs' (default: all)")
    parser.add_argument("--tree-sitter-verus-path", required=True,
                        help="Path to the Verus tree-sitter shared library (.so / .dylib)")
    parser.add_argument("--skip-descriptions", action="store_true",
                        help="Skip LLM description generation (faster indexing)")
    parser.add_argument("--text", action="store_true",
                        help="Output search results as formatted text instead of JSON")

    args = parser.parse_args()

    if not args.index and not args.search:
        parser.print_help()
        sys.exit(0)

    try:
        # Create configuration
        config = SemanticGrepConfig(
            repo_path=args.repo_path,
            db_path=args.db_path,
            patterns_file=args.patterns,
            skip_descriptions=args.skip_descriptions,
            tree_sitter_verus_path=args.tree_sitter_verus_path,
        )

        # Create semantic grep instance
        sg = SemanticGrep(config)

        if args.index:
            sg.index()

        elif args.search:
            sg.search(args.search, args.num_results, args.type, args.text)

    except KeyboardInterrupt:
        log("\nInterrupted by user")
        sys.exit(0)
    except Exception as e:
        log(f"Fatal error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
