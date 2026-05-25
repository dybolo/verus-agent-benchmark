import os
import sys
import argparse
import re
import subprocess
from pathlib import Path
import tempfile
import logging

logger = logging.getLogger(__name__)

class Lynette:
    lynette_path = Path(__file__).resolve().parent/ "lynette" / "source"
    meta_command = ["cargo", "run", "--manifest-path", lynette_path / "Cargo.toml", "--"]
    env = os.environ.copy()
    env["RUSTFLAGS"] = "-Awarnings"

    # Run a command
    # @command: a list of lynette commands arguemnts, e.g. ["compare", "foo.rs", "bar.rs"]
    # @return: a CompletedProcess object(returned by subprocess.run(...))
    def run(self, command):
        command = self.meta_command + command
        return subprocess.run(command, env=self.env, capture_output=True, text=True)

    def code_unimpl(self, file):
        return self.run(["code", "unimpl", file])

    def func_add(self, file1, file2, replace=False, funcs=None):
        if funcs is None:
            funcs = []
        return self.run(
            ["func", "add", file1, file2, "--replace" if replace else ""] + ["--funcs"] + funcs
            if funcs
            else []
        )

    def code_merge(self, file1, file2, merge_mode):
        pass

    def code_merge_all(self, file1, file2):
        return self.run(["code", "merge", "--all", file1, file2])

    def code_merge_invariant(self, file1, file2):
        return self.run(["code", "merge", "--invariants", file1, file2])

    def code_detect_nonlinear(self, file):
        return self.run(["code", "detect-nl", file])

    def code_get_ghost(self, file):
        """Get all ghost code in a verus source code file.

        Returns a CompletedProcess with output format:
        <type>:((<start_line>, <start_column>), (<end_line>, <end_column>))
        """
        return self.run(["code", "get-ghost", file])

    def get_assertions(self, file):
        """Get assertion statements with their line numbers.

        Args:
            file: Path to the Verus source file

        Returns:
            List of dictionaries with assertion information:
            [
                {
                    'type': 'assert' or 'assert_forall',
                    'start_line': int,
                    'start_column': int,
                    'end_line': int,
                    'end_column': int
                },
                ...
            ]
        """
        result = self.code_get_ghost(file)
        if result.returncode != 0:
            return []

        assertions = []
        # Parse output lines like: assert:((32, 20), (32, 42))
        pattern = r"^(assert|assert_forall):\(\((\d+), (\d+)\), \((\d+), (\d+)\)\)$"

        for line in result.stdout.strip().split("\n"):
            if not line:
                continue
            match = re.match(pattern, line)
            if match:
                assertions.append(
                    {
                        "type": match.group(1),
                        "start_line": int(match.group(2)),
                        "start_column": int(match.group(3)),
                        "end_line": int(match.group(4)),
                        "end_column": int(match.group(5)),
                    }
                )

        return assertions

    def get_all_ghost_code(self, file):
        """Get all ghost code with their line numbers.

        Args:
            file: Path to the Verus source file

        Returns:
            List of dictionaries with ghost code information:
            [
                {
                    'type': str (e.g., 'assert', 'requires', 'ensures', etc.),
                    'start_line': int,
                    'start_column': int,
                    'end_line': int,
                    'end_column': int
                },
                ...
            ]
        """
        result = self.code_get_ghost(file)
        if result.returncode != 0:
            return []

        ghost_items = []
        # Parse output lines like: <type>:((<start_line>, <start_column>), (<end_line>, <end_column>))
        pattern = r"^([^:]+):\(\((\d+), (\d+)\), \((\d+), (\d+)\)\)$"

        for line in result.stdout.strip().split("\n"):
            if not line:
                continue
            match = re.match(pattern, line)
            if match:
                ghost_items.append(
                    {
                        "type": match.group(1),
                        "start_line": int(match.group(2)),
                        "start_column": int(match.group(3)),
                        "end_line": int(match.group(4)),
                        "end_column": int(match.group(5)),
                    }
                )

        return ghost_items


    def proof_completion_code_change_is_safe(
        self,
        origin: str,
        changed: str,
    ) -> bool:
        """
        Check if code changes are safe for proof completion.

        Ensures that no admit(), assume(), or verifier attributes are added/removed.
        Uses Lynette to verify changes don't violate safety rules.

        Args:
            origin: Original source code
            changed: Modified source code

        Returns:
            True if changes are safe, False otherwise
        """
        # Check the number of admit(), assume(, #[verifier::external_body]
        # They should not be increased
        if origin.count("admit()") != changed.count("admit()"):
            logger.error("admit() calls have been added or removed")
            return False
        if origin.count("assume(") != changed.count("assume("):
            logger.error("assume(...) calls have been added or removed")
            return False
        if origin.count("#[verifier::external_body]") != changed.count("#[verifier::external_body]"):
            logger.error("#[verifier::external_body] annotations have been added or removed")
            return False
        if origin.count("#[verifier::admit]") != changed.count("#[verifier::admit]"):
            logger.error("#[verifier::admit] annotations have been added or removed")
            return False

        with (
            tempfile.NamedTemporaryFile(mode="w", prefix="llm4v_orig", suffix=".rs", encoding="utf-8") as orig_f,
            tempfile.NamedTemporaryFile(mode="w", prefix="llm4v_changed", suffix=".rs", encoding="utf-8") as changed_f,
        ):
            orig_f.write(origin)
            orig_f.flush()
            changed_f.write(changed)
            changed_f.flush()

            m = self.run(["additions", orig_f.name, changed_f.name])

            if m.returncode == 0:
                return True
            elif m.returncode == 1:
                err_m = m.stdout.strip()
                # lynette safety check could output more information than just `Disallowed changes detected'
                if "Disallowed changes detected" in err_m:
                    logger.error("Disallowed changes detected by lynette")
                    return False
                else:
                    logger.error("Unknown errors during lynette safety check")
                    return False
            else:
                err_m = m.stderr.strip()
                logger.error("Unknown errors during lynette safety check")
                logger.error(f"{err_m}")
                if "unwrap()" in err_m:
                    return False
        return False


def main():
    parser = argparse.ArgumentParser(description="Check if code changes are safe for proof completion.")
    parser.add_argument("origin_file", help="Path to the original source file")
    parser.add_argument("changed_file", help="Path to the modified source file")
    args = parser.parse_args()

    try:
        with open(args.origin_file, 'r', encoding='utf-8') as f:
            origin_content = f.read()
        with open(args.changed_file, 'r', encoding='utf-8') as f:
            changed_content = f.read()
    except FileNotFoundError as e:
        logger.error(f"Error reading files: {e}")
        sys.exit(1)

    lynette = Lynette()

    is_safe = lynette.proof_completion_code_change_is_safe(
        origin=origin_content,
        changed=changed_content
    )

    if is_safe:
        print("Changes are safe.")
        sys.exit(0)
    else:
        print("Changes are NOT safe.")
        sys.exit(1)


if __name__ == "__main__":
    main()
