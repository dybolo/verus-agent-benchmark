#!/usr/bin/env python3
# pyright: basic

import argparse
import dataclasses
import fnmatch
import glob
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone

from stats_protocol import StatsFn


def build_base_image():
    """Build the base Docker image with all shared dependencies."""
    print("=" * 60)
    print("Building base image: benchmark-base:latest")
    print("=" * 60)
    subprocess.run(
        ["docker", "build", "-t", "benchmark-base:latest", "-f", "Dockerfile", "."],
        check=True,
    )
    print()


print_lock = threading.Lock()

FINAL_TASK_STATUSES = {"completed"}
RATE_LIMIT_PATTERNS = (
    r"rate[ -]?limit",
    r"usage[ -]?limit",
    r"too many requests",
    r"quota (?:has been )?exceeded",
    r"insufficient_quota",
    r"resource_exhausted",
)


def safe_print(*args, **kwargs):
    with print_lock:
        print(*args, **kwargs)


def is_rate_limited(output: str) -> bool:
    """Return whether an agent's output indicates an exhausted provider allowance."""
    return any(
        re.search(pattern, output, re.IGNORECASE) for pattern in RATE_LIMIT_PATTERNS
    )


def write_run_stats(stats_file: str, run_stats: dict) -> None:
    """Write the current state of a benchmark run."""
    os.makedirs(os.path.dirname(stats_file), exist_ok=True)
    with open(stats_file, "w") as f:
        json.dump(run_stats, f, indent=2)
        f.write("\n")


def tasks_to_run(task_stats: dict) -> list[str]:
    """Select unfinished tasks; timeouts and completed attempts are final."""
    return [
        task
        for task, stats in task_stats.items()
        if stats.get("status", "pending") not in FINAL_TASK_STATUSES
    ]


def build_agent_image(agent_tag, agent_path):
    """Build a specific agent's Docker image."""
    print(f"Building agent image: benchmark-{agent_tag}")
    subprocess.run(
        ["docker", "build", "-t", f"benchmark-{agent_tag}", agent_path], check=True
    )
    print()


def verify_solution(
    staging_dir, task, solution_filename, original_task_path, staged_task_path
) -> dict:
    """Run Verus and Lynette checks on the generated solution using a single persistent container."""
    stats = {"verus_passed": False, "cheat_checker_passed": False}

    container_name = f"verify_{uuid.uuid4().hex[:8]}"

    try:
        safe_print(f"Starting verification container {container_name}...")
        # Start the container in detached mode running sleep infinity
        subprocess.run(
            [
                "docker",
                "run",
                "-d",
                "--rm",
                "--name",
                container_name,
                "-v",
                f"{staging_dir}:/workspace/task_env",
                "benchmark-base:latest",
                "sleep",
                "infinity",
            ],
            check=True,
            capture_output=True,
        )

        safe_print("Running Verus verification...")
        verus_cmd = [
            "docker",
            "exec",
            container_name,
            "verus",
            f"/workspace/task_env/{solution_filename}",
            "--output-json",
        ]
        verus_res = subprocess.run(
            verus_cmd, capture_output=True, text=True, check=False
        )

        # We should try to find the JSON string in stdout since verus might output other lines
        try:
            verus_data = json.loads(verus_res.stdout)
            stats["verus_passed"] = verus_data.get("verification-results", {}).get(
                "success", False
            )
        except json.JSONDecodeError:
            # Attempt to find json inside stdout if there's surrounding text
            try:
                json_start = verus_res.stdout.find("{")
                json_end = verus_res.stdout.rfind("}")
                if json_start != -1 and json_end != -1:
                    verus_data = json.loads(verus_res.stdout[json_start : json_end + 1])
                    stats["verus_passed"] = verus_data.get(
                        "verification-results", {}
                    ).get("success", False)
                else:
                    stats["verus_passed"] = False
            except (TypeError, ValueError) as e:
                stats["verus_passed"] = False
                safe_print(f"Caught error while analysing Verus output: {e}")

        safe_print(f"Verus passed: {stats['verus_passed']}")

        # clear original file in case agent has modify it to check changes with cheat checker
        try:
            os.remove(staged_task_path)
        except FileNotFoundError:
            pass
        shutil.copy2(original_task_path, staged_task_path)

        # Run Lynette Cheat Checker validation
        safe_print("Running Lynette cheat checker...")
        lynette_cmd = [
            "docker",
            "exec",
            container_name,
            "python3",
            "/opt/lynette.py",
            f"/workspace/task_env/{task}",
            f"/workspace/task_env/{solution_filename}",
        ]
        lynette_res = subprocess.run(
            lynette_cmd, capture_output=True, text=True, check=False
        )
        stats["cheat_checker_passed"] = lynette_res.returncode == 0

        safe_print(f"Cheat checker passed: {stats['cheat_checker_passed']}")

    finally:
        safe_print(f"Cleaning up verification container {container_name}...")
        subprocess.run(
            ["docker", "kill", container_name], capture_output=True, check=False
        )

    return stats


def compute_session_statistics(agent_name, session_path) -> dict:
    """Import the agent's statistics module and call compute_statistics directly."""
    agent_dir = agent_name.split("/")[0]
    stats_script = os.path.join("agents", agent_dir, "statistics.py")
    if not os.path.exists(stats_script):
        safe_print(f"  (no statistics.py found for agent '{agent_dir}')")
        return {}

    spec = importlib.util.spec_from_file_location(
        f"agents_{agent_dir}_statistics", stats_script
    )
    if spec is None or spec.loader is None:
        safe_print(f"  (could not load statistics.py for agent '{agent_dir}')")
        return {}

    mod = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(mod)
        fn = mod.compute_statistics
        if not isinstance(fn, StatsFn):
            safe_print(
                f"⚠ Agent '{agent_dir}' does not conform to the StatsFn protocol"
            )
            return {}
        stats = fn(session_path)
        safe_print("✓ Session statistics recorded")
        return dataclasses.asdict(stats)
    except Exception as e:  # noqa: BLE001 - third-party statistics modules may raise arbitrary errors
        safe_print(f"⚠ Could not compute statistics: {e}")
        return {}


def extract_solution_file(
    staging_dir, solution_filename, agent_name, timestamp
) -> dict:
    """Extract the solution file from the staging directory to the permanent solutions folder."""
    expected_solution_path = os.path.join(staging_dir, solution_filename)
    if os.path.exists(expected_solution_path):
        final_solution_dir = os.path.abspath(
            os.path.join("solutions", agent_name, f"{timestamp}")
        )
        os.makedirs(final_solution_dir, exist_ok=True)
        final_solution_path = os.path.join(final_solution_dir, solution_filename)
        shutil.copy2(expected_solution_path, final_solution_path)
        safe_print(f"✓ Solution extracted to {final_solution_path}")
        return {"solution_file": os.path.relpath(final_solution_path)}
    else:
        safe_print(f"✗ Agent did not produce the expected file: {solution_filename}")
        return {"solution_file": None}


def run_single_job(
    agent_name,
    agent_tag,
    agent_dir,
    entrypoint,
    task,
    timestamp,
    prompt_template,
    staging_base,
) -> dict:
    """Run a single agent on a single task and return its stats."""
    task_base = task.removesuffix(".rs")
    solution_filename = f"{task_base}_verified.rs"

    task_stats = {
        "verus_passed": False,
        "cheat_checker_passed": False,
        "timed_out": False,
        "status": "pending",
    }

    with tempfile.TemporaryDirectory(dir=staging_base) as staging_dir:
        original_task_path = os.path.abspath(os.path.join("tasks", task))
        staged_task_path = os.path.join(staging_dir, task)
        shutil.copy2(original_task_path, staged_task_path)

        session_dir_staging = os.path.join(staging_dir, "session")
        os.makedirs(session_dir_staging)

        entrypoint_path = os.path.join(os.path.abspath("agents"), agent_dir, entrypoint)
        shutil.copy2(entrypoint_path, os.path.join(staging_dir, entrypoint))
        os.chmod(os.path.join(staging_dir, entrypoint), 0o755)

        task_path_in_container = f"/workspace/task_env/{task}"
        output_path_in_container = f"/workspace/task_env/{solution_filename}"
        session_path_in_container = "/workspace/task_env/session"
        formatted_prompt = prompt_template.format(
            task=task_path_in_container, output=output_path_in_container
        )

        container_name = f"agent_{uuid.uuid4().hex[:8]}"
        cmd = [
            "docker",
            "run",
            "--rm",
            "--name",
            container_name,
            "--user",
            f"{os.getuid()}:{os.getgid()}",
            "-e",
            "HOME=/root",
            "-v",
            f"{staging_dir}:/workspace/task_env",
            "-e",
            "TASK_PROMPT",
            "-e",
            "SESSION",
        ]

        for key in [
            "ANTHROPIC_API_KEY",
            "OPENAI_API_KEY",
            "GEMINI_API_KEY",
            "OPENCODE_API_KEY",
            "OPENROUTER_API_KEY",
            "AWS_BEARER_TOKEN_BEDROCK",
        ]:
            if key in os.environ:
                cmd.extend(["-e", key])

        cmd.extend(
            [
                "--entrypoint",
                f"/workspace/task_env/{entrypoint}",
                f"benchmark-{agent_tag}",
            ]
        )

        env = os.environ.copy()
        env["TASK_PROMPT"] = formatted_prompt
        env["SESSION"] = session_path_in_container

        try:
            result = subprocess.run(
                cmd, env=env, check=False, capture_output=True, text=True, timeout=1200
            )

            if result.stdout:
                safe_print("[STDOUT]")
                safe_print(result.stdout)
            if result.stderr:
                safe_print("[STDERR]")
                safe_print(result.stderr)

            if is_rate_limited(f"{result.stdout}\n{result.stderr}"):
                safe_print(
                    f"⚠ Agent {agent_name} hit a usage/rate limit on task {task}; leaving it pending for --resume"
                )
                return {task: task_stats}
            if result.returncode != 0:
                safe_print(
                    f"⚠ Agent {agent_name} exited with code {result.returncode} on task {task}"
                )
            task_stats["status"] = "completed"

        except subprocess.TimeoutExpired:
            task_stats["timed_out"] = True
            task_stats["status"] = "completed"
            safe_print(f"✗ Agent {agent_name} timed out on task {task} (20 minutes)")
            subprocess.run(
                ["docker", "stop", container_name], capture_output=True, check=False
            )

        except subprocess.CalledProcessError as e:
            safe_print(f"✗ Agent {agent_name} failed on task {task}: {e}")
            return {task: task_stats}

        extracted = extract_solution_file(
            staging_dir, solution_filename, agent_name, timestamp
        )
        task_stats.update(extracted)
        if extracted["solution_file"]:
            verification_status = verify_solution(
                staging_dir,
                task,
                solution_filename,
                original_task_path,
                staged_task_path,
            )
            task_stats.update(verification_status)

        session_dir_path = os.path.abspath(
            os.path.join("sessions", agent_name, f"{timestamp}", task_base)
        )
        try:
            shutil.copytree(session_dir_staging, session_dir_path)
            session_stats = compute_session_statistics(agent_name, session_dir_path)
            task_stats.update(session_stats)
        except Exception as e:  # noqa: BLE001 - session capture must not discard task results
            safe_print(f"Failed to capture statistics for the agent: {e}")

    return {task: task_stats}


def discover_agents(agent_filter=None, model_filter=None):
    """Discover selected entrypoints without performing Docker builds."""
    agents = []
    if os.path.exists("agents"):
        for agent_dir in sorted(os.listdir("agents")):
            agent_path = os.path.join("agents", agent_dir)
            if not os.path.isdir(agent_path):
                continue
            if not os.path.exists(os.path.join(agent_path, "Dockerfile")):
                continue
            if agent_filter and not fnmatch.fnmatch(agent_dir, agent_filter):
                continue
            for model_file in sorted(glob.glob(os.path.join(agent_path, "*.model"))):
                model_name = os.path.basename(model_file)
                name_no_ext = os.path.splitext(model_name)[0]
                if model_filter and not fnmatch.fnmatch(name_no_ext, model_filter):
                    continue
                agents.append(
                    {
                        "name": f"{agent_dir}/{name_no_ext}",
                        "tag": agent_dir,
                        "entrypoint": model_name,
                        "agent_dir": agent_dir,
                    }
                )
    return agents


def start_new_run(agent_filter=None, model_filter=None):
    """Create a run file with every selected task marked pending."""
    tasks = sorted(f for f in os.listdir("tasks") if f.endswith(".rs"))
    agents = discover_agents(agent_filter, model_filter)
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    stats_file = os.path.join("runs", f"{timestamp}.json")
    run_stats = {
        "timestamp": timestamp,
        "configuration": {"agents": agents, "tasks": tasks},
        "agents": {
            agent["name"]: {"tasks": {task: {"status": "pending"} for task in tasks}}
            for agent in agents
        },
    }
    write_run_stats(stats_file, run_stats)
    return stats_file, run_stats, tasks, agents


def resume_run(run_id, agent_filter=None, model_filter=None):
    """Load a prior run and return its original agents and pending task states."""
    run_id = os.path.basename(run_id)
    run_id = run_id.removesuffix(".json")
    if not run_id or run_id in {".", ".."}:
        raise ValueError("--resume must be a run ID, not a path")
    stats_file = os.path.join("runs", f"{run_id}.json")
    try:
        with open(stats_file) as f:
            run_stats = json.load(f)
    except FileNotFoundError as e:
        raise ValueError(f"Run file not found: {stats_file}") from e
    if "configuration" not in run_stats or "agents" not in run_stats:
        raise ValueError("Run file predates resumable runs and cannot be resumed")

    tasks = run_stats["configuration"]["tasks"]
    agents = run_stats["configuration"]["agents"]
    available_agents = {agent["name"] for agent in discover_agents()}
    missing_agents = [
        agent["name"] for agent in agents if agent["name"] not in available_agents
    ]
    if missing_agents:
        raise ValueError(
            f"Cannot resume: configured agent entrypoints are missing: {', '.join(missing_agents)}"
        )
    if agent_filter and any(
        not fnmatch.fnmatch(agent["agent_dir"], agent_filter) for agent in agents
    ):
        raise ValueError("--agent filter does not match every agent in the run file")
    if model_filter and any(
        not fnmatch.fnmatch(os.path.splitext(agent["entrypoint"])[0], model_filter)
        for agent in agents
    ):
        raise ValueError("--model filter does not match every model in the run file")

    return stats_file, run_stats, tasks, agents


def run_tasks(max_workers, agent_filter=None, model_filter=None, resume_id=None):
    """Run a new benchmark or resume only the pending tasks from an existing run."""
    if resume_id:
        stats_file, run_stats, tasks, agents = resume_run(
            resume_id, agent_filter, model_filter
        )
    else:
        stats_file, run_stats, tasks, agents = start_new_run(agent_filter, model_filter)
    timestamp = run_stats["timestamp"]

    if not agents:
        print("Error: No agents found in agents/ directory")
        sys.exit(1)
    if not tasks:
        print("Error: No tasks found in tasks/ directory")
        sys.exit(1)

    print(f"Found {len(agents)} agent(s): {', '.join(a['name'] for a in agents)}")
    print(f"Found {len(tasks)} task(s)")
    print()

    build_base_image()
    for agent_dir in sorted({agent["agent_dir"] for agent in agents}):
        build_agent_image(agent_dir, os.path.join("agents", agent_dir))
    with open("prompt.txt", "r") as f:
        prompt_template = f.read()

    max_workers = min(max_workers, len(tasks))
    staging_base = os.path.abspath(".staging_areas")
    os.makedirs(staging_base, exist_ok=True)

    for agent in agents:
        agent_name = agent["name"]
        pending_tasks = tasks_to_run(run_stats["agents"][agent_name]["tasks"])
        if not pending_tasks:
            print(f"No unfinished tasks for agent '{agent_name}'.")
            continue
        print(
            f"Submitting {len(pending_tasks)} tasks for agent '{agent_name}' to thread pool ({max_workers} workers)..."
        )
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {
                executor.submit(
                    run_single_job,
                    agent_name,
                    agent["tag"],
                    agent["agent_dir"],
                    agent["entrypoint"],
                    task,
                    timestamp,
                    prompt_template,
                    staging_base,
                ): task
                for task in pending_tasks
            }
            for future in as_completed(futures):
                task = futures[future]
                try:
                    run_stats["agents"][agent_name]["tasks"].update(future.result())
                except Exception as e:  # noqa: BLE001 - preserve the remaining tasks after a worker crash
                    safe_print(f"✗ Task {task} crashed before completion: {e}")
                    run_stats["agents"][agent_name]["tasks"][task] = {
                        "status": "pending",
                        "error": str(e),
                    }
                write_run_stats(stats_file, run_stats)

    has_pending = any(
        tasks_to_run(agent_stats["tasks"])
        for agent_stats in run_stats["agents"].values()
    )
    if has_pending:
        print(
            f"Benchmark paused. Resume with: python3 benchmark.py --resume {timestamp}"
        )
        return

    print("=" * 60)
    print(f"Benchmark complete. Run statistics saved to {stats_file}")
    print("=" * 60)

    subprocess.run(
        [
            "git",
            "add",
            f"solutions/**/{timestamp}/**",
            f"sessions/**/{timestamp}/**",
            f"runs/{timestamp}.json",
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    result = subprocess.run(
        ["git", "commit", "-m", f"run {timestamp}"],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode == 0:
        print(f"✓ Committed run artifacts: 'run {timestamp}'")
    else:
        print(f"⚠ Git commit skipped: {result.stderr.strip()}")


def main():
    parser = argparse.ArgumentParser(description="Run benchmarks")
    parser.add_argument(
        "--parallel",
        "-j",
        type=int,
        default=os.cpu_count() or 4,
        help="Max parallel tasks (default: CPU count)",
    )
    parser.add_argument(
        "--agent",
        "-a",
        help="Glob filter for agent directory name (e.g. 'opencode', 'open*')",
    )
    parser.add_argument(
        "--model", "-m", help="Glob filter for model name (e.g. 'gpt-5.4', '*gpt*')"
    )
    parser.add_argument(
        "--resume",
        metavar="RUN_ID",
        help="Resume pending tasks from runs/<RUN_ID>.json",
    )
    args = parser.parse_args()
    try:
        run_tasks(
            max_workers=args.parallel,
            agent_filter=args.agent,
            model_filter=args.model,
            resume_id=args.resume,
        )
    except ValueError as e:
        parser.error(str(e))


if __name__ == "__main__":
    main()
