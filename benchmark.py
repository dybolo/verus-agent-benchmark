#!/usr/bin/env python3
# pyright: basic

from __future__ import annotations

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
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Any

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
SESSION_ERROR_PATTERNS = (r'"stopReason"\s*:\s*"error"',)


@dataclass(frozen=True)
class AgentSpec:
    """The agent image and entrypoint used for one benchmark condition."""

    name: str
    tag: str
    agent_dir: str
    entrypoint: str

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> AgentSpec:
        return cls(
            name=str(data["name"]),
            tag=str(data["tag"]),
            agent_dir=str(data["agent_dir"]),
            entrypoint=str(data["entrypoint"]),
        )

    def to_dict(self) -> dict[str, str]:
        return {
            "name": self.name,
            "tag": self.tag,
            "agent_dir": self.agent_dir,
            "entrypoint": self.entrypoint,
        }


@dataclass
class Task:
    """The persisted state and result fields for one benchmark task."""

    name: str
    status: str = "pending"
    verus_passed: bool = False
    cheat_checker_passed: bool = False
    timed_out: bool = False
    solution_file: str | None = None
    extra_stats: dict[str, Any] = field(default_factory=dict)

    @property
    def is_pending(self) -> bool:
        return self.status not in FINAL_TASK_STATUSES

    def update_from_stats(self, stats: dict[str, Any]) -> None:
        self.status = str(stats.pop("status", self.status))
        self.verus_passed = bool(stats.pop("verus_passed", self.verus_passed))
        self.cheat_checker_passed = bool(
            stats.pop("cheat_checker_passed", self.cheat_checker_passed)
        )
        self.timed_out = bool(stats.pop("timed_out", self.timed_out))
        self.solution_file = stats.pop("solution_file", self.solution_file)
        self.extra_stats.update(stats)

    @classmethod
    def from_dict(cls, name: str, data: dict[str, Any]) -> Task:
        data = data.copy()
        # Historical run files predate task status; their recorded result is final.
        status = str(data.pop("status", "completed"))
        return cls(
            name=name,
            status=status,
            verus_passed=bool(data.pop("verus_passed", False)),
            cheat_checker_passed=bool(data.pop("cheat_checker_passed", False)),
            timed_out=bool(data.pop("timed_out", False)),
            solution_file=data.pop("solution_file", None),
            extra_stats=data,
        )

    def to_dict(self) -> dict[str, Any]:
        if self.is_pending and not self.extra_stats:
            return {"status": self.status}
        result = {
            "verus_passed": self.verus_passed,
            "cheat_checker_passed": self.cheat_checker_passed,
            "timed_out": self.timed_out,
            "status": self.status,
            "solution_file": self.solution_file,
        }
        result.update(self.extra_stats)
        return result


@dataclass
class Run:
    """A benchmark run and all agent-specific task results persisted to JSON."""

    timestamp: str
    stats_file: str
    agents: list[AgentSpec]
    task_names: list[str]
    tasks_by_agent: dict[str, dict[str, Task]]

    @classmethod
    def create(cls, agents: list[AgentSpec], task_names: list[str]) -> Run:
        timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
        return cls(
            timestamp=timestamp,
            stats_file=os.path.join("runs", f"{timestamp}.json"),
            agents=agents,
            task_names=task_names,
            tasks_by_agent={
                agent.name: {name: Task(name) for name in task_names}
                for agent in agents
            },
        )

    @classmethod
    def from_dict(cls, data: dict[str, Any], stats_file: str) -> Run:
        configuration = data["configuration"]
        agents = [AgentSpec.from_dict(agent) for agent in configuration["agents"]]
        return cls(
            timestamp=str(data["timestamp"]),
            stats_file=stats_file,
            agents=agents,
            task_names=[str(name) for name in configuration["tasks"]],
            tasks_by_agent={
                agent_name: {
                    name: Task.from_dict(name, stats)
                    for name, stats in agent_data["tasks"].items()
                }
                for agent_name, agent_data in data["agents"].items()
            },
        )

    def pending_tasks(self, agent: AgentSpec) -> list[Task]:
        return [
            task for task in self.tasks_by_agent[agent.name].values() if task.is_pending
        ]

    def has_pending_tasks(self) -> bool:
        return any(
            task.is_pending
            for tasks in self.tasks_by_agent.values()
            for task in tasks.values()
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "timestamp": self.timestamp,
            "configuration": {
                "agents": [agent.to_dict() for agent in self.agents],
                "tasks": self.task_names,
            },
            "agents": {
                agent.name: {
                    "tasks": {
                        task.name: task.to_dict()
                        for task in self.tasks_by_agent[agent.name].values()
                    }
                }
                for agent in self.agents
            },
        }

    def save(self) -> None:
        """Write the current task states to this run's JSON file."""
        os.makedirs(os.path.dirname(self.stats_file), exist_ok=True)
        with open(self.stats_file, "w") as f:
            json.dump(self.to_dict(), f, indent=2)
            f.write("\n")


def safe_print(*args, **kwargs):
    with print_lock:
        print(*args, **kwargs)


def detect_rate_limited(output: str) -> bool:
    """Return whether an agent's output indicates an exhausted provider allowance."""
    return any(
        re.search(pattern, output, re.IGNORECASE) for pattern in RATE_LIMIT_PATTERNS
    )


def detect_session_error(session_file: str) -> bool:
    """Return whether an agents's session messages contain an error that invalidates the session
    and leaves it pending for a retry"""
    with open(session_file) as f:
        session_output = f.read()
    return any(
        re.search(pattern, session_output, re.IGNORECASE)
        for pattern in SESSION_ERROR_PATTERNS
    )


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
    agent: AgentSpec,
    task_result: Task,
    run: Run,
    prompt_template,
    staging_base,
) -> None:
    """Run a single agent on a single task and update its persisted state."""
    task = task_result.name
    timestamp = run.timestamp
    task_base = task.removesuffix(".rs")
    solution_filename = f"{task_base}_verified.rs"

    with tempfile.TemporaryDirectory(dir=staging_base) as staging_dir:
        original_task_path = os.path.abspath(os.path.join("tasks", task))
        staged_task_path = os.path.join(staging_dir, task)
        shutil.copy2(original_task_path, staged_task_path)

        session_dir_staging = os.path.join(staging_dir, "session")
        os.makedirs(session_dir_staging)

        entrypoint_path = os.path.join(
            os.path.abspath("agents"), agent.agent_dir, agent.entrypoint
        )
        shutil.copy2(entrypoint_path, os.path.join(staging_dir, agent.entrypoint))
        os.chmod(os.path.join(staging_dir, agent.entrypoint), 0o755)

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

        # Subscription-backed agents keep refreshable OAuth credentials outside
        # task staging/session directories so they are never copied into run
        # artifacts. BENCHMARK_AUTH_DIR contains one directory per agent.
        auth_root = os.environ.get("BENCHMARK_AUTH_DIR", ".agent-auth")
        agent_auth_dir = os.path.abspath(os.path.join(auth_root, agent.agent_dir))
        if os.path.isdir(agent_auth_dir):
            cmd.extend(
                [
                    "-v",
                    f"{agent_auth_dir}:/workspace/agent_auth",
                    "-e",
                    "BENCHMARK_AGENT_AUTH_DIR=/workspace/agent_auth",
                ]
            )

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
                f"/workspace/task_env/{agent.entrypoint}",
                f"benchmark-{agent.tag}",
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

            if detect_rate_limited(f"{result.stdout}\n{result.stderr}"):
                safe_print(
                    f"⚠ Agent {agent.name} hit a usage/rate limit on task {task}; leaving it pending for --resume"
                )
                task_result.extra_stats["return_error"] = result.stderr
            elif result.returncode != 0:
                safe_print(
                    f"⚠ Agent {agent.name} exited with code {result.returncode} on task {task}; leaving it pending for --resume"
                )
                task_result.extra_stats["return_error"] = result.stderr
            else:
                task_result.status = "completed"

        except subprocess.TimeoutExpired:
            task_result.timed_out = True
            task_result.status = "completed"
            safe_print(f"✗ Agent {agent.name} timed out on task {task} (20 minutes)")
            subprocess.run(
                ["docker", "stop", container_name], capture_output=True, check=False
            )

        except subprocess.CalledProcessError as e:
            safe_print(f"✗ Agent {agent.name} failed on task {task}: {e}")
            return

        extracted = extract_solution_file(
            staging_dir, solution_filename, agent.name, timestamp
        )
        task_result.update_from_stats(extracted)
        if task_result.solution_file:
            verification_status = verify_solution(
                staging_dir,
                task,
                solution_filename,
                original_task_path,
                staged_task_path,
            )
            task_result.update_from_stats(verification_status)

        session_dir_path = os.path.abspath(
            os.path.join("sessions", agent.name, f"{timestamp}", task_base)
        )
        try:
            shutil.copytree(session_dir_staging, session_dir_path)
            session_stats = compute_session_statistics(agent.name, session_dir_path)
            task_result.extra_stats.update(session_stats)

            session_file = task_result.extra_stats.get("session_file")
            if not session_file or detect_session_error(session_file):
                task_result.status = "pending"
                safe_print(
                    f"⚠ Agent {agent.name} recorded a session error on task {task}; "
                    "leaving it pending for --resume"
                )
                task_result.extra_stats["session_error"] = "Detected error that invalidated the session. Check the session file."

        except Exception as e:  # noqa: BLE001 - session capture must not discard task results
            safe_print(f"Failed to capture statistics for the agent: {e}")
            task_result.extra_stats["statistics_error"] = str(e)
    return


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
                    AgentSpec(
                        name=f"{agent_dir}/{name_no_ext}",
                        tag=agent_dir,
                        entrypoint=model_name,
                        agent_dir=agent_dir,
                    )
                )
    return agents


def start_new_run(agent_filter=None, model_filter=None):
    """Create a run file with every selected task marked pending."""
    task_names = sorted(f for f in os.listdir("tasks") if f.endswith(".rs"))
    agents = discover_agents(agent_filter, model_filter)
    run = Run.create(agents, task_names)
    run.save()
    return run


def resume_run(run_id, agent_filter=None, model_filter=None):
    """Load a prior run and return its original agents and pending task states."""
    run_id = os.path.basename(run_id)
    run_id = run_id.removesuffix(".json")
    if not run_id or run_id in {".", ".."}:
        raise ValueError("--resume must be a run ID, not a path")
    stats_file = os.path.join("runs", f"{run_id}.json")
    try:
        with open(stats_file) as f:
            data = json.load(f)
    except FileNotFoundError as e:
        raise ValueError(f"Run file not found: {stats_file}") from e
    if "configuration" not in data or "agents" not in data:
        raise ValueError("Run file predates resumable runs and cannot be resumed")

    run = Run.from_dict(data, stats_file)
    available_agents = {agent.name for agent in discover_agents()}
    missing_agents = [
        agent.name for agent in run.agents if agent.name not in available_agents
    ]
    if missing_agents:
        raise ValueError(
            f"Cannot resume: configured agent entrypoints are missing: {', '.join(missing_agents)}"
        )
    if agent_filter and any(
        not fnmatch.fnmatch(agent.agent_dir, agent_filter) for agent in run.agents
    ):
        raise ValueError("--agent filter does not match every agent in the run file")
    if model_filter and any(
        not fnmatch.fnmatch(os.path.splitext(agent.entrypoint)[0], model_filter)
        for agent in run.agents
    ):
        raise ValueError("--model filter does not match every model in the run file")

    return run


def run_tasks(max_workers, agent_filter=None, model_filter=None, resume_id=None):
    """Run a new benchmark or resume only the pending tasks from an existing run."""
    if resume_id:
        run = resume_run(resume_id, agent_filter, model_filter)
    else:
        run = start_new_run(agent_filter, model_filter)

    timestamp = run.timestamp
    agents = run.agents
    task_names = run.task_names

    if not agents:
        print("Error: No agents found in agents/ directory")
        sys.exit(1)
    if not task_names:
        print("Error: No tasks found in tasks/ directory")
        sys.exit(1)

    print(f"Found {len(agents)} agent(s): {', '.join(a.name for a in agents)}")
    print(f"Found {len(task_names)} task(s)")
    print()

    build_base_image()
    for agent_dir in sorted({agent.agent_dir for agent in agents}):
        build_agent_image(agent_dir, os.path.join("agents", agent_dir))

    with open("prompt.txt", "r") as f:
        prompt_template = f.read()

    max_workers = min(max_workers, len(task_names))

    staging_base = os.path.abspath(".staging_areas")
    os.makedirs(staging_base, exist_ok=True)

    for agent in agents:
        pending_tasks = run.pending_tasks(agent)
        if not pending_tasks:
            print(f"No unfinished tasks for agent '{agent.name}'.")
            continue
        print(
            f"Submitting {len(pending_tasks)} tasks for agent '{agent.name}' to thread pool ({max_workers} workers)..."
        )
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {
                executor.submit(
                    run_single_job,
                    agent,
                    task,
                    run,
                    prompt_template,
                    staging_base,
                ): task
                for task in pending_tasks
            }
            for future in as_completed(futures):
                task = futures[future]
                try:
                    future.result()
                except Exception as e:  # noqa: BLE001 - preserve the remaining tasks after a worker crash
                    safe_print(f"✗ Task {task.name} crashed before completion: {e}")
                    task.extra_stats["error"] = str(e)
                run.save()

    print("=" * 60)
    print(f"Benchmark complete. Run statistics saved to {run.stats_file}")
    print("=" * 60)

    artifact_paths = [run.stats_file]
    artifact_paths.extend(
        glob.glob(os.path.join("solutions", "**", timestamp), recursive=True)
    )
    artifact_paths.extend(
        glob.glob(os.path.join("sessions", "**", timestamp), recursive=True)
    )
    result = subprocess.run(
        ["git", "add", "--", *artifact_paths],
        capture_output=True,
        text=True,
        check=False,
    )
    git_output = (result.stdout + result.stderr).strip()
    if result.returncode != 0:
        print(f"⚠ Git staging skipped: {git_output}")
        return
    result = subprocess.run(
        ["git", "commit", "-m", f"run {timestamp}"],
        capture_output=True,
        text=True,
        check=False,
    )
    git_output = (result.stdout + result.stderr).strip()
    if result.returncode == 0:
        print(f"✓ Committed run artifacts: 'run {timestamp}'")
    else:
        print(f"⚠ Git commit skipped: {git_output}")


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
