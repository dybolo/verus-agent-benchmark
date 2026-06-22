#!/usr/bin/env python3

import argparse
import dataclasses
import fnmatch
import importlib.util
import os
import subprocess
import sys
import tempfile
import shutil
import glob
import json
import uuid
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime

from stats_protocol import StatsFn

def build_base_image():
    """Build the base Docker image with all shared dependencies."""
    print("=" * 60)
    print("Building base image: benchmark-base:latest")
    print("=" * 60)
    subprocess.run([
        "docker", "build", "-t", "benchmark-base:latest", "-f", "Dockerfile", "."
    ], check=True)
    print()


print_lock = threading.Lock()


def safe_print(*args, **kwargs):
    with print_lock:
        print(*args, **kwargs)


def build_agent_image(agent_tag, agent_path):
    """Build a specific agent's Docker image."""
    print(f"Building agent image: benchmark-{agent_tag}")
    subprocess.run([
        "docker", "build", "-t", f"benchmark-{agent_tag}", agent_path
    ], check=True)
    print()


def verify_solution(staging_dir, task, solution_filename, original_task_path, staged_task_path) -> dict:
    """Run Verus and Lynette checks on the generated solution using a single persistent container."""
    stats = {
        "verus_passed": False,
        "cheat_checker_passed": False
    }

    container_name = f"verify_{uuid.uuid4().hex[:8]}"

    try:
        safe_print(f"Starting verification container {container_name}...")
        # Start the container in detached mode running sleep infinity
        subprocess.run([
            "docker", "run", "-d", "--rm", "--name", container_name,
            "-v", f"{staging_dir}:/workspace/task_env",
            "benchmark-base:latest",
            "sleep", "infinity"
        ], check=True, capture_output=True)

        safe_print("Running Verus verification...")
        verus_cmd = [
            "docker", "exec", container_name,
            "verus", f"/workspace/task_env/{solution_filename}", "--output-json"
        ]
        verus_res = subprocess.run(verus_cmd, capture_output=True, text=True)

        # We should try to find the JSON string in stdout since verus might output other lines
        try:
            verus_data = json.loads(verus_res.stdout)
            stats["verus_passed"] = verus_data.get("verification-results", {}).get("success", False)
        except json.JSONDecodeError:
            # Attempt to find json inside stdout if there's surrounding text
            try:
                json_start = verus_res.stdout.find('{')
                json_end = verus_res.stdout.rfind('}')
                if json_start != -1 and json_end != -1:
                    verus_data = json.loads(verus_res.stdout[json_start:json_end+1])
                    stats["verus_passed"] = verus_data.get("verification-results", {}).get("success", False)
                else:
                    stats["verus_passed"] = False
            except Exception as e:
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
            "docker", "exec", container_name,
            "python3", "/opt/lynette.py",
            f"/workspace/task_env/{task}",
            f"/workspace/task_env/{solution_filename}"
        ]
        lynette_res = subprocess.run(lynette_cmd, capture_output=True, text=True)
        stats["cheat_checker_passed"] = (lynette_res.returncode == 0)

        safe_print(f"Cheat checker passed: {stats['cheat_checker_passed']}")

    finally:
        safe_print(f"Cleaning up verification container {container_name}...")
        subprocess.run(["docker", "kill", container_name], capture_output=True)

    return stats


def compute_session_statistics(agent_name, session_path) -> dict:
    """Import the agent's statistics module and call compute_statistics directly."""
    agent_dir = agent_name.split("/")[0]
    stats_script = os.path.join("agents", agent_dir, "statistics.py")
    if not os.path.exists(stats_script):
        safe_print(f"  (no statistics.py found for agent '{agent_dir}')")
        return {}

    spec = importlib.util.spec_from_file_location(f"agents_{agent_dir}_statistics", stats_script)
    if spec is None:
        safe_print(f"  (could not load statistics.py for agent '{agent_dir}')")
        return {}

    mod = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(mod)
        fn = mod.compute_statistics
        if not isinstance(fn, StatsFn):
            safe_print(f"⚠ Agent '{agent_dir}' does not conform to the StatsFn protocol")
            return {}
        stats = fn(session_path)
        safe_print("✓ Session statistics recorded")
        return dataclasses.asdict(stats)
    except Exception as e:
        safe_print(f"⚠ Could not compute statistics: {e}")
        return {}


def extract_solution_file(staging_dir, solution_filename, agent_name, timestamp) -> dict:
    """Extract the solution file from the staging directory to the permanent solutions folder."""
    expected_solution_path = os.path.join(staging_dir, solution_filename)
    if os.path.exists(expected_solution_path):
        final_solution_dir = os.path.abspath(os.path.join("solutions", agent_name, f"{timestamp}"))
        os.makedirs(final_solution_dir, exist_ok=True)
        final_solution_path = os.path.join(final_solution_dir, solution_filename)
        shutil.copy2(expected_solution_path, final_solution_path)
        safe_print(f"✓ Solution extracted to {final_solution_path}")
        return {"solution_file": os.path.relpath(final_solution_path)}
    else:
        safe_print(f"✗ Agent did not produce the expected file: {solution_filename}")
        return {"solution_file": None}


def run_single_job(agent_name, agent_tag, agent_dir, entrypoint, task, timestamp, prompt_template, staging_base) -> dict:
    """Run a single agent on a single task and return its stats."""
    task_base = task[:-3] if task.endswith(".rs") else task
    solution_filename = f"{task_base}_verified.rs"

    task_stats = {
        "verus_passed": False,
        "cheat_checker_passed": False,
        "timed_out": False
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
        formatted_prompt = prompt_template.format(task=task_path_in_container, output=output_path_in_container)

        container_name = f"agent_{uuid.uuid4().hex[:8]}"
        cmd = [
            "docker", "run", "--rm", "--name", container_name,
            "--user", f"{os.getuid()}:{os.getgid()}",
            "-e", "HOME=/root",
            "-v", f"{staging_dir}:/workspace/task_env",
            "-e", "TASK_PROMPT",
            "-e", "SESSION",
        ]

        for key in ["ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GEMINI_API_KEY", "OPENCODE_API_KEY", "OPENROUTER_API_KEY"]:
            if key in os.environ:
                cmd.extend(["-e", key])

        cmd.extend(["--entrypoint", f"/workspace/task_env/{entrypoint}", f"benchmark-{agent_tag}"])

        env = os.environ.copy()
        env["TASK_PROMPT"] = formatted_prompt
        env["SESSION"] = session_path_in_container

        try:
            result = subprocess.run(
                cmd,
                env=env,
                check=False,
                capture_output=True,
                text=True,
                timeout=1200
            )

            if result.stdout:
                safe_print("[STDOUT]")
                safe_print(result.stdout)
            if result.stderr:
                safe_print("[STDERR]")
                safe_print(result.stderr)

            if result.returncode != 0:
                safe_print(f"⚠ Agent {agent_name} exited with code {result.returncode} on task {task}")

        except subprocess.TimeoutExpired:
            task_stats["timed_out"] = True
            safe_print(f"✗ Agent {agent_name} timed out on task {task} (20 minutes)")
            subprocess.run(["docker", "stop", container_name], capture_output=True, check=False)

        except subprocess.CalledProcessError as e:
            safe_print(f"✗ Agent {agent_name} failed on task {task}: {e}")

        extracted = extract_solution_file(staging_dir, solution_filename, agent_name, timestamp)
        task_stats.update(extracted)
        if extracted["solution_file"]:
            verification_status = verify_solution(staging_dir, task, solution_filename, original_task_path, staged_task_path)
            task_stats.update(verification_status)

        session_dir_path = os.path.abspath(os.path.join("sessions", agent_name, f"{timestamp}", task_base))
        try:
            shutil.copytree(session_dir_staging, session_dir_path)
            session_stats = compute_session_statistics(agent_name, session_dir_path)
            task_stats.update(session_stats)
        except Exception as e:
            safe_print(f"Failed to capture statistics for the agent: {e}")

    return {task: task_stats}


def run_tasks(max_workers, agent_filter=None, model_filter=None):
    """Main benchmark orchestration."""
    # Build the base docker image once
    build_base_image()

    # Read the prompt template
    with open("prompt.txt", "r") as f:
        prompt_template = f.read()

    # Discover agents and tasks
    tasks = [f for f in os.listdir("tasks") if f.endswith(".rs")]
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
            build_agent_image(agent_dir, agent_path)
            for model_file in sorted(glob.glob(os.path.join(agent_path, "*.model"))):
                model_name = os.path.basename(model_file)
                name_no_ext = os.path.splitext(model_name)[0]
                if model_filter and not fnmatch.fnmatch(name_no_ext, model_filter):
                    continue
                agents.append({
                    "name": f"{agent_dir}/{name_no_ext}",
                    "tag": agent_dir,
                    "entrypoint": model_name,
                    "agent_dir": agent_dir,
                })

    if not agents:
        print("Error: No agents found in agents/ directory")
        sys.exit(1)

    if not tasks:
        print("Error: No tasks found in tasks/ directory")
        sys.exit(1)

    print(f"Found {len(agents)} agent(s): {', '.join(a['name'] for a in agents)}")
    print(f"Found {len(tasks)} task(s)")
    print()

    # Generate timestamp for this benchmark run
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    run_stats = {
        "timestamp": timestamp,
        "agents": {}
    }

    # Create an isolated staging directory to keep temporary dirs for tasks
    staging_base = os.path.abspath(".staging_areas")
    os.makedirs(staging_base, exist_ok=True)

    for agent in agents:
        agent_name = agent["name"]
        agent_tag = agent["tag"]
        run_stats["agents"][agent_name] = {"tasks": {}}

        print(f"Submitting {len(tasks)} tasks for agent '{agent_name}' to thread pool ({max_workers} workers)...")
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {
                executor.submit(run_single_job, agent_name, agent_tag, agent["agent_dir"], agent["entrypoint"], task, timestamp, prompt_template, staging_base): task
                for task in tasks
            }
            for future in as_completed(futures):
                run_stats["agents"][agent_name]["tasks"].update(future.result())

    # Save run statistics to JSON file
    os.makedirs("runs", exist_ok=True)
    stats_file = os.path.join("runs", f"{timestamp}.json")
    with open(stats_file, "w") as f:
        json.dump(run_stats, f, indent=2)

    print("=" * 60)
    print(f"Benchmark complete. Run statistics saved to {stats_file}")
    print("=" * 60)

    # Commit only the artifacts from this run
    subprocess.run(
        ["git", "add",
         f"solutions/**/{timestamp}/**",
         f"sessions/**/{timestamp}/**",
         f"runs/{timestamp}.json"],
        capture_output=True, text=True
    )
    result = subprocess.run(
        ["git", "commit", "-m", f"run {timestamp}"],
        capture_output=True, text=True
    )
    if result.returncode == 0:
        print(f"✓ Committed run artifacts: 'run {timestamp}'")
    else:
        print(f"⚠ Git commit skipped: {result.stderr.strip()}")

def main():
    parser = argparse.ArgumentParser(description="Run benchmarks")
    parser.add_argument("--parallel", "-j", type=int, default=os.cpu_count() or 4,
                        help="Max parallel tasks (default: CPU count)")
    parser.add_argument("--agent", "-a",
                        help="Glob filter for agent directory name (e.g. 'opencode', 'open*')")
    parser.add_argument("--model", "-m",
                        help="Glob filter for model name (e.g. 'gpt-5.4', '*gpt*')")
    args = parser.parse_args()
    run_tasks(max_workers=args.parallel, agent_filter=args.agent, model_filter=args.model)


if __name__ == "__main__":
    main()
