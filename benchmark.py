#!/usr/bin/env python3

import os
import subprocess
import sys
import tempfile
import shutil
import json
import uuid
from datetime import datetime

def build_base_image():
    """Build the base Docker image with all shared dependencies."""
    print("=" * 60)
    print("Building base image: benchmark-base:latest")
    print("=" * 60)
    subprocess.run([
        "docker", "build", "-t", "benchmark-base:latest", "-f", "Dockerfile", "."
    ], check=True)
    print()


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
        print(f"Starting verification container {container_name}...")
        # Start the container in detached mode running sleep infinity
        subprocess.run([
            "docker", "run", "-d", "--rm", "--name", container_name,
            "-v", f"{staging_dir}:/workspace/task_env",
            "benchmark-base:latest",
            "sleep", "infinity"
        ], check=True, capture_output=True)

        print("Running Verus verification...")
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
                print(f"Caught error while analysing Verus output: {e}")

        print(f"Verus passed: {stats['verus_passed']}")

        # Restore the original task file in case the agent modified it
        try:
            shutil.copy2(original_task_path, staged_task_path)
        except PermissionError:
            os.chmod(staged_task_path, 0o644)
            os.remove(staged_task_path)
            shutil.copy2(original_task_path, staged_task_path)

        # Run Lynette Cheat Checker validation
        print("Running Lynette cheat checker...")
        lynette_cmd = [
            "docker", "exec", container_name,
            "python3", "/opt/lynette.py",
            f"/workspace/task_env/{task}",
            f"/workspace/task_env/{solution_filename}"
        ]
        lynette_res = subprocess.run(lynette_cmd, capture_output=True, text=True)
        stats["cheat_checker_passed"] = (lynette_res.returncode == 0)

        print(f"Cheat checker passed: {stats['cheat_checker_passed']}")

    finally:
        print(f"Cleaning up verification container {container_name}...")
        subprocess.run(["docker", "kill", container_name], capture_output=True)

    return stats


def compute_session_statistics(agent_name, session_path) -> dict:
    """Run the agent's statistics.py on a session file and return the parsed stats."""
    agent_dir = agent_name.split("/")[0]
    stats_script = os.path.join("agents", agent_dir, "statistics.py")
    if not os.path.exists(stats_script):
        print(f"  (no statistics.py found for agent '{agent_dir}')")
        return {}

    result = subprocess.run(
        [sys.executable, stats_script, session_path],
        capture_output=True, text=True
    )

    if result.returncode != 0:
        print(f"⚠ statistics.py exited with code {result.returncode}")
        if result.stderr:
            print(f"   stderr: {result.stderr.strip()}")
        return {}

    try:
        stats = json.loads(result.stdout)
        print("✓ Session statistics recorded")
        return stats
    except json.JSONDecodeError:
        print("⚠ Could not parse statistics output")
        return {}


def extract_solution_file(staging_dir, solution_filename, agent_name, timestamp) -> dict:
    """Extract the solution file from the staging directory to the permanent solutions folder."""
    expected_solution_path = os.path.join(staging_dir, solution_filename)
    if os.path.exists(expected_solution_path):
        final_solution_dir = os.path.abspath(os.path.join("solutions", agent_name, f"{timestamp}"))
        os.makedirs(final_solution_dir, exist_ok=True)
        final_solution_path = os.path.join(final_solution_dir, solution_filename)
        shutil.copy2(expected_solution_path, final_solution_path)
        print(f"✓ Solution extracted to {final_solution_path}")
        return {"solution_generated": True}
    else:
        print(f"✗ Agent did not produce the expected file: {solution_filename}")
        return {"solution_generated": False}


def extract_session_file(staging_dir, session_filename, agent_name, timestamp) -> dict:
    """Extract the session file from the staging directory to the permanent sessions folder."""
    expected_session_path = os.path.join(staging_dir, session_filename)
    if os.path.exists(expected_session_path):
        final_session_dir = os.path.abspath(os.path.join("sessions", agent_name, f"{timestamp}"))
        os.makedirs(final_session_dir, exist_ok=True)
        final_session_path = os.path.join(final_session_dir, session_filename)
        shutil.copy2(expected_session_path, final_session_path)
        print(f"✓ Session extracted to {final_session_path}")
        return {"session_extracted": True}
    else:
        print(f"✗ Could not find the expected session file: {session_filename}")
        return {"session_extracted": False}


def run_tasks():
    """Main benchmark orchestration."""
    # Build the base docker image once
    build_base_image()

    # Read the prompt template
    with open("prompt.txt", "r") as f:
        prompt_template = f.read()

    # Discover agents and tasks (agents are now agent/model)
    tasks = [f for f in os.listdir("tasks") if f.endswith(".rs")]
    agents = []
    if os.path.exists("agents"):
        for agent_dir in sorted(os.listdir("agents")):
            agent_path = os.path.join("agents", agent_dir)
            if not os.path.isdir(agent_path):
                continue
            for model_dir in sorted(os.listdir(agent_path)):
                model_path = os.path.join(agent_path, model_dir)
                if os.path.isdir(model_path) and os.path.exists(os.path.join(model_path, "Dockerfile")):
                    agents.append({
                        "name": f"{agent_dir}/{model_dir}",
                        "tag": f"{agent_dir}-{model_dir}"
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

    for agent in agents:
        agent_name = agent["name"]
        agent_tag = agent["tag"]
        agent_path = os.path.join("agents", agent_name)

        # Build the agent's docker image
        build_agent_image(agent_tag, agent_path)
        run_stats["agents"][agent_name] = {"tasks": {}}

        # Create an isolated staging directory too keep temporary dirs for tasks
        staging_base = os.path.abspath(".staging_areas")
        os.makedirs(staging_base, exist_ok=True)

        for task in tasks:
            print("=" * 60)
            print(f"Running agent '{agent_name}' on task '{task}'")
            print("=" * 60)

            # Strip .rs extension and create the expected output filename
            task_base = task[:-3] if task.endswith(".rs") else task
            solution_filename = f"{task_base}_verified.rs"
            session_filename = f"{task_base}_session.jsonl" # NOTE for now the agent has to save session in jsonl format

            task_stats = {
                "solution_generated": False,
                "verus_passed": False,
                "cheat_checker_passed": False,
                "timed_out": False
            }
            run_stats["agents"][agent_name]["tasks"][task] = task_stats

            with tempfile.TemporaryDirectory(dir=staging_base) as staging_dir:
                # Copy the specific task file into the empty staging area
                original_task_path = os.path.abspath(os.path.join("tasks", task))
                staged_task_path = os.path.join(staging_dir, task)
                shutil.copy2(original_task_path, staged_task_path)

                # Format the prompt with the path to the task file inside the container
                task_path_in_container = f"/workspace/task_env/{task}"
                output_path_in_container = f"/workspace/task_env/{solution_filename}"
                session_path_in_container = f"/workspace/task_env/{session_filename}"
                formatted_prompt = prompt_template.format(task=task_path_in_container, output=output_path_in_container)

                # Run the container
                container_name = f"agent_{uuid.uuid4().hex[:8]}"
                cmd = [
                    "docker", "run", "--rm", "--name", container_name,
                    "-v", f"{staging_dir}:/workspace/task_env",
                    "-e", "TASK_PROMPT",
                    "-e", "SESSION",
                ]

                # Pass through API keys to Docker
                for key in ["ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GEMINI_API_KEY", "OPENCODE_API_KEY", "OPENROUTER_API_KEY"]:
                    if key in os.environ:
                        cmd.extend(["-e", key])

                cmd.append(f"benchmark-{agent_tag}")

                # Build the environment for the subprocess that runs docker
                env = os.environ.copy()
                env["TASK_PROMPT"] = formatted_prompt
                env["SESSION"] = session_path_in_container

                try:
                    # Create a simple wrapper script to run the agent inside the container with the prompt
                    result = subprocess.run(
                        cmd,
                        env=env,
                        check=False,
                        capture_output=True,
                        text=True,
                        timeout=2400
                    )

                    # Display captured output
                    if result.stdout:
                        print("[STDOUT]")
                        print(result.stdout)
                    if result.stderr:
                        print("[STDERR]")
                        print(result.stderr)

                    if result.returncode != 0:
                        print(f"⚠ Agent {agent_name} exited with code {result.returncode} on task {task}")


                except subprocess.TimeoutExpired:
                    task_stats["timed_out"] = True
                    print(f"✗ Agent {agent_name} timed out on task {task} (40 minutes)")
                    subprocess.run(["docker", "kill", container_name], capture_output=True, check=False)

                except subprocess.CalledProcessError as e:
                    print(f"✗ Agent {agent_name} failed on task {task}: {e}")

                finally:
                    subprocess.run(["docker", "rm", "-f", container_name], capture_output=True, check=False)

                # Extract the solution file
                extracted = extract_solution_file(staging_dir, solution_filename, agent_name, timestamp)
                task_stats.update(extracted)

                # Verify the solution
                if extracted["solution_generated"]:
                    verification_status = verify_solution(staging_dir, task, solution_filename, original_task_path, staged_task_path)
                    task_stats.update(verification_status)

                # Extract the session file
                session_extracted = extract_session_file(staging_dir, session_filename, agent_name, timestamp)
                task_stats.update(session_extracted)

                # Compute session statistics
                if session_extracted["session_extracted"]:
                    expected_session_path = os.path.join(staging_dir, session_filename)
                    session_stats = compute_session_statistics(agent_name, expected_session_path)
                    task_stats.update(session_stats)

                print()

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

if __name__ == "__main__":
    run_tasks()
