#!/usr/bin/env python3

import os
import subprocess
import sys
import tempfile
import shutil

def build_base_image():
    """Build the base Docker image with all shared dependencies."""
    print("=" * 60)
    print("Building base image: benchmark-base:latest")
    print("=" * 60)
    subprocess.run([
        "docker", "build", "-t", "benchmark-base:latest", "-f", "Dockerfile", "."
    ], check=True)
    print()

def build_agent_image(agent_name):
    """Build a specific agent's Docker image."""
    print(f"Building agent image: benchmark-{agent_name}")
    agent_dir = os.path.join("agents", agent_name)
    subprocess.run([
        "docker", "build", "-t", f"benchmark-{agent_name}", agent_dir
    ], check=True)
    print()

def run_tasks():
    """Main benchmark orchestration."""
    # Build the base docker image once
    build_base_image()

    # Read the prompt template
    with open("prompt.txt", "r") as f:
        prompt_template = f.read()

    # Discover agents and tasks
    agents = [d for d in os.listdir("agents") if os.path.isdir(os.path.join("agents", d))]
    tasks = [f for f in os.listdir("tasks") if f.endswith(".rs")]

    if not agents:
        print("Error: No agents found in agents/ directory")
        sys.exit(1)

    if not tasks:
        print("Error: No tasks found in tasks/ directory")
        sys.exit(1)

    print(f"Found {len(agents)} agent(s): {', '.join(agents)}")
    print(f"Found {len(tasks)} task(s)")
    print()

    for agent in agents:
        # Build the agent's docker image
        build_agent_image(agent)

        for task in tasks:
            print("=" * 60)
            print(f"Running agent '{agent}' on task '{task}'")
            print("=" * 60)

            # Strip .rs extension and create the expected output filename
            task_base = task[:-3] if task.endswith(".rs") else task
            solution_filename = f"{task_base}_verified.rs"

            # Create an isolated staging directory just for THIS run
            with tempfile.TemporaryDirectory() as staging_dir:
                # Copy the specific task file into the empty staging area
                original_task_path = os.path.abspath(os.path.join("tasks", task))
                staged_task_path = os.path.join(staging_dir, task)
                shutil.copy2(original_task_path, staged_task_path)

                # Format the prompt with the path to the task file inside the container
                task_path_in_container = f"/workspace/task_env/{task}"
                formatted_prompt = prompt_template.format(task=task_path_in_container)

                # Run the container, mounting ONLY this isolated staging folder
                cmd = [
                    "docker", "run", "--rm",
                    "-v", f"{staging_dir}:/workspace/task_env",
                    "-w", "/workspace/task_env",
                    f"benchmark-{agent}",
                ]

                # Pass the formatted prompt as environment variable for clarity
                env = os.environ.copy()
                env["TASK_PROMPT"] = formatted_prompt

                try:
                    # Create a simple wrapper script to run the agent inside the container with the prompt
                    result = subprocess.run(
                        cmd,
                        env=env,
                        check=False,
                        capture_output=False
                    )

                    # After the container finishes, extract the solution file
                    expected_solution_path = os.path.join(staging_dir, solution_filename)

                    if os.path.exists(expected_solution_path):
                        # Move it to the permanent solutions folder
                        final_solution_dir = os.path.abspath(os.path.join("solutions", agent))
                        os.makedirs(final_solution_dir, exist_ok=True)
                        final_solution_path = os.path.join(final_solution_dir, solution_filename)

                        shutil.copy2(expected_solution_path, final_solution_path)
                        print(f"✓ Solution extracted to {final_solution_path}")
                    else:
                        print(f"✗ Agent did not produce the expected file: {solution_filename}")

                    if result.returncode != 0:
                        print(f"⚠ Agent {agent} exited with code {result.returncode} on task {task}")

                except subprocess.CalledProcessError as e:
                    print(f"✗ Agent {agent} failed on task {task}: {e}")

                print()

if __name__ == "__main__":
    run_tasks()
