# Benchmark repo for verus-based agents

## Requirements

- python
- docker

## Adding Agents

- Add a new agent by creating a directory under `agents/<agent_name>/` with:
  - `Dockerfile` — defines the agent's environment (dependencies, tooling). No `CMD` needed — the entrypoint is provided at runtime.
  - `<model_name>.model` — an executable entrypoint script named after the model (e.g. `gpt-5.4-nano.model`). It receives a prompt for the task in the `TASK_PROMPT` environment variable and the directory to save session logs to in the `SESSION` environment variable.
  - `statistics.py` — placed at `agents/<agent_name>/statistics.py` to parse that agent's session logs. It must expose a function `compute_statistics(session_dir: str) -> Stats` conforming to the `StatsFn` protocol (defined in `stats_protocol.py`).
- To test the same agent with a different model, just add another `.model` file (no new Dockerfile needed).
- Keep any provider/model logic inside the entrypoint script (e.g. `pi --model openrouter/gpt-5.4-nano:xhigh ...`).

### How it works

Each agent has a single `Dockerfile` shared by all its entrypoints. When the benchmark runs, it builds the agent image once, then for each `.model` file it starts a container with `--entrypoint /workspace/task_env/<model>.model`, staging the entrypoint alongside the task files.

## How to run

- Run the benchmark with `python3 benchmark.py`.
- Use the `-j` flag to set the number of parallel workers (defaults to the number of CPU cores).
- Use `-a <pattern>` or `--agent <pattern>` to filter agents by glob pattern (e.g. `opencode`, `open*`).
- Use `-m <pattern>` or `--model <pattern>` to filter models by glob pattern (e.g. `gpt-5.4`, `*gpt*`).

## Reviewing runs

The Streamlit viewer provides a human-readable overview of run results, conversation logs, and generated solution files. Run it from the repository root:

```bash
python3 -m pip install -r requirements.txt
python3 -m streamlit run run_viewer.py
```

Use the sidebar to select a run, agent/model, result status, and task. Conversation tool calls and outputs are collapsed by default, and the solution view shows a diff whenever the original task is still available.

## Important

- The script uses the user's current environment variables for provider credentials.
- Make sure to run the agents with a provider with the credentials set in the environment.
- `.model` entrypoint files must be executable (`chmod +x`).
