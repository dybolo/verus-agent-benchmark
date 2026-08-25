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
- A run JSON file is created with every task marked `pending` and updated after every completed task. If a provider reports a usage/rate limit, rerun later with `python3 benchmark.py --resume <run-id>`; completed tasks are skipped and the limited task is started again. Timed-out tasks remain final and are not retried.

## Important

- The script uses the user's current environment variables for provider credentials.
- Make sure to run the agents with a provider with the credentials set in the environment.
- `.model` entrypoint files must be executable (`chmod +x`).

### ChatGPT subscription models

The `opencode/gpt-5.6-luna` and `pi/gpt-5.6-luna` entrypoints use ChatGPT
Plus/Pro OAuth instead of an OpenAI API key. Credentials live under
`.agent-auth/<agent>/` by default (or under `$BENCHMARK_AUTH_DIR/<agent>/`) and
are mounted directly into the container; they are excluded from Git and are
not copied into session artifacts.

Build the images, then authenticate each agent once:

```bash
docker build -t benchmark-base:latest -f Dockerfile .
docker build -t benchmark-opencode agents/opencode
docker build -t benchmark-pi agents/pi

mkdir -p .agent-auth/opencode .agent-auth/pi

docker run --rm -it --user "$(id -u):$(id -g)" \
  -e HOME=/root -e XDG_DATA_HOME=/auth -e XDG_STATE_HOME=/tmp/opencode-state \
  -v "$PWD/.agent-auth/opencode:/auth" \
  benchmark-opencode opencode auth login

docker run --rm -it --user "$(id -u):$(id -g)" \
  -e HOME=/root -e PI_CODING_AGENT_DIR=/auth \
  -v "$PWD/.agent-auth/pi:/auth" \
  benchmark-pi pi
```

For OpenCode, choose **OpenAI → ChatGPT Plus/Pro**. In Pi, enter `/login` and
choose **OpenAI ChatGPT Plus/Pro (Codex)**, then exit after authentication.
Run only these model entrypoints with:

```bash
python3 benchmark.py -m gpt-5.6-luna
```

# Streamlit App

## Reviewing runs

The Streamlit viewer provides a human-readable overview of run results, conversation logs, and generated solution files. Run it from the repository root:

```bash
python3 -m pip install -e streamlit_app
benchmark-runs-viewer
```

Use the sidebar to select a run, agent/model, result status, and task. Conversation tool calls and outputs are collapsed by default, and the solution view shows a diff whenever the original task is still available.

## Generating evaluation plots

The thesis evaluation dashboard reads the JSON files in `runs/` directly and
selects the latest `opencode` and `pi` harness/model results in the largest
identical task cohort (runs with common tests) by default. Start it from the repository root:

```bash
python3 -m pip install -e streamlit_app
benchmark-plots-viewer
```

Use the sidebar to select a cohort, harness/model conditions, proof styles,
source modules, tasks, and figure dimensions. Each plot can be downloaded as
SVG, PDF, 300-DPI PNG, or CSV containing the exact displayed data. 

Run the analysis and rendering tests with:

```bash
python3 -m unittest discover -s streamlit_app/tests
```
