# Verus agent benchmark

A Docker-based benchmark for coding agents that repair incomplete Verus proofs
in concurrent Rust programs. Each proposed solution is checked with Verus and
Lynette (adapted from the [original implementation]((https://github.com/microsoft/verus-proof-synthesis/tree/main/utils/lynette))); a valid repair must pass both checks.

The corpus contains 75 focused tasks (42 atomic-operation proofs and 33
state-machine proofs) and 17 full-file tasks. See [TASKS.md](TASKS.md) for the
manifest, reference proofs, smaller follow-up sets, and task metadata.

## Requirements

- Python 3.10 or newer.
- Docker with a running daemon. The images install Rust, Verus, and Lynette.
- Provider credentials for the selected entrypoint (see below).
- Git, if you want the runner's automatic run-artifact commit to succeed.

Run commands from the repository root. Building the images requires network
access to download dependencies.

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

The runner builds the base image and selected agent images automatically.
Without filters, it runs every discovered agent/model entrypoint on `tasks/`.
For example:

```bash
python3 benchmark.py -a opencode -m gpt-5.6-luna -j 4
python3 benchmark.py -a pi -m claude-sonnet-4.6 --task-directory full_tasks -j 4
python3 benchmark.py -a opencode -m gpt-5.6-luna --task-directory tasks_2
python3 benchmark.py --resume <run-id>
```

- Run the benchmark with `python3 benchmark.py`.
- Use `--task-directory <directory>` to load `.rs` tasks from another directory (defaults to `tasks/`).
- Use `--verus-version <release-tag>` to download a specific Verus GitHub release when building the images. Omit it (or use `latest`) for the latest release. Use the exact tag from the [Verus releases](https://github.com/verus-lang/verus/releases) page.
- Use the `-j` flag to set the number of parallel workers (defaults to the number of CPU cores).
- Use `-a <pattern>` or `--agent <pattern>` to filter agents by glob pattern (e.g. `opencode`, `open*`).
- Use `-m <pattern>` or `--model <pattern>` to filter models by glob pattern (e.g. `gpt-5.4`, `*gpt*`).
- Each agent runs its tasks with up to `-j` workers; agent/model conditions run sequentially. Each agent invocation has a 20-minute timeout.
- A run JSON file is created with every task marked `pending` and saved after each worker finishes. Usage/rate limits, nonzero agent exits, and missing or invalid sessions leave tasks pending. Resume with `python3 benchmark.py --resume <run-id>` (the filename under `runs/`, without `.json`). Completed tasks are skipped. Timeouts are recorded as completed, but a missing or invalid session can still make them pending.
- Resume uses the original agents, task directory, and Verus version selection. An explicitly supplied task directory or Verus version must match the saved run; agent/model filters must match every saved condition. Runs saved before version selection was supported default to `latest`. To keep the same release across resumes, select an explicit release tag; `latest` can change between builds (and Docker may reuse a cached download).

The downloader also supports `python3 fetch_verus_release.py --version <release-tag>`.
For a manual base-image build, use
`docker build --build-arg VERUS_VERSION=<release-tag> -t benchmark-base:latest .`.

Results are written to:

| Path | Contents |
| --- | --- |
| `runs/<run-id>.json` | Configuration, task status, verification results, token/cost totals, tool-call counts, and durations. |
| `sessions/<agent>/<model>/<run-id>/<task>/` | Agent session logs. |
| `solutions/<agent>/<model>/<run-id>/<task>_verified.rs` | Generated solutions, when produced. |

At the end of a run, the runner stages its artifacts and attempts a Git commit
named `run <run-id>`.

## Important

- The runner forwards these provider variables when set: `ANTHROPIC_API_KEY`, `OPENAI_API_KEY`, `GEMINI_API_KEY`, `OPENCODE_API_KEY`, `OPENROUTER_API_KEY`, and `AWS_BEARER_TOKEN_BEDROCK`.
- The checked-in `claude-sonnet-4.6` entrypoints for OpenCode and Pi use Amazon Bedrock. Configure `AWS_BEARER_TOKEN_BEDROCK` for those entrypoints; the `gpt-5.6-luna` entrypoints use the OAuth setup below.
- `.model` entrypoint files must be executable (`chmod +x`).

### ChatGPT subscription models

The `codex/gpt-5.6-luna`, `opencode/gpt-5.6-luna`, `pi/gpt-5.6-luna`, and
`copilot/gpt-5.6-luna` entrypoints use ChatGPT Plus/Pro OAuth instead of an
OpenAI API key. Credentials live under `.agent-auth/<agent>/` by default (or
under `$BENCHMARK_AUTH_DIR/<agent>/`). At runtime, only the agent's `auth.json`
file is mounted into the container, at `/tmp/auth.json`; the containing auth
directory and any CLI session history in it are not exposed. Credentials are
excluded from Git and are not copied into session artifacts.

Build the images, then authenticate each agent once:

```bash
docker build -t benchmark-base:latest -f Dockerfile .
docker build -t benchmark-codex agents/codex
docker build -t benchmark-copilot agents/copilot
docker build -t benchmark-opencode agents/opencode
docker build -t benchmark-pi agents/pi

mkdir -p .agent-auth/codex .agent-auth/copilot .agent-auth/opencode .agent-auth/pi

docker run --rm -it --user "$(id -u):$(id -g)" \
  -e CODEX_HOME=/auth \
  -v "$PWD/.agent-auth/codex:/auth" \
  benchmark-codex codex login --device-auth

docker run --rm -it --user "$(id -u):$(id -g)" \
  -e CODEX_HOME=/auth \
  -v "$PWD/.agent-auth/copilot:/auth" \
  benchmark-codex codex login --device-auth

docker run --rm -it --user "$(id -u):$(id -g)" \
  -e HOME=/root -e XDG_DATA_HOME=/auth -e XDG_STATE_HOME=/tmp/opencode-state \
  -v "$PWD/.agent-auth/opencode:/auth" \
  benchmark-opencode opencode auth login

docker run --rm -it --user "$(id -u):$(id -g)" \
  -e HOME=/root -e PI_CODING_AGENT_DIR=/auth \
  -v "$PWD/.agent-auth/pi:/auth" \
  benchmark-pi pi
```

For Codex and Copilot, complete the browser OAuth login. For OpenCode, choose
**OpenAI → ChatGPT Plus/Pro**. In Pi, enter `/login` and
choose **OpenAI ChatGPT Plus/Pro (Codex)**, then exit after authentication.
Run only these model entrypoints with:

```bash
python3 benchmark.py -m gpt-5.6-luna
```

## Streamlit dashboards

### Reviewing runs

The Streamlit viewer provides a human-readable overview of run results, conversation logs, and generated solution files. Run it from the repository root:

```bash
python3 -m pip install -e streamlit_app
benchmark-runs-viewer
```

Use the sidebar to select a run, agent/model, result status, and task. Conversation tool calls and outputs are collapsed by default, and the solution view shows a diff whenever the original task is still available.

### Generating evaluation plots

The thesis evaluation dashboard reads the JSON files in `runs/` directly and
selects the latest `opencode` and `pi` harness/model results in the largest
identical task cohort (runs with common tests) by default. Start it from the repository root:

```bash
python3 -m pip install -e streamlit_app
benchmark-plots-viewer
```

Use the sidebar to select a cohort, harness/model conditions, proof styles,
source modules, tasks, figure dimensions, and font sizes for titles, axis labels,
ticks, legends, and annotations. Plots cover outcomes and cost, task difficulty
by method size and missing proof lines, atomic-operation counts, harness effects,
per-task tokens, resource usage, and tool-call composition. Tool-call categories
are those reported by each harness; reads performed through a shell remain shell
commands. Each plot can be downloaded as SVG, PDF, 300-DPI PNG, or CSV containing
the exact displayed data.

## Maintaining metadata and statistics

Regenerate the task-size columns in the dashboard's
[`task_metadata.csv`](streamlit_app/src/streamlit_app/task_metadata.csv) after
changing reference proofs or task files:

```bash
python3 scripts/update_task_method_sizes.py
```

The updater validates explicit target-function ranges in `solutions/base/`;
update its `TASK_SPECS` when those ranges change. It computes `method_lines`,
`atomic_operations`, and `missing_code_lines` as described in
[TASKS.md](TASKS.md#task-metadata). `scripts/update_task_missing_lines.py` is a
compatibility wrapper for the same updater.

To recompute stored token totals, fixed-price costs, and tool-call counts from
existing sessions, inspect the changes first, then write them:

```bash
python3 scripts/update_run_token_stats.py <run-id> --dry-run
python3 scripts/update_run_token_stats.py <run-id>
```

The script accepts multiple run IDs, JSON filenames, or paths directly under
`runs/`. Shared token pricing and tool categories live in
[`stats_protocol.py`](stats_protocol.py).

## License

Original benchmark infrastructure is licensed under [MIT](LICENSE).
Benchmark tasks and reference proofs retain their original licenses. 
See [TASKS.md](TASKS.md) for source mappings.
