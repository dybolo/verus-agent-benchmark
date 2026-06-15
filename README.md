# Benchmark repo for verus-based agents

## Requirements

- python 3.14
- docker

## Adding Agents

- Add a new agent by creating a new directory under `agents/<agent_name>/<model_name>/` and adding a Dockerfile that defines the agent's environment. The `<model_name>` should just be the model identifier (e.g. `gpt-5.4-nano`) keeping any provider logic inside the Dockerfile (e.g. `--model openrouter/gpt-5.4-nano`).
- The prompt to give the agent is stored in the `TASK_PROMPT` environment variable inside the container.
- The directory to save sessions to is given by the `SESSION` environment variable inside the container.
- A `statistics.py` file must be placed at `agents/<agent_name>/statistics.py`to retrieve information from each agent specific session format. It receives a path to a session directory and returns a JSON dict containing the session's token usage, cost, turn count, tool calls, duration, etc.

## How to run

- Run the benchmark with `python3 benchmark.py`.
- Use the `-j` flag to set the number of parallel workers (defaults to the number of CPU cores).

## Important

- The script uses the user current environment variables for provider credentials.
- Make sure to run the agents with a provider with the credentials set in the environment.
