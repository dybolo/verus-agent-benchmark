# Benchmark repo for verus-based agents

## Requirements

- python 3.14
- docker

## Adding Agents

- Add a new agent by creating a new directory under `agents/<agent_name>/<model_name>/` and adding a Dockerfile that defines the agent's environment. The `<model_name>` should just be the model identifier (e.g. `gpt-5.4-nano`) keeping any provider prefix inside the Dockerfile (e.g. `--model openrouter/gpt-5.4-nano`).
- The prompt of the agent is stored in the `TASK_PROMPT` environment variable inside the container
- The file to store the exported session is given by the `SESSION` environment variable

## Important

- The script uses the user current environment variables for provider credentials.
- Make sure to run the agents with a provider with the credentials set in the environment.
