# Benchmark repo for verus-based agents

## Requirements

- python 3.14
- docker

## Adding Agents

- Add a new agent by creating a new directory under `agents/` and adding a Dockerfile that defines the agent's environment.

## Important

- The script uses the user current environment variables for provider credentials.
- Make sure to run the agents with a provider with the credentials set in the environment.
