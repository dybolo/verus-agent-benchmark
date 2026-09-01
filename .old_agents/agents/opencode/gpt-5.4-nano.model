#!/bin/bash
set -e

export XDG_DATA_HOME=$SESSION

opencode run --dangerously-skip-permissions --format json \
    -m openrouter/openai/gpt-5.4-nano --variant xhigh "$TASK_PROMPT" \
    > "$SESSION/session.jsonl"
