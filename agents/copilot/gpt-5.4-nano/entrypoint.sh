#!/bin/sh
export COPILOT_PROVIDER_API_KEY="$OPENROUTER_API_KEY"
export COPILOT_HOME="$SESSION"

copilot --autopilot --model gpt-5.4-nano --reasoning-effort xhigh -p "$TASK_PROMPT" \
    --allow-all-tools --allow-all-paths -s
