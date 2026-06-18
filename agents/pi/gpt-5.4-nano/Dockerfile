FROM benchmark-base:latest

RUN apt-get update && apt-get install -y \
    curl \
    && curl -fsSL https://deb.nodesource.com/setup_20.x | bash - \
    && apt-get install -y nodejs \
    && rm -rf /var/lib/apt/lists/*

RUN npm install -g @earendil-works/pi-coding-agent

# Run the agent and send the session to the session directory
CMD ["/bin/sh", "-c", "pi --model openrouter/gpt-5.4-nano:xhigh --session-dir \"$SESSION\" -p \"$TASK_PROMPT\""]
