FROM benchmark-base:latest

RUN apt-get update && apt-get install -y \
    curl \
    && curl -fsSL https://deb.nodesource.com/setup_20.x | bash - \
    && apt-get install -y nodejs \
    && rm -rf /var/lib/apt/lists/*

RUN npm install -g @earendil-works/pi-coding-agent

# Verify pi is installed
RUN which pi && pi --version

# Run pi with the task prompt, using exec so it replaces the shell process
# CMD ["/bin/sh", "-c", "exec pi -p \"$TASK_PROMPT\""]
CMD pi --model openrouter/gpt-5.4-nano -p "$TASK_PROMPT"
#CMD ["pi", "--model", "openrouter/gpt-5.4-nano", "-p", "$TASK_PROMPT"]
