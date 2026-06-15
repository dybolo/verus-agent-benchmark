FROM benchmark-base:latest

ENV COPILOT_PROVIDER_BASE_URL=https://openrouter.ai/api/v1
ENV COPILOT_PROVIDER_TYPE=openai
ENV COPILOT_MODEL=gpt-5.4-nano

RUN apt-get update && apt-get install -y \
    curl \
    && curl -fsSL https://deb.nodesource.com/setup_20.x | bash - \
    && apt-get install -y nodejs \
    && rm -rf /var/lib/apt/lists/*

RUN npm install -g @github/copilot

COPY entrypoint.sh /entrypoint.sh
RUN chmod +x /entrypoint.sh
CMD ["/entrypoint.sh"]
