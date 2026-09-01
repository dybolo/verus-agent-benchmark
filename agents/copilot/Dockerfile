FROM benchmark-base:latest

RUN apt-get update && apt-get install -y \
    curl \
    python3-pip \
    && curl -fsSL https://deb.nodesource.com/setup_24.x | bash - \
    && apt-get install -y nodejs \
    && rm -rf /var/lib/apt/lists/*

RUN python3 -m pip install --break-system-packages \
   'litellm[proxy]' \
   'fastapi==0.140.0' \
   'boto3>=1.28.57'

RUN npm install -g @github/copilot
