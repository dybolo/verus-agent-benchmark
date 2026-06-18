FROM benchmark-base:latest

# Install Node.js and build tools in one layer
RUN apt-get update && apt-get install -y \
    curl \
    python3-venv \
    build-essential \
    git \
    && rm -rf /var/lib/apt/lists/* \
    && curl -fsSL https://deb.nodesource.com/setup_20.x | bash - \
    && apt-get install -y nodejs

# Global npm dependencies (pi and tree-sitter)
RUN npm install -g --force \
    @earendil-works/pi-coding-agent \
    tree-sitter-cli

# Tree-sitter Verus setup
RUN git clone https://github.com/secure-foundations/tree-sitter-verus.git /opt/tree-sitter-verus \
    && cd /opt/tree-sitter-verus \
    && npm install \
    && tree-sitter generate \
    && tree-sitter build

# tool setup
RUN python3 -m venv /opt/venv
ENV PATH="/opt/venv/bin:$PATH"

COPY semantic-grep/ /opt/semantic-grep/
RUN pip install --upgrade pip && \
    pip install -r /opt/semantic-grep/requirements.txt

# Create wrapper script for the command-line tool, specifying the tree-sitter-verus library path
RUN echo '#!/bin/bash' > /usr/local/bin/semantic_grep && \
    echo 'exec /opt/venv/bin/python3 /opt/semantic-grep/semantic_grep_unified.py --tree-sitter-verus-path "/opt/tree-sitter-verus/verus.so" "$@"' >> /usr/local/bin/semantic_grep && \
    chmod +x /usr/local/bin/semantic_grep

# Set pi extension
RUN mkdir -p /root/.pi/agent/extensions

COPY semantic-grep/semantic-grep-tool.ts /root/.pi/agent/extensions/semantic-grep-tool.ts

CMD ["/bin/sh", "-c", "pi --model openrouter/gpt-5.4-nano:xhigh --session-dir \"$SESSION\" -t read,bash,edit,write,find,ls,semantic_grep -p \"$TASK_PROMPT\""]
