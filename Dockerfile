# Use a Rust base image because Lynette requires Cargo
FROM rust:latest

# Install Python 3, Git, and other necessary utilities
RUN apt-get update && apt-get install -y \
    python3 \
    git \
    curl \
    unzip \
    bash \
    && rm -rf /var/lib/apt/lists/*

# Set up the working directory inside the sandbox
WORKDIR /workspace

# Copy the fetch scripts and the lynette directory
COPY fetch_vstd.py fetch_verus_release.py ./
COPY lynette/ ./lynette/

# Execute the scripts to bake vstd and verus into the Docker image
RUN python3 fetch_vstd.py
RUN python3 fetch_verus_release.py

# Add Cargo and Rustup to the PATH
ENV PATH="/usr/local/cargo/bin:/usr/local/rustup/bin:${PATH}"
# Add the downloaded Verus binaries to the system PATH so the agent can just run `verus`
ENV PATH="/workspace/.verus:${PATH}"

# Keep the container running for the agent
CMD ["/bin/bash", "-i"]
