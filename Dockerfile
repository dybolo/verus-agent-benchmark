# Use a Rust base image because Lynette requires Cargo
FROM rust:slim

# Install Python 3, Git, and other necessary utilities
RUN apt-get update && apt-get install -y \
    python3 \
    git \
    curl \
    unzip \
    bash \
    && rm -rf /var/lib/apt/lists/*

# Set up an installation directory outside of the workspace for dependencies
WORKDIR /opt

# Copy the fetch scripts
COPY fetch_vstd.py fetch_verus_release.py ./
# Copy the Lynette source code
COPY lynette/ ./

# Execute the scripts to bake vstd and verus into the Docker image
RUN python3 fetch_verus_release.py

# Add Cargo and Rustup to the PATH
ENV PATH="/usr/local/cargo/bin:/usr/local/rustup/bin:${PATH}"
# Add the downloaded Verus binaries to the system PATH so the agent can just run `verus`
ENV PATH="/opt/.verus:${PATH}"

# fetch_verus_release.py automatically detects and installs the required Rust toolchain

# Add Lynette to the system PATH so the agent can just run `lynette`
RUN ln -s /opt/lynette.py /usr/local/bin/lynette

# Set up the working directory inside the sandbox
WORKDIR /workspace

# Add symbolic link from vstd of the verus release to the working directory
RUN ln -s /opt/.verus/vstd /workspace/vstd
