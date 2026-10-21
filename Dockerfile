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
# fetch_verus_release.py automatically detects and installs the required Rust toolchain
ARG VERUS_VERSION=latest
RUN python3 fetch_verus_release.py --version "$VERUS_VERSION"

# remove examples from verus (some tasks are removed from there)
RUN rm -rf /opt/.verus/examples

# Add Cargo and Rustup to the PATH
ENV PATH="/usr/local/cargo/bin:/usr/local/rustup/bin:${PATH}"
# Add the downloaded Verus binaries to the system PATH so the agent can just run `verus`
ENV PATH="/opt/.verus:${PATH}"

# Add Lynette to the system PATH so the agent can just run `lynette`
RUN ln -s /opt/lynette.py /usr/local/bin/lynette

# Set up the working directory inside the sandbox
WORKDIR /workspace

# Add symbolic link from vstd of the verus release to the working directory
RUN ln -s /opt/.verus/vstd /workspace/vstd

# Give agents access to needed folders
RUN chmod -R a+rwX /opt /workspace /root
