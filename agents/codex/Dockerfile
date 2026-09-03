FROM benchmark-base:latest

RUN apt-get update && apt-get install -y curl \
    && curl -fsSL https://deb.nodesource.com/setup_24.x | bash - \
    && apt-get install -y nodejs \
    && apt-get install -y jq \
    && apt-get purge -y curl wget \
    && apt-get autoremove -y \
    && rm -rf /var/lib/apt/lists/*

RUN npm i -g @openai/codex

# Codex's command runner uses a restricted PATH that retains /usr/local/bin
# but drops the base image's /opt/.verus and /usr/local/cargo/bin entries.
# Keep the Rust environment available normally, and restore the PATH through
# a shared launcher when commands run under Codex.
ENV RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo

RUN <<'EOF'
set -eu

cat > /usr/local/bin/rust-launcher <<'SCRIPT'
#!/bin/sh
set -eu

export PATH="/usr/local/cargo/bin:/usr/local/rustup/bin:/opt/.verus:${PATH}"

case "$(basename "$0")" in
  verus) exec /opt/.verus/verus "$@" ;;
  cargo) exec /usr/local/cargo/bin/cargo "$@" ;;
  *)     exit 1 ;;
esac
SCRIPT

chmod 755 /usr/local/bin/rust-launcher
ln -s rust-launcher /usr/local/bin/verus
ln -s rust-launcher /usr/local/bin/cargo
EOF
