#!/usr/bin/env python3.14

import argparse
import os
import stat
import json
import subprocess
import urllib.request
from urllib.parse import quote
import platform
import shutil
import zipfile
from pathlib import Path

def get_platform_info():
    sys_name = platform.system().lower()
    if sys_name == "darwin":
        os_name = "macos"
    elif sys_name == "linux":
        os_name = "linux"
    elif sys_name == "windows":
        os_name = "win"
    else:
        raise ValueError(f"Unsupported OS: {sys_name}")

    machine = platform.machine().lower()
    if machine in ["x86_64", "amd64"]:
        arch = "x86"
    elif machine in ["arm64", "aarch64"]:
        arch = "arm64"
    else:
        raise ValueError(f"Unsupported architecture: {machine}")

    return os_name, arch

def get_rust_host_triple():
    machine = platform.machine().lower()
    if machine in ["x86_64", "amd64"]:
        arch = "x86_64"
    elif machine in ["arm64", "aarch64"]:
        arch = "aarch64"
    else:
        raise ValueError(f"Unsupported architecture: {machine}")

    sys_name = platform.system().lower()
    if sys_name == "linux":
        return f"{arch}-unknown-linux-gnu"
    elif sys_name == "darwin":
        return f"{arch}-apple-darwin"
    elif sys_name == "windows":
        return f"{arch}-pc-windows-msvc"
    else:
        raise ValueError(f"Unsupported OS: {sys_name}")

def install_required_toolchain(release_data):
    tag = release_data.get('tag_name')
    if tag:
        url = f"https://raw.githubusercontent.com/verus-lang/verus/{tag}/rust-toolchain.toml"
    else:
        url = "https://raw.githubusercontent.com/verus-lang/verus/main/rust-toolchain.toml"

    print(f"Fetching rust-toolchain.toml...")
    req = urllib.request.Request(url, headers={'User-Agent': 'Verus-Benchmark-Agent'})

    try:
        with urllib.request.urlopen(req) as response:
            content = response.read().decode()
    except Exception as e:
        print(f"Warning: Could not fetch rust-toolchain.toml: {e}")
        return

    channel = None
    for line in content.splitlines():
        line = line.strip()
        if line.startswith("channel"):
            channel = line.split("=", 1)[1].strip().strip('"').strip("'")
            break

    if not channel:
        print("Warning: Could not parse channel from rust-toolchain.toml")
        return

    host_triple = get_rust_host_triple()
    toolchain = f"{channel}-{host_triple}"

    print(f"Installing required Rust toolchain: {toolchain}...")
    result = subprocess.run(["rustup", "install", toolchain], capture_output=True, text=True)
    if result.returncode == 0:
        print(result.stdout.strip())
    else:
        print(f"Warning: Failed to install toolchain: {result.stderr.strip()}")

def fetch_latest_verus_release():
    """Download the latest Verus release for the current platform."""
    fetch_verus_release()


def fetch_verus_release(version=None):
    """Download a Verus release by its exact GitHub tag, or latest if omitted."""
    target_dir = Path(".verus")

    os_name, arch = get_platform_info()
    search_str = f"{arch}-{os_name}.zip"
    print(f"Detected platform: {os_name}, architecture: {arch}")

    version = version or "latest"
    print(f"Fetching release information for {version}...")
    endpoint = "latest" if version == "latest" else f"tags/{quote(version, safe='')}"
    api_url = f"https://api.github.com/repos/verus-lang/verus/releases/{endpoint}"
    req = urllib.request.Request(api_url, headers={'User-Agent': 'Verus-Benchmark-Agent'})

    try:
        with urllib.request.urlopen(req) as response:
            release_data = json.loads(response.read().decode())
    except Exception as e:
        raise RuntimeError(f"Could not fetch Verus release {version}: {e}") from e

    download_url = None
    for asset in release_data.get('assets', []):
        if search_str in asset['name']:
            download_url = asset['browser_download_url']
            break

    if not download_url:
        print(f"Error: Could not find a release asset matching '{search_str}'")
        print("Available assets:")
        for asset in release_data.get('assets', []):
            print(f" - {asset['name']}")
        raise RuntimeError(f"Verus release {version} has no asset for {arch}-{os_name}")

    if target_dir.exists():
        print(f"Removing existing {target_dir} directory...")
        shutil.rmtree(target_dir)

    target_dir.mkdir(parents=True, exist_ok=True)

    zip_path = target_dir / "verus_release.zip"
    print(f"Downloading {download_url}...")

    # Simple download with urllib
    urllib.request.urlretrieve(download_url, zip_path)

    print(f"Extracting to {target_dir}...")
    with zipfile.ZipFile(zip_path, 'r') as zip_ref:
        zip_ref.extractall(target_dir)

    zip_path.unlink() # clean up the zip file

    # If the zip extracted a single folder (e.g., verus-1.0-arm64-macos), move contents up one level
    extracted_items = list(target_dir.iterdir())
    if len(extracted_items) == 1 and extracted_items[0].is_dir():
        inner_dir = extracted_items[0]
        for item in inner_dir.iterdir():
            shutil.move(str(item), str(target_dir))
        inner_dir.rmdir()

    # Make binaries executable on macos/linux
    if os_name in ["macos", "linux"]:
        print("Setting executable permissions...")
        for root, _, files in os.walk(target_dir):
            for file in files:
                # Assuming binaries don't have extensions on unix, or checking specific known names
                if not file.endswith((".txt", ".md", ".zip")):
                    file_path = Path(root) / file
                    st = os.stat(file_path)
                    os.chmod(file_path, st.st_mode | stat.S_IEXEC)

    install_required_toolchain(release_data)

    print(f"Successfully downloaded and extracted Verus to ./{target_dir}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Download a Verus release")
    parser.add_argument(
        "--version", default="latest", help="Exact GitHub release tag (default: latest)"
    )
    args = parser.parse_args()
    try:
        fetch_verus_release(args.version)
    except RuntimeError as e:
        parser.exit(1, f"Error: {e}\n")
