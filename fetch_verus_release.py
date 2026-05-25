#!/usr/bin/env python3.14

import os
import stat
import json
import urllib.request
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

def fetch_latest_verus_release():
    target_dir = Path(".verus")

    os_name, arch = get_platform_info()
    search_str = f"{arch}-{os_name}.zip"
    print(f"Detected platform: {os_name}, architecture: {arch}")

    print("Fetching latest release information...")
    api_url = "https://api.github.com/repos/verus-lang/verus/releases/latest"
    req = urllib.request.Request(api_url, headers={'User-Agent': 'Verus-Benchmark-Agent'})

    try:
        with urllib.request.urlopen(req) as response:
            release_data = json.loads(response.read().decode())
    except Exception as e:
        print(f"Error fetching release data: {e}")
        return

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
        return

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

    print(f"Successfully downloaded and extracted Verus to ./{target_dir}")

if __name__ == "__main__":
    fetch_latest_verus_release()
