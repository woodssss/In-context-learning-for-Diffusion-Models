#!/usr/bin/env python3
"""Record or verify SHA256 hashes of the publishable project files."""

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "verification" / "source-manifest.json"
IGNORED_DIRS = {".git", ".lake", ".elan", ".cache", ".verification", "logs", "__pycache__"}
IGNORED_FILES = {"verification/source-manifest.json", ".DS_Store"}


def project_hashes():
    result = {}
    for path in sorted(ROOT.rglob("*")):
        relative = path.relative_to(ROOT)
        if any(part in IGNORED_DIRS for part in relative.parts):
            continue
        name = relative.as_posix()
        if name in IGNORED_FILES or path.name == ".DS_Store":
            continue
        if path.is_symlink():
            raise SystemExit("Unexpected publishable symlink: " + name)
        if path.is_file():
            result[name] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    current = project_hashes()
    if args.write:
        MANIFEST.parent.mkdir(exist_ok=True)
        MANIFEST.write_text(json.dumps({"algorithm": "sha256", "files": current}, indent=2) + "\n")
        print(f"Recorded {len(current)} publishable files.")
        return
    if not MANIFEST.is_file():
        raise SystemExit("Missing source manifest. Run python3 scripts/source_manifest.py --write.")
    recorded = json.loads(MANIFEST.read_text())
    if recorded.get("algorithm") != "sha256":
        raise SystemExit("Unsupported source-manifest algorithm.")
    expected = recorded["files"]
    changed = sorted(name for name in set(current) | set(expected) if current.get(name) != expected.get(name))
    if changed:
        raise SystemExit("Source manifest mismatch:\n" + "\n".join(changed))
    print(f"Source manifest verified: {len(current)} files.")


if __name__ == "__main__":
    main()
