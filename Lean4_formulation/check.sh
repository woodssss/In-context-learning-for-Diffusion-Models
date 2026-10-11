#!/usr/bin/env bash
set -euo pipefail

PROOF_ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$PROOF_ROOT"
for program in lake python3; do
  if ! command -v "$program" >/dev/null 2>&1; then
    echo "Missing prerequisite: $program. See docs/reproduction.md." >&2
    exit 1
  fi
done

python3 scripts/source_manifest.py --check
mkdir -p .verification/logs
echo "Building the pinned Lean project..."
if ! lake build > .verification/logs/build.log 2>&1; then
  cat .verification/logs/build.log
  exit 1
fi

echo "Checking every source file and printing theorem dependencies..."
for source in ICLGeneralization.lean ICLGeneralization/*.lean; do
  module="$(basename "$source" .lean)"
  if ! lake env lean "$source" > ".verification/logs/$module.log" 2>&1; then
    cat ".verification/logs/$module.log"
    exit 1
  fi
done
python3 scripts/audit.py

