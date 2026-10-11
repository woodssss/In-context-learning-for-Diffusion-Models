#!/usr/bin/env python3
"""Audit the fresh Lean diagnostics and record a path-independent report."""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / ".verification" / "logs"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED = {
    "lemma_one_transformer_realization",
    "lemma_two_uniform_time_original",
    "lemma_two_uniform_time_rate",
    "lemma_three_uniform_time_original",
    "lemma_four_fixed_uniform_time",
    "lemma_five_complete",
    "proposition_one_uniform_time",
    "main_generalization_error_inequality",
}


def main():
    sources = [ROOT / "ICLGeneralization.lean", *sorted((ROOT / "ICLGeneralization").rglob("*.lean"))]
    build_log = (LOGS / "build.log").read_text()
    if re.search(r"sorryAx|\berror:|\bwarning:", build_log):
        raise SystemExit("Unexpected diagnostic in the project build log.")
    total = 0
    names = set()
    used_axioms = set()
    hashes = {}
    for path in sources:
        relative = path.relative_to(ROOT).as_posix()
        source = path.read_text()
        hashes[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
        if re.search(r"\b(sorry|admit|axiom|unsafe)\b", source):
            raise SystemExit("Untrusted placeholder or declaration in " + relative)
        declarations = re.findall(r"^theorem\s+([A-Za-z0-9_]+)", source, re.M)
        prints = re.findall(r"^#print axioms\s+([A-Za-z0-9_]+)", source, re.M)
        if len(prints) != len(declarations) or set(prints) != set(declarations):
            raise SystemExit("Incomplete source-level dependency audit in " + relative)
        log = (LOGS / (path.stem + ".log")).read_text()
        if re.search(r"sorryAx|\berror:|\bwarning:", log):
            raise SystemExit("Unexpected Lean diagnostic in " + relative)
        audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
        if len(audits) != len(declarations):
            raise SystemExit("Missing dependency output in " + relative)
        audited = set()
        for theorem, axioms in audits:
            short_name = theorem.rsplit(".", 1)[-1]
            if short_name in audited:
                raise SystemExit("Duplicate dependency output: " + theorem)
            audited.add(short_name)
            used = {item.strip() for item in axioms.split(",") if item.strip()}
            if not used <= ALLOWED:
                raise SystemExit("Unexpected dependencies for " + theorem + ": " + ", ".join(sorted(used - ALLOWED)))
            used_axioms.update(used)
        if audited != set(declarations):
            raise SystemExit("Dependency names do not match declarations in " + relative)
        names.update(declarations)
        total += len(declarations)
    if not REQUIRED <= names:
        raise SystemExit("Missing public entry points: " + ", ".join(sorted(REQUIRED - names)))
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    tree_hash = hashlib.sha256(json.dumps(hashes, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    config_hashes = {
        name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
    }
    compiler = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=ROOT, text=True).strip()
    report = {
        "result": "PASS",
        "finished_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "compiler": compiler,
        "mathlib_revision": mathlib["rev"],
        "source_files_checked": len(sources),
        "theorem_declarations_audited": total,
        "allowed_axioms": sorted(ALLOWED),
        "observed_axioms": sorted(used_axioms),
        "source_tree_sha256": tree_hash,
        "configuration_sha256": config_hashes,
        "source_sha256": hashes,
        "entry_points_checked": sorted(REQUIRED),
        "checks": {
            "project_build": "PASS",
            "every_source_typechecked": "PASS",
            "no_local_placeholders_or_custom_axioms": "PASS",
            "every_theorem_dependency_audited": "PASS",
            "no_compiler_errors_or_warnings": "PASS",
        },
    }
    output = ROOT / ".verification" / "report.json"
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: {total} theorems in {len(sources)} Lean source files; no errors, warnings, placeholders, or custom axioms.")
    print("Report: .verification/report.json")


if __name__ == "__main__":
    main()

