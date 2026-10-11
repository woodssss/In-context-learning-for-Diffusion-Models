# Verification checkpoint

The publication package passed its own complete local audit at **2026-10-09 05:11:27 UTC**. The run used this directory's `bash check.sh` and the pinned compiler and dependency revisions.

| Check | Result |
|---|---|
| Library build | PASS |
| All 107 Lean source files independently checked | PASS |
| All 529 theorem declarations matched to dependency output | PASS |
| No compiler errors or warnings | PASS |
| No local incomplete proofs or custom axioms | PASS |
| All advertised main entry points present | PASS |

The compiler was Lean 4.35.0-rc4, commit `c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`, on macOS arm64. Mathlib was pinned to `49fd9dee36e7bbf345fe7981d2de6aeeb591f75b`.

The local project was rebuilt from an empty project build directory. The installed pinned compiler and existing pinned dependency cache were reused; this was not a network-installation test. The copied Lean source files were also compared byte for byte with the previously verified development version. Compiler binaries, dependencies, and generated build files are excluded from the publication package.

The workflow YAML, action commit pins, read-only repository permission, and project-location detection for both standalone and subfolder layouts were checked locally. Documentation links and the publication files were checked for unintended local paths and token strings. These checks do not establish a hosted CI result.

[local-verification.json](../verification/local-verification.json) contains the completed publication check and its source/configuration fingerprints. The definitive evidence is the source and a reproduced Lean run, rather than this prose or a theorem count.

The source/configuration hashes in that report identify the files actually checked. The separate `verification/source-manifest.json` identifies the publishable package contents. Fresh checks write `.verification/report.json` and do not overwrite the historical publication record.

Allowed logical dependencies are `propext`, `Classical.choice`, and `Quot.sound`. ERM existence and the geometric covering condition remain explicit premises as described in [proof-scope.md](proof-scope.md).

GitHub-hosted CI has not been run for this package.
