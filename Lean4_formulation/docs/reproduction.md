# Reproducing the proof audit

## Requirements

Use Git, Bash, Python 3, and [elan](https://github.com/leanprover/elan). Elan selects the compiler specified by this directory's `lean-toolchain`; no global default Lean version is needed when running inside the project. The current compiler is the release candidate `leanprover/lean4:v4.35.0-rc4`.

The project pins mathlib to `49fd9dee36e7bbf345fe7981d2de6aeeb591f75b`. `lake-manifest.json` records its transitive Git revisions. Do not run `lake update` or replace the compiler with a newer version when reproducing this checkpoint.

## Fresh checkout

From the directory containing `lean-toolchain`:

```sh
lake exe cache get
bash check.sh
```

Lake fetches the pinned dependency checkouts as needed. The mathlib cache avoids compiling all foundational library files from scratch. Both operations need network access on a fresh checkout. Proof compilation does not use a remote theorem-proving service.

Successful output ends with:

```text
PASS: 529 theorems in 107 Lean source files; no errors, warnings, placeholders, or custom axioms.
Report: .verification/report.json
```

The report is generated from the current check, not copied from the publication checkpoint. Diagnostics are stored in `.verification/logs/`. These generated files are ignored by Git.

## What the check does

1. Verify hashes against `verification/source-manifest.json`.
2. Run `lake build` for the library entry point.
3. Invoke Lean separately on the root source and every proof module.
4. Reject local placeholder proofs and custom `axiom` or `unsafe` declarations.
5. Match each theorem declaration to its `#print axioms` command and the actual compiler output.
6. Permit only `propext`, `Classical.choice`, and `Quot.sound`; reject `sorryAx`, unexpected axioms, and compiler errors or warnings.
7. Check that all advertised main entry points are present and write a report with source/configuration hashes and actual dependency lists summarized.

The audit script checks the project's current declaration format, in which all result declarations use `theorem`. It is a reproducibility and dependency audit around Lean's typechecker, not an independent replacement for Lean's kernel.

## Checking a single result

After building, for example:

```sh
lake env lean ICLGeneralization/MainInequality.lean
```

The end of that file prints the axiom dependencies of the two main inequality declarations. Checking a single file does not replace the complete project audit.

## Source manifest

The manifest records publishable files by relative path and SHA256, including the historical local verification JSON. Generated logs, caches, and the manifest itself are excluded. Its purpose is to identify this package's contents; editing both a proof and its manifest does not prove anything. A new proof version must be rechecked by Lean.

When deliberately changing the project, follow [CONTRIBUTING.md](../CONTRIBUTING.md). To check the publication files without compiling:

```sh
python3 scripts/source_manifest.py --check
```

## GitHub Actions

The included workflow is configured to run the same audit on Ubuntu on pushes, pull requests, and manual dispatch. Its external actions use explicit Git commit pins. The setup follows the [Lean action's documented configuration](https://github.com/leanprover/lean-action/blob/38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9/README.md).

The workflow is supplied as configuration. A hosted CI success is established only by a completed GitHub run; it is not implied by the local checkpoint.
