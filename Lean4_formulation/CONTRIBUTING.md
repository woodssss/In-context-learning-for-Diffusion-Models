# Updating the formalization

Use the pinned compiler and mathlib revisions. Keep the statement, prerequisites, and paper correspondence clear when changing a theorem. All local result declarations currently use `theorem` and have a matching `#print axioms` command in the same module.

After intentional source or documentation changes:

```sh
python3 scripts/source_manifest.py --write
bash check.sh
```

Review changed theorem premises and proof dependencies, not only the number of declarations. Document changes in `docs/proof-scope.md` and `docs/paper-correspondence.md` if the model or result changes. A successful hash check alone is not a proof.

Do not replace `verification/local-verification.json` with a new result unless intentionally updating the publication checkpoint after a complete successful audit. Fresh audit output belongs in the ignored `.verification/` directory. If a checkpoint is updated, also update `docs/verification.md` and regenerate the publication manifest.

The project accepts only the standard dependency set `propext`, `Classical.choice`, and `Quot.sound`; incomplete proofs, new custom axioms, or compiler warnings should be resolved before a checkpoint is published.
