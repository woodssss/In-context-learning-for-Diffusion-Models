# Publishing this package

This directory contains the standalone source package. The manuscript, experiments, historical working notes, and dependency binaries are not included.

## Standalone repository

Use the contents of `lean_proof_github/` as the repository root. Include the hidden `.gitignore`, `.gitattributes`, and `.github/` files. The workflow at `.github/workflows/check.yml` will locate the proof project at the repository root.

Run the two reproduction commands before publishing. Commit the Lean sources, pinned Lake configuration, audit tools, documentation, and `verification/` checkpoint files. Keep `.lake/`, `.elan/`, `.cache/`, `.verification/`, and generated logs out of the commit.

## Subfolder of an existing repository

Keep the package at `lean_proof_github/`. GitHub Actions discovers workflows only in the repository root's `.github/workflows/`, so place a copy of this package's `check.yml` there under an unused filename. The supplied workflow detects the `lean_proof_github/` location automatically. This package does not modify an existing repository or replace its workflows.

The nested `.github/workflows/check.yml` remains part of the standalone package; copying it to the outer workflow directory does not require changing the package manifest.

## License and citation metadata

The original proof code, audit tools, and accompanying documentation are distributed under the [MIT License](../LICENSE). Existing dependency licenses remain applicable to their own code. Dependency sources are fetched separately and are not redistributed in this package.

No DOI, release URL, author list, or publication identifier has been invented. When the paper and repository have public identifiers, cite the paper for the mathematical claims and cite a repository release or commit for the formalization. A `CITATION.cff` can then be added using that confirmed metadata.

This packaging step does not create a GitHub repository, upload files, or establish a hosted CI result.
