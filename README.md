# lean-sparse-mm

Lean companion to **Sparse Matrix Multiplication Exponent 1.5 in the Low-bandwidth Model**, by Chetan Gupta, Jukka Suomela, and Hossein Vahidi.

Read the [paper](paper/sparse-mm.pdf), the [coverage audit](docs/coverage.md), and the [verification report](docs/verification.md). This repository is a local release candidate. Publication awaits the decisions in the [release checklist](docs/release.md); no public repository, release, DOI, or Palomar entry is asserted.

## Scope

The main result is an actual deterministic, five-phase sparse matrix multiplication protocol over arbitrary semirings, with public allowed input masks, public requested output mask and initial holders. One program and balanced output assignment are chosen before all numerical inputs. Each machine sends and receives at most one scalar per round. With initial load at most `K*d`, the proved finite bound is at most `(8*K+80)*d*sqrt(d)` rounds, for fixed `K`.

The source paper assumes that transmitted inputs, products and partial sums admit one-word encodings. `Main.lean` is a scalar-message theorem; `Wire.lean` proves per-round preservation under a shared codec correct on the values actually sent. A complete encoded bit-vector program is not asserted. The correspondence audit distinguishes this conditional model interpretation from exact finite statements.

Integer teams use `h = Nat.sqrt d + 1`, clusters have `d*h` positions, and public batch permutations replace the paper's sorted cyclic output assignment. The toolbox includes exact regular-load redistribution, pipelined broadcast/aggregation, Boolean AND/OR systems, and adaptive broadcast/aggregation lower bounds. See the coverage table for exact types and differences. Contextual bounds from cited papers and triangle-coverage remarks are outside the advertised formal results.

## Contents

- `Challenge.lean`: independently readable statement/model interface.
- `Solution.lean`, `SparseMM/`: complete project-specific proofs and local execution models.
- `comparator.json`: every advertised main and toolbox interface selected for comparison.
- `paper/`: matching PDF, complete active LaTeX sources, bibliography and inline figures.
- `docs/`: coverage, source provenance, correspondence review, verification and release guidance.
- `scripts/`, `.github/workflows/`: reproducible checks and fail-on-error CI.
- `CITATION.cff`, `NOTICE.md`, `LICENSE_STATUS.md`: citation draft and scoped attribution/licensing.

## Verify

Use Linux, or Linux under WSL. The pinned `lean-toolchain` selects Lean 4.35.0-rc2; `lake-manifest.json` fixes all standard dependencies. Follow [docs/verification.md](docs/verification.md) for the exact prerequisites and commands, including the required Bubblewrap version and fresh-checkout procedure. The documented verification entry point and GitHub Actions run the same checks.

After installing the prerequisites and committing the source, run the complete gate:

```sh
bash scripts/verify-isolated.sh
```

Ordinary proof builds use:

```sh
lake exe cache get
lake build
```

A build alone is not the full verification. Required checks also compare the Challenge and Solution, inspect every advertised declaration's axiom closure, validate metadata and paper provenance, and replay through Lean, NanoDa and con-ron. Solution proofs may use only `propext`, `Classical.choice`, and `Quot.sound`. Challenge statement placeholders are intentionally isolated from Solution.

## Provenance and citation

The included manuscript sources are from revision `678f50ee1fd6c1f97ab92062f965063be28015af`; the supplied PDF is identified separately by its SHA-256 in [docs/source-provenance.json](docs/source-provenance.json). The mathematical Lean development originates at revision `8badbe471000b4e0f63d2e40b1ee784cb74c4556`, with prior evidence at `3ac917835b35e7b1d4b66f758f1b2a37a7f78826`. No sibling checkout or private source is required to build this package.

For archival citation, use the DOI of the exact verified Zenodo release once it exists, as described in [docs/release.md](docs/release.md). The current `CITATION.cff` preserves the existing formalization attribution pending author confirmation. AI assistance is recorded in `formalization.yaml`; automated checks and agent review are not human peer review or Palomar registration.

Licensing for the new formalization and manuscript remains undecided. The retained Apache-2.0 licence applies only to the reused material identified in `NOTICE.md`.
