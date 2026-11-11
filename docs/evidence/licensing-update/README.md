# Licensing and attribution update verification

The local source snapshot `91d3021c8e5c5b231a8fda96e9a6500f24ba844f`
was verified on 11 November 2026 by `bash scripts/verify-isolated.sh`.
A fresh Linux directory materialized all 97 committed files, fetched all nine
pinned public Git dependencies and the canonical Mathlib cache, and ran the
complete verification workflow. `run-status.txt` records exit code zero.

## Confirmed scope and metadata

- The root `LICENSE` is the unchanged Apache-2.0 text and matches the retained
  standard licence copy. `CITATION.cff` and `formalization.yaml` identify that
  code licence consistently.
- All contents of `paper/` are explicitly excluded. `paper/LICENSE` retains
  the manuscript authors' copyright and grants no CC licence or purported
  arXiv distribution terms.
- Both repository metadata files credit Chetan Gupta, Jukka Suomela and
  Hossein Vahidi in that order. Hossein Vahidi remains the maintainer.
  AI assistance and actual review status are recorded separately.
- The original PDF, LaTeX files, bibliography, all Lean sources and the
  Comparator selection were unchanged by the licensing update.

## Observed checks

The pinned formalization and CFF schemas, paper/proof provenance, root licence,
explicit manuscript exclusion and author consistency checks passed. The build,
source discipline and generated-interface checks passed. All 78 selected axiom
closures use only `propext`, `Classical.choice` and `Quot.sound`.

Comparator matched all 25 theorem statements and 53 concrete definitions.
Lean, NanoDa and con-ron each explicitly accepted the solution; con-ron
checked 17,745 declarations with `--verified`. Both final byte comparisons
passed for all 97 committed files. The retained Comparator log matches its
recorded SHA-256.

`source-snapshot.json` and `provenance.json` identify the exact commit, file
hashes, declaration selection, configuration and verifier hashes. `metadata.json`
contains the new licensing/credit checks. Adjacent logs are from this actual
run. Earlier evidence in the parent directory remains historical evidence for
its own recorded snapshot.

This verification is local; it is not a hosted CI run, publication, release,
Palomar registration or Zenodo deposit. The paper's eventual arXiv submission
licence is still to be recorded when actually chosen. Mathematical coverage
and representation qualifications remain those in `docs/coverage.md`.
