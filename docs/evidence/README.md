# Standalone verification on 11 November 2026

The fresh Linux run verified source commit
`225f3b758cf95ab321c59a33d9b52e26c91eb7d0`. It materialized 75 regular files
from the local Git object database and fetched all nine dependency sources
at their committed public Git revisions. Mathlib's canonical cache supplied
2,024 downloaded and decompressed artifacts. The run used the installed
official Lean 4.35.0-rc2 distribution and Bubblewrap 0.12.0 built from its
pinned upstream commit.

| Check | Observed result |
| --- | --- |
| Committed source bytes | All 75 files matched before and after replay, and the live checkout matched the tested bytes. |
| Lean sources | All 36 source files passed. Challenge contains 25 deliberate statement placeholders. Solution has no proof holes. |
| Generated interface | Challenge and Comparator configuration matched their generator. |
| Metadata | `formalization.yaml` passed the pinned upstream v0.4 schema. `CITATION.cff` passed the pinned official 1.2.0 schema. |
| Paper and proof provenance | All seven recorded manuscript files and 33 copied proof modules matched, as did the recorded PDF identifier in Challenge and formalization metadata. |
| Dependencies | All nine origins and Git revisions matched the manifest. Mathlib's toolchain and inherited dependency pins matched. |
| Complete Lean build | Passed with 2,078 jobs. |
| Selected axiom closures | All 78 passed using only `propext`, `Classical.choice`, and `Quot.sound`. |
| Comparator | Matched all 25 selected theorem types and 53 concrete definitions, with exit code 0. |
| Kernel replay | Lean, NanoDa and con-ron each explicitly accepted. con-ron checked 17,745 declarations. |
| Full verification entry point | Exit code 0, including evidence writing and the two final source comparisons. |

The supplied PDF's SHA-256 is
`37ff1c413e7b088bf4364e64c8886128e5fbc566e3abebb6a59c5c2a79e42672`.
The proof-scope and paper correspondence review are in the coverage and
semantic review documents. [Coverage](../coverage.md)

`source-snapshot.json` records each committed path, Git blob and SHA-256.
`provenance.json` records the exact selected declarations, permitted axioms,
tool versions and hashes, configuration hashes and actual kernel outcomes.
`metadata.json` and `dependencies.json` retain the checked schema digests and
dependency identities. The adjacent logs and comparison reports come from
this run. The checkout retains the original run under
`.lake/verification/run-20261111T040243Z.MwC27bso`.

This run took place locally in Linux under WSL. The GitHub Actions workflow
uses the same entry point and has been reviewed statically. Hosted execution
is pending a future hosted checkout. The evidence can be added in a separate
local commit while keeping the tested source commit fixed.
