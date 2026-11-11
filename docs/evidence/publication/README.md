# Version 0.1.0 local verification before GitHub publication

Source commit: `645a8115fc81ca12d855a35850aa81c911f16bc1`.
The committed source includes the formalization title, all three authors,
version `0.1.0`, and the intended public repository URL in `CITATION.cff`.
Apache-2.0 applies to code and project documentation outside `paper/`;
the separate manuscript rights notice is retained.

On 11 November 2026, `bash scripts/verify-isolated.sh` completed with exit
code zero after a fresh dependency fetch and build. Both metadata schemas,
the licensing/author consistency checks, source provenance, generated
interface, all nine dependency pins and all 78 selected axiom closures passed.
Comparator matched 25 theorem types and 53 concrete definitions. Lean,
NanoDa and con-ron explicitly accepted; con-ron checked 17,745 declarations.
All 117 committed files matched before and after replay and in the live checkout.

The adjacent reports and logs record this actual local run. The evidence-only
commit adding them does not alter the verified Lean sources or metadata.
GitHub Actions verification is a separate hosted run; use the public workflow
for the exact repository commit. This report does not assert a GitHub release,
Zenodo DOI or Palomar registration.
