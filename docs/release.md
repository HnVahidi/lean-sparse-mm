# Release and archive

## Confirmed licensing and credit

- Apache-2.0 applies to the code, scripts and project documentation outside `paper/`, subject to retained third-party notices.
- The manuscript files in `paper/` retain the authors' copyright and are governed by the separate rights notice. [Manuscript rights](../paper/LICENSE)
- The formalization authors are Chetan Gupta, Jukka Suomela and Hossein Vahidi, in manuscript order. Hossein Vahidi maintains the repository. [Formalization and AI disclosure](../formalization.yaml)

## Version 1.0.0

GitHub released the verified source and Zenodo archived it on 11 November 2026.

| Record | Value |
| --- | --- |
| GitHub release | [`v1.0.0`](https://github.com/HnVahidi/lean-sparse-mm/releases/tag/v1.0.0) |
| Source commit | [`76a5a6a73fdc9f3f1fe02d1d2e4664d4f802467d`](https://github.com/HnVahidi/lean-sparse-mm/commit/76a5a6a73fdc9f3f1fe02d1d2e4664d4f802467d) |
| Verification | [Successful GitHub Actions run 42969947794](https://github.com/HnVahidi/lean-sparse-mm/actions/runs/42969947794) |
| Zenodo version DOI | [`10.5281/zenodo.24127515`](https://doi.org/10.5281/zenodo.24127515) |
| Zenodo concept DOI | [`10.5281/zenodo.24127514`](https://doi.org/10.5281/zenodo.24127514) |
| Archive ZIP | `HnVahidi/lean-sparse-mm-v1.0.0.zip`, 814,910 bytes |
| ZIP SHA-256 | `bdd86815626022127b495f6d45a73e0d343dc7adda57ead38ecfefed4fe2ecf8` |
| ZIP MD5 | `6c08becea78e002449765c39df5a72ab` |

All 137 file paths and file contents in the downloaded ZIP matched the Git
snapshot at the release commit. The `v1.0.0` tag identifies those archived bytes.
The citation metadata on `main` records the DOI assigned after archival.
[Zenodo record and archive](https://zenodo.org/records/24127515)

The release proves the scalar-message theorem with the paper's shared codec
premise for its bit interpretation. The coverage audit records the finite public
choices and the rounding and output-assignment variants. [Coverage audit](coverage.md)

## Citation

> Chetan Gupta, Jukka Suomela, and Hossein Vahidi. (2026). *lean-sparse-mm: Lean companion for sparse matrix multiplication* (Version 1.0.0) [Software]. Zenodo. [10.5281/zenodo.24127515](https://doi.org/10.5281/zenodo.24127515)

Use the version DOI for the exact snapshot. The concept DOI identifies the
collection of versions. Cite the manuscript separately for its mathematical
results. Record its arXiv identifier and licence once issued.
[Zenodo versioning guide](https://zenodo.org/help/versioning)

## Future versions

1. Keep the existing release tags and archived files fixed. Prepare a new version on `main` and update the package and citation versions.
2. Remove or replace the previous version's DOI and release date when preparing a different version; do not present the old version DOI as the new archive's identifier.
3. Check the exact candidate commit with the verification workflow. Confirm that this GitHub repository remains enabled in Zenodo before publishing its new release.
4. After archival, verify the creators, licence scope, version, file checksums and new version DOI. Record that DOI in the current citation metadata.

Palomar submission and registration remain separate actions; neither the GitHub release nor the Zenodo DOI is a Palomar registration.
