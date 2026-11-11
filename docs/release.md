# Release and archival checklist

## Decisions before publication

- Approve licences for the new code/documentation and for `paper/`; retain the scoped Apache notice. See [licensing status](../LICENSE_STATUS.md).
- Confirm the formalization author list in `CITATION.cff` and `formalization.yaml`. The current entry preserves the earlier formalization's attribution to Hossein Vahidi; manuscript authorship remains Gupta, Suomela and Vahidi. AI assistance is disclosed separately.
- Approve the coverage description, including the scalar-message theorem, shared codec premise, finite classical public choices, and the explicit rounding/output-balancing variants. A fully composed bit-vector implementation is not claimed. If the release is to advertise complete formal verification of that representation, finish the encoded-program and bit-budget bridge first; otherwise keep the scalar/encoding qualification in the public claim.
- Choose the public repository owner, release version and tag. The requested repository name is `lean-sparse-mm`; no public repository or release is created by this local preparation.
- Review the final snapshot and its mechanical evidence. Run the Actions workflow on the exact public commit after publishing; a prepared workflow is not a successful hosted CI run.

## Later GitHub-Zenodo steps

1. After authorization, publish this focused repository and ensure its verification workflow passes on the intended release commit. Include the current paper and citation metadata in that commit.
2. Link the owner's GitHub account to Zenodo and enable this repository in the GitHub integration. Check the configured permissions and repository selection using [Zenodo's enablement guide](https://help.zenodo.org/docs/github/enable-repository/).
3. Follow the current [release archival guide](https://help.zenodo.org/docs/github/archive-software/github-upload/) to archive the approved GitHub release. Check the resulting Zenodo record, creators, licences, tag, commit and included files before citing it. Do not treat a draft or failed integration as a published archive.
4. Record the actual version DOI, concept DOI and landing page after Zenodo assigns them. Keep the verified release tag immutable. Update future metadata or repository documentation without silently changing an already cited source snapshot.
5. In arXiv, cite the exact archived version used for verification, with the repository release tag and source commit. [Zenodo recommends a version DOI for reproducibility](https://zenodo.org/help/versioning); a concept DOI refers to the evolving collection of versions.

Suggested citation form, to fill only after approval and archival:

> Confirmed formalization authors. *lean-sparse-mm: Lean companion for sparse matrix multiplication*. Release TAG, source commit COMMIT. Zenodo. ACTUAL VERSION DOI.

The capitalized fields above are instructions, not assigned identifiers. Copy the final citation from the actual Zenodo landing page and verify its metadata. Cite the manuscript separately when discussing the mathematical result.

Palomar submission, editorial review and registration are separate optional actions; local Comparator/kernel acceptance is not a registry entry.
