# Palomar conventions used here

The project uses the ordinary root layout described by Palomar. Its concrete
statement interface is `Challenge.lean`, with Mathlib imports and one deliberate
placeholder per selected theorem. `Solution.lean` imports the proof development.
`comparator.json` fixes the selected declarations and permits the three standard
Lean axioms. The checked-in configuration uses submitter fields. The verifier
generates its local kernel configuration from that file and the pinned Lean
distribution. [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406)

On 11 November 2026 the minimum listed Lean release was `v4.35.0-rc2`. This
repository uses that release and Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, whose toolchain matches. The root
manifest records exact public Git commits for the dependency closure. Source
checks enforce the module header and physical line limits. The Challenge
stays within the policy's 1,000-line and 100 KiB limits. [Supported toolchains](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/toolchains.json) · [Policy sections 2.1–2.4](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md#2-prepare-an-ordinary-submission)

The template's local workflow uses Comparator and the independent kernels
bundled with Lean. This project also requires con-ron acceptance. Palomar's
registry policy requires Lean and NanoDa and treats recognized con-ron support
or capacity declines separately. The local reports record the particular
executables and checks that ran. The workflow pins checkout, Lean Action and
artifact upload to the template's immutable action revisions, and builds
Bubblewrap 0.12.0 from commit `2a76602a8c71f36c1527cf9fc3417d9149822e0c`.
[Template workflow](https://github.com/PalomarRegistry/PalomarTemplate/blob/2891de4c48955af824969a263d31b25e7a9a1406/.github/workflows/ci.yml) · [Policy section 5](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md#5-what-mechanical-verification-establishes)

The current deliverable is a local companion. Registry submission would need a
public repository, authorization for that submission, and a recognized root
licence matching the metadata. The licence choice is open and recorded in
`LICENSE_STATUS.md`. Local schema validation and proof replay are independent of
that release decision. [Policy sections 2.5 and 4](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md#25-repository-licence)
