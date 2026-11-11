# Verification

The local entry point and the GitHub Actions job verify the same committed
source. They fetch the pinned dependency sources and the Mathlib cache for
the imported modules into a fresh Linux directory. Use a Linux filesystem
for the temporary build, including when the checkout is on Windows under WSL.

Install Git, Bash, Python 3.11 or newer with `PyYAML` and `jsonschema`, and Lean
via [Elan](https://github.com/leanprover/elan). From the repository root,
install the release named in `lean-toolchain`.

```bash
elan toolchain install "$(cat lean-toolchain)"
```

The verifier needs Bubblewrap 0.12.0 or newer with working Linux namespaces.
To build the version used by CI, install a C compiler, Meson, Ninja, pkg-config,
and the libcap development headers. The installer fetches Bubblewrap 0.12.0
at its pinned Git commit and puts the resulting executable in the directory
you name.

```bash
bash scripts/install-bubblewrap.sh .lake/tools/bin
export PATH="$PWD/.lake/tools/bin:$PATH"
```

Commit the tracked changes, then run the full gate from the repository root.

```bash
bash scripts/verify-isolated.sh
```

The gate reads the regular Git blobs at `HEAD` and checks the copied bytes
against a source manifest. It checks Lean source discipline and regeneration
of the selected Challenge and Comparator interface, validates the two pinned
metadata schemas, checks the recorded paper, proof and attribution files, and
checks the Apache-2.0 code licence, explicit paper/ exclusion and consistent
formalization/source author lists.
Lake materializes the existing manifest. The gate checks each dependency's
origin and revision, checks tracked source cleanliness, and verifies Mathlib's
toolchain and inherited pins. It fetches cache data for the declared Mathlib
imports from the canonical upstream cache and builds the complete project.

The axiom audit covers each selected theorem and definition from
`comparator.json`. Comparator exports the selected Challenge and Solution
interfaces separately and compares them. The gate requires explicit acceptance
from the bundled Lean kernel, NanoDa and con-ron, as well as successful evidence
writing. It checks all committed source bytes again after replay. Deliberate
Challenge placeholders belong to the statement interface.

Each invocation writes its result and available logs to a distinct
`.lake/verification/run-*` directory. `source-snapshot.json` records every
checked Git blob and file SHA-256. `provenance.json` records the commit, exact
selected names, executable basenames and hashes, compiler and sandbox versions,
the submitted and effective configuration hashes, and the Comparator outcome.
The effective configuration is generated in the temporary verification directory
using the installed tool paths. The retained report uses executable names so
it can be read independently of the machine that ran the check. Inspect
`run-status.txt`, `output-comparison.json`, and `live-comparison.json` together
with the kernel report. The temporary source and dependency directory is
removed after the run.

The [original evidence directory](evidence/) contains the retained standalone result.
The [licensing-update evidence](evidence/licensing-update/README.md) records the
subsequent code-licence and three-author metadata verification.
The Actions workflow is prepared for a future hosted checkout. The current
verification takes place locally in Linux under WSL.
