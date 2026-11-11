# Reused proof sources

The following two files adapt proof code from Hossein Vahidi's earlier
`HnVahidi/formalization_rectangular_mm` project, whose supplied source snapshot
declares the Apache License 2.0. A copy of that licence is retained in
`docs/licenses/Apache-2.0.txt`.
The earlier checkout's `main` reference was
`bd1ccd69001bb84db4ac8b5192083903b8f12b44` when inspected; the individual source
hashes below identify the actual files consumed.

| This project | Earlier source | Earlier source SHA-256 | Adaptation |
| --- | --- | --- | --- |
| `SparseMM/Routing.lean` | `RectangularMM/StaticRouting.lean` | `9ddd2eaae441f54a134225cec2c54543c15fc72f7087d502308aba9fed90394b` | Namespace and documentation adapted for sparse-MM; source scheduling proof retained. |
| `SparseMM/PermutationBalancing.lean` | `RectangularMM/LoadBalancing.lean` | `77a9c5fb0c66ce1aadbfa9149f7670639bbfedd91d30f9811aecfc53f7940dc` | Namespace changed from `RectangularMM` to `SparseMM`; finite balancing proofs retained. |

This attribution and copied licence apply to the reused material. They do not
declare a licence for the supplied paper, the other new formalization files,
or the surrounding shared research repository. The overall project's licence
is currently unspecified by its owner. No whole-repository licensing decision
is inferred from the request to formalize the paper.
