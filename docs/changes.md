# Lean source changes

The standalone companion uses proof source revision
`8badbe471000b4e0f63d2e40b1ee784cb74c4556` and prior evidence revision
`3ac917835b35e7b1d4b66f758f1b2a37a7f78826` as its baselines. Every Lean
file was compared byte for byte against the Git blob at both revisions.

| Paths | Result |
| --- | --- |
| `SparseMM/*.lean` | All 33 modules match both revisions byte for byte. |
| `SparseMM.lean` and `Solution.lean` | Both root proof modules match both revisions byte for byte. |
| `Challenge.lean` | The PDF hash on line 20 of the module comment was updated. Every other byte matches both revisions. |

The old PDF hash in the Challenge comment was
`e9b186280f854e69a01b63e12f75ae0a4e4e9d22b3c06f216746b83a206fea5e`.
The new hash is
`37ff1c413e7b088bf4364e64c8886128e5fbc566e3abebb6a59c5c2a79e42672`.
The Challenge generator and formalization metadata identify the same
current paper. The Challenge file's SHA-256 changed from
`3df61261928098f5973f47690593236fb81a4a9e155a72d4b7a86ca5dc288964`
to
`49a619638817e20e066b3e349b172367143f01d15085ff2f43bf630fb2a2051f`.

The comparison list, allowed axioms, Lean pin, Lake project file, and
dependency manifest retain their baseline bytes. The new package adds
the matching current manuscript snapshot, documentation and attribution,
and fresh-checkout verification tooling. The recorded hashes for all
seven manuscript files and all 33 imported proof modules match the files
in this companion. [Source provenance](source-provenance.json)

The manuscript correspondence review describes the scalar-message
interpretation, integer rounding, and other construction choices already
present in the proof baseline. The verification report records the
mechanical result for the standalone snapshot. [Correspondence review](correspondence-review.md) · [Verification](verification.md)
