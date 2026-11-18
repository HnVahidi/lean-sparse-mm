# Manuscript source and reproduction

The repository includes *Sparse Matrix Multiplication Exponent 1.5 in the Low-bandwidth Model* by Chetan Gupta, Jukka Suomela, and Hossein Vahidi.

## Current paper: arXiv v1

[Open the included PDF](../paper/sparse-mm.pdf) · [arXiv:2611.15201v1](https://arxiv.org/abs/2611.15201v1)

On 17 November 2026, the bundled PDF was replaced with the author's copy downloaded from arXiv. Its 495,564 bytes match the public arXiv PDF, with SHA-256 `ac738917953df4bed957f736a4a1cc811d93eaf7d07de28080d0b4bff7b28f36`. It has ten pages and was submitted to arXiv on 11 November 2026.

The four active TeX files and `da.bib` match the author's `arxiv-v1.zip` submission bundle and manuscript source revision `4f0c46f513163d7b61ceeff9e324fce9fb806fa1`. Only `main.tex` differs from the previously bundled active sources. The ZIP also contains a generated `main.bbl`; the repository retains `da.bib` and generates the bibliography when built. The unchanged `conclusions.tex` is retained from the earlier draft and is inactive.

| File | SHA-256 |
| --- | --- |
| `conclusions.tex` | `5f2a52291284dce4e066c58db6554d08164d6ee1de700477fd23f7a1f85ed00e` |
| `da.bib` | `e1297ed5b251fb992e93c3f4a7bdef2294686cd8fdf4f2e157df7b2a839f5009` |
| `introduction.tex` | `6cad3690266b31d72f5c49ae97964628982c4fabed7a761d470496cfe4665119` |
| `main.tex` | `6297fc3d29ded9b483d3bc3dcd8550de6139ad8d7ed5096ed76715eaaf74ab6f` |
| `preliminaries.tex` | `f6d829cc85a6337168dcb75ef001b40d47fe933fa349aaa18bc6ce748f98fe51` |
| `sparse-mm.pdf` | `ac738917953df4bed957f736a4a1cc811d93eaf7d07de28080d0b4bff7b28f36` |
| `ub.tex` | `0301bdcf80a0a65d5e7c26117071b3908e598ea27905455a724552d4c0c9c1a0` |

The numbered claims, their proofs, and the model assumptions are unchanged from the earlier draft. Theorem 4 remains on page 6. The arXiv version removes the former Conclusions section, updates the AI Methodology section, and adds the formalization DOI footnote. Some cross-reference labels in proof prose changed from Lemma to Theorem without changing the referenced numbered claims. The [coverage guide](coverage.md) applies to these unchanged claims. [Build instructions](../paper/README.md)

The paper uses the [arXiv perpetual, non-exclusive distribution licence](https://arxiv.org/licenses/nonexclusive-distrib/1.0/). The authors retain copyright, and `paper/` remains excluded from Apache-2.0.

## Earlier draft archived in formalization v1.0.0

The fixed [v1.0.0 release](https://github.com/HnVahidi/lean-sparse-mm/releases/tag/v1.0.0) contains the earlier author-supplied PDF, SHA-256 `37ff1c413e7b088bf4364e64c8886128e5fbc566e3abebb6a59c5c2a79e42672`, and source revision `678f50ee1fd6c1f97ab92062f965063be28015af`. Replacing the working copy does not change that release or its Zenodo archive.

On 11 November 2026, a temporary copy of that earlier draft's five TeX files and `da.bib` built with `latexmk`, MiKTeX 26.5, pdfTeX 1.40.29, and BibTeX 0.99e. The ten rebuilt pages matched the earlier supplied PDF in extracted text and 100 dpi Poppler renders. The rebuilt PDF had SHA-256 `10ec03e4d71e30602ae9939deb2d5b3ec6c3a600cea3631bf49c388edef7c0f1`. This is historical evidence for the earlier draft, not a new rebuild of arXiv v1.

The Lean proof baseline is revision `8badbe471000b4e0f63d2e40b1ee784cb74c4556`, with earlier verification evidence at `3ac917835b35e7b1d4b66f758f1b2a37a7f78826`. Its original PDF identity remains recorded separately in [source-provenance.json](source-provenance.json).
