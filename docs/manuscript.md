# Manuscript source and reproduction

The included manuscript is *Sparse Matrix Multiplication Exponent 1.5 in the Low-bandwidth Model* by Chetan Gupta, Jukka Suomela, and Hossein Vahidi. [Supplied PDF](../paper/sparse-mm.pdf)

The five TeX files and bibliography match the `arxiv/` source checkout at commit `678f50ee1fd6c1f97ab92062f965063be28015af`. The PDF is a separate supplied file from that checkout. Its hash identifies the precise document covered by the [claim map](coverage.md).

| File | SHA-256 |
| --- | --- |
| `main.tex` | `7295a3696803dbe117af5378b6ca21423b19a74d2410685f18ce6f71f71c3ff5` |
| `introduction.tex` | `6cad3690266b31d72f5c49ae97964628982c4fabed7a761d470496cfe4665119` |
| `preliminaries.tex` | `f6d829cc85a6337168dcb75ef001b40d47fe933fa349aaa18bc6ce748f98fe51` |
| `ub.tex` | `0301bdcf80a0a65d5e7c26117071b3908e598ea27905455a724552d4c0c9c1a0` |
| `conclusions.tex` | `5f2a52291284dce4e066c58db6554d08164d6ee1de700477fd23f7a1f85ed00e` |
| `da.bib` | `e1297ed5b251fb992e93c3f4a7bdef2294686cd8fdf4f2e157df7b2a839f5009` |
| `sparse-mm.pdf` | `37ff1c413e7b088bf4364e64c8886128e5fbc566e3abebb6a59c5c2a79e42672` |

The entry point is `main.tex`. It reads the other four TeX files, uses `da.bib` with the distribution-provided `plainurl.bst`, and draws Figure 1 using TikZ in `introduction.tex`. The local input list recorded during the build contains these sources and generated auxiliary files. The commented reference to `beyond.tex` is inactive. [Build instructions](../paper/README.md)

On 11 November 2026, a clean temporary copy containing only the five TeX files and `da.bib` built successfully with `latexmk`, MiKTeX 26.5, pdfTeX 1.40.29, and BibTeX 0.99e. BibTeX resolved all nine cited entries. The final pass reported three `hyperref` bookmark-token warnings.

The rebuilt PDF had ten pages, with exact per-page extracted text and identical Poppler PNG renders at 100 dpi on all ten pages. Pages 1, 4, 6, and 10 were inspected visually for the title, figure and model description, main theorem, and references. The rebuild's PDF hash was `10ec03e4d71e30602ae9939deb2d5b3ec6c3a600cea3631bf49c388edef7c0f1` and its creation timestamp differed from the supplied file's. The supplied PDF in `paper/` remains the hashed manuscript snapshot.

The Lean proof baseline comes from commit `8badbe471000b4e0f63d2e40b1ee784cb74c4556` of the research repository. Its earlier verification evidence was recorded at commit `3ac917835b35e7b1d4b66f758f1b2a37a7f78826`. That proof project originally identified the PDF with SHA-256 `e9b186280f854e69a01b63e12f75ae0a4e4e9d22b3c06f216746b83a206fea5e`. The coverage map in this companion was checked against the current PDF and Lean statements.
