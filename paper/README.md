# Manuscript

The supplied PDF and the complete LaTeX source for its ten pages are included here. [Open the manuscript](sparse-mm.pdf)

To rebuild, copy the five `.tex` files and `da.bib` into a temporary directory. Run the following command from that copy.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -recorder main.tex
```

This writes `main.pdf` beside `main.tex` in the temporary copy. The tested setup used MiKTeX 26.5 with pdfTeX and BibTeX. Use a LaTeX distribution with the packages declared in `main.tex`, including Latin Modern, PGF/TikZ, `orcidlink`, `cleveref`, and the `plainurl` BibTeX style. The figure is drawn in `introduction.tex`.

The temporary-directory build keeps the supplied `sparse-mm.pdf` as the reference file and lets BibTeX find `da.bib` beside the entry point. On the tested Windows setup, `latexmk -outdir` moved the BibTeX working directory and failed to resolve the database. [Source hashes and rebuild record](../docs/manuscript.md)
