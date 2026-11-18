# Paper

[Read the arXiv PDF](sparse-mm.pdf) · [arXiv:2611.15201v1](https://arxiv.org/abs/2611.15201v1)

The PDF is the published arXiv v1, supplied by the authors. The active sources (`main.tex`, `introduction.tex`, `preliminaries.tex`, `ub.tex`, and `da.bib`) match the v1 submission bundle. The retained `conclusions.tex` belongs to the earlier draft and is not included by `main.tex`.

To build the source, copy the four active `.tex` files and `da.bib` to a temporary directory and run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -recorder main.tex
```

This creates `main.pdf` in that directory. Use a LaTeX distribution with the packages declared in `main.tex` and the `plainurl` BibTeX style. Figure 1 is drawn in `introduction.tex`.

The [manuscript record](../docs/manuscript.md) distinguishes the arXiv PDF from the earlier draft and its build evidence. These files are excluded from the repository's Apache-2.0 licence; see [the manuscript rights notice](LICENSE).
