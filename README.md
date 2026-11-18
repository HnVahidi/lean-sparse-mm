# Sparse matrix multiplication in Lean

A Lean 4 formalization of **[Sparse Matrix Multiplication Exponent 1.5 in the Low-bandwidth Model](https://arxiv.org/abs/2611.15201)** by Chetan Gupta, Jukka Suomela, and Hossein Vahidi.

[Paper PDF](paper/sparse-mm.pdf) · [arXiv](https://arxiv.org/abs/2611.15201)

The main theorem gives a deterministic algorithm that runs in $O(d^{3/2})$ rounds when the sparsity pattern is known in advance. Here $d$ bounds the number of nonzero entries in each row and column.

## Abstract

We study sparse matrix multiplication in the low-bandwidth model: $n$ computers multiply two $n\times n$ matrices, and each computer can send and receive one $O(\log n)$-bit message per round. The input matrices are uniformly sparse, meaning that there are at most $d$ nonzero entries in each row and column, and the task is to compute a uniformly sparse part of their product.

In prior work, Gupta et al. (SPAA 2022) presented an $O(d^{1.907})$-round algorithm over fields for this problem when the sparsity structure is globally known in advance (this is referred to as the supported setting). The upper bound was later improved to $O(d^{1.832})$ rounds.

In this work, we give a deterministic algorithm that solves this problem in $O(d^{3/2})$ rounds in the supported setting, improving the previous bounds over fields and semirings.

## Read the proofs

- [Paper results and their Lean statements](docs/coverage.md).
- [Challenge.lean](Challenge.lean): theorem statements and definitions.
- [SparseMM/Main.lean](SparseMM/Main.lean): the main theorem and proof.
- [SparseMM/](SparseMM/): supporting proofs, imported by [Solution.lean](Solution.lean).

## Build and verify

Install [Elan](https://github.com/leanprover/elan), then run these commands from the repository root:

```sh
lake exe cache get
lake build
```

The project pins its Lean version and dependencies. For the full verification procedure, including independent proof checks, see the [verification guide](docs/verification.md). It requires Linux or WSL and a committed source snapshot.

## Citation and licence

Cite the paper for the mathematical results and an [archived release](docs/release.md) for the formalization. Citation metadata is provided in [CITATION.cff](CITATION.cff).

Code and project documentation outside `paper/` use [Apache-2.0](LICENSE), subject to the [existing notices](NOTICE.md). The manuscript has [separate rights](paper/LICENSE).

The formalization was developed with AI assistance, recorded in [formalization.yaml](formalization.yaml).
