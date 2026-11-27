# A quadratic alphabet threshold for non-overlapping codes

**Peiwei Wu** · Shandong Medical and Pharmaceutical University (formerly Binzhou Medical University)  
**Qian Peng** · The University of Melbourne · Corresponding author

A non-overlapping code (also called a *cross-bifix-free code*) has no nonempty proper prefix of a codeword equal to a suffix of any codeword. We study the smallest alphabet threshold beyond which Blackburn's construction is optimal at a given word length.

## Results

* **Quadratic threshold.** For word length $n$, let $q_0(n)$ be the least alphabet size from which every larger alphabet, including that size, admits an optimal Blackburn split. We prove $q_0(n)=\Theta(n^2)$. The upper bound is $4n(n-1)$ for $n\ge3$, and explicit codes give $\liminf q_0(n)/n^2\ge 1/2$.
* **A counterexample to Conjecture 1 of Stanovnik, Moškon and Mraz.** On nine letters we give a non-overlapping code of length six with **33,851** codewords. All Blackburn splits have at most **33,614**. By Remark 3 of the original article, this disproves its proposed structural conjecture. The finite counterexample, including its size and every possible overlap, is verified in [Lean](SixCount.lean).
* **Exact threshold at length five.** The optimal size on two and three letters is 2 and 17, respectively. Blackburn's best split is optimal for every alphabet of size at least four.

[Research note in Chinese / 中文研究笔记](RESEARCH.md) · [Verification report](VERIFICATION.txt) · [Prior work and search record](PRIORITY.md)

## Verify the proofs

Use the Lean toolchain in `lean-toolchain` and the mathlib revision recorded in `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Nonoverlap.lean
```

[SixCount.lean](SixCount.lean) and [ExplicitSix.lean](ExplicitSix.lean) formalize the finite counterexample as a set of actual nine-letter words. [LengthFive.lean](LengthFive.lean) solves the integer partition optimization. The analytic, upper-bound and lower-bound modules verify the indicated estimates for the general threshold. The research note states the published representation theorem and explains how those estimates apply to arbitrary maximum codes.

## Related work

* Yeow Meng Chee, *A Proof of Blackburn's Conjecture on Non-Overlapping Codes*, §IV. [arXiv:2611.28776](https://arxiv.org/abs/2611.28776)
* Lidija Stanovnik, Miha Moškon and Miha Mraz, *In search of maximum non-overlapping codes*, Conjecture 1 and Remark 3. [Designs, Codes and Cryptography](https://doi.org/10.1007/s10623-023-01344-z)
* Simon R. Blackburn, *Non-overlapping codes*. [Author's preprint](https://arxiv.org/abs/1303.1026)
