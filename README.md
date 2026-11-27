# A quadratic alphabet threshold for non-overlapping codes

**Peiwei Wu** · Shandong Medical and Pharmaceutical University (formerly Binzhou Medical University)  
**Qian Peng** · The University of Melbourne · Corresponding author

A non-overlapping code (also called a *cross-bifix-free code*) has no nonempty proper prefix of a codeword equal to a suffix of any codeword. We study the smallest alphabet threshold beyond which Blackburn's construction is optimal at a given word length.

## Results

* **Sharp threshold.** Let $q_0(n)$ be the least alphabet size from which an optimal Blackburn split exists for every larger alphabet, including that size. Our main theorem is $q_0(n)=n^2/2+O(n)$. In particular the limiting ratio is exactly $1/2$. We also prove $q_0(n)\le4n(n-1)$ for every $n\ge3$ and construct exceptional alphabets for every $n\ge12$.
* **A counterexample to Conjecture 1 of Stanovnik, Moškon and Mraz.** On nine letters we give a non-overlapping code of length six with **33,851** codewords. All Blackburn splits have at most **33,614**. By Remark 3 of the original article, this disproves its proposed structural conjecture. The finite counterexample, including its size and every possible overlap, is verified in [Lean](SixCount.lean).
* **Exact threshold at length five.** The optimal size on two and three letters is 2 and 17, respectively. Blackburn's best split is optimal for every alphabet of size at least four.

[Paper (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Research note in Chinese / 中文研究笔记](RESEARCH.md) · [Verification report](VERIFICATION.txt) · [Prior work and search record](PRIORITY.md)

## Verify the proofs

Use the Lean toolchain in `lean-toolchain` and the mathlib revision recorded in `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Nonoverlap.lean
```

[SixCount.lean](SixCount.lean) verifies the 33,851-word counterexample. [WordLower.lean](WordLower.lean) constructs genuine non-overlapping word sets at every length $n\ge12$ and compares them with every integer split. [LengthFive.lean](LengthFive.lean) solves the length-five integer partition problem. The [verification report](VERIFICATION.txt) records the declarations actually checked. The manuscript gives the general proof, including the asymptotic analysis, and identifies the structural results it uses from earlier work.

## Related work

* Yeow Meng Chee, *A Proof of Blackburn's Conjecture on Non-Overlapping Codes*, §IV. [arXiv:2611.28776](https://arxiv.org/abs/2611.28776)
* Lidija Stanovnik, Miha Moškon and Miha Mraz, *In search of maximum non-overlapping codes*, Conjecture 1 and Remark 3. [Designs, Codes and Cryptography](https://doi.org/10.1007/s10623-023-01344-z)
* Simon R. Blackburn, *Non-overlapping codes*. [Author's preprint](https://arxiv.org/abs/1303.1026)
