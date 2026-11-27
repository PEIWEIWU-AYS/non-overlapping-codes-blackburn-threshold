# A quadratic alphabet threshold for non-overlapping codes

[Version DOI 10.5281/zenodo.24590036](https://doi.org/10.5281/zenodo.24590036) · [All versions](https://doi.org/10.5281/zenodo.24590035) · [Paper and abstract](https://peiweiwu-ays.github.io/non-overlapping-codes-blackburn-threshold/)

**Peiwei Wu** · Shandong Medical and Pharmaceutical University (formerly Binzhou Medical University)  
**Qian Peng** · The University of Melbourne · Corresponding author

A non-overlapping code (also called a *cross-bifix-free code*) has no nonempty proper prefix of a codeword equal to a suffix of any codeword. We study the smallest alphabet threshold beyond which Blackburn's construction is optimal at a given word length.

## Results

* **Sharp threshold.** Let $q_0(n)$ be the least alphabet size from which an optimal Blackburn split exists for every larger alphabet, including that size. Our main theorem is $q_0(n)=n^2/2+O(n)$. In particular the limiting ratio is exactly $1/2$. We also prove $q_0(n)\le4n(n-1)$ for every $n\ge3$ and construct exceptional alphabets for every $n\ge12$.
* **An exact counterexample to Conjecture 1 of Stanovnik, Moškon and Mraz.** At length six on nine letters the maximum is **33,872**. A Blackburn split gives at most **33,614**. We give a two-mark construction attaining the maximum and prove a matching upper bound for every word code. An even simpler one-mark construction already has **33,851** words and disproves the conjecture on its own. [Exact maximum in Lean](TwoMark.lean).
* **Exact threshold at length five.** The optimal size on two and three letters is 2 and 17, respectively. Blackburn's best split is optimal for every alphabet of size at least four.

[Paper (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Research note in Chinese / 中文研究笔记](RESEARCH.md) · [Verification report](VERIFICATION.txt) · [Prior work and search record](PRIORITY.md)

## Verify the proofs

Use the Lean toolchain in `lean-toolchain` and the mathlib revision recorded in `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Nonoverlap.lean
```

[ThresholdBounds.lean](ThresholdBounds.lean) proves the limiting ratio and explicit linear remainder for the *least threshold over actual finite word codes*. For every $n\ge564$, it proves $n^2<2q_0(n)+4n$ and $2q_0(n)\le n^2+286n+2$. [Representation.lean](Representation.lean) supplies the word-to-integer reduction and [WordLower.lean](WordLower.lean) constructs the exceptional family for every $n\ge12$. [ExactFiveWords.lean](ExactFiveWords.lean) proves $q_0(5)=4$ and the maxima for all alphabet sizes. [TwoMark.lean](TwoMark.lean) and [ExactSix.lean](ExactSix.lean) give the matching construction and upper bound for $S_6(9)$. The [verification report](VERIFICATION.txt) lists the audited declarations and source hashes.

## Related work

* Yeow Meng Chee, *A Proof of Blackburn's Conjecture on Non-Overlapping Codes*, §IV. [arXiv:2611.28776](https://arxiv.org/abs/2611.28776)
* Lidija Stanovnik, Miha Moškon and Miha Mraz, *In search of maximum non-overlapping codes*, Conjecture 1 and Remark 3. [Designs, Codes and Cryptography](https://doi.org/10.1007/s10623-023-01344-z)
* Simon R. Blackburn, *Non-overlapping codes*. [Author's preprint](https://arxiv.org/abs/1303.1026)
