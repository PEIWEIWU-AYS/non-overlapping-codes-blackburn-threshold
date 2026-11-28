# A quadratic alphabet threshold for non-overlapping codes | 非重叠码的二次字母表阈值

[Version DOI 10.5281/zenodo.24590143](https://doi.org/10.5281/zenodo.24590143) · [Paper (PDF)](manuscript.pdf) · [All versions](https://doi.org/10.5281/zenodo.24590035) · [Paper and abstract](https://peiweiwu-ays.github.io/non-overlapping-codes-blackburn-threshold/)

**Peiwei Wu** · Shandong Medical and Pharmaceutical University (formerly Binzhou Medical University)  
**Qian Peng** · The University of Melbourne · Corresponding author

A non-overlapping code (also called a *cross-bifix-free code*) has no nonempty proper prefix of a codeword equal to a suffix of any codeword. We prove that the least alphabet threshold for Blackburn's construction has leading term $n^2/2$, and give a counterexample to [Conjecture 1 of Stanovnik, Moškon and Mraz](https://doi.org/10.1007/s10623-023-01344-z).

本文确定 Blackburn 构造取得最优值的最小字母表阈值的首项系数为 1/2，证明长度 5、6 的精确阈值分别为 4、10，并给出 Stanovnik、Moškon 和 Mraz 猜想 1 的反例。

**Keywords · 关键词**　Blackburn construction · Chee alphabet threshold · Stanovnik–Moškon–Mraz Conjecture 1 · cross-bifix-free codes · 非重叠码 · 字母表阈值

## Results

* **Sharp threshold.** Let $q_0(n)$ be the least alphabet size from which an optimal Blackburn split exists for every larger alphabet, including that size. Our main theorem is $q_0(n)=n^2/2+O(n)$. In particular the limiting ratio is exactly $1/2$. We also prove $q_0(n)\le4n(n-1)$ for every $n\ge3$ and construct exceptional alphabets for every $n\ge12$.
* **An exact counterexample to Conjecture 1 of Stanovnik, Moškon and Mraz.** At length six on nine letters the maximum is **33,872**. A Blackburn split gives at most **33,614**. We give a two-mark construction attaining the maximum and prove a matching upper bound for every word code. An even simpler one-mark construction already has **33,851** words and disproves the conjecture on its own. [Exact maximum in Lean](TwoMark.lean).
* **Complete classifications at lengths five and six.** At length five the optimal sizes on two and three letters are 2 and 17, and the best Blackburn split is optimal for every alphabet of size at least four. At length six exactly four alphabets admit a larger code. For 2, 3, 4 and 9 symbols the maximum sizes are 3, 41, 251 and 33,872, respectively. Thus $q_0(5)=4$ and $q_0(6)=10$. [Length-six classification in Lean](SixSummary.lean).

[Paper (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Research note in Chinese / 中文研究笔记](RESEARCH.md) · [Verification report](VERIFICATION.txt) · [Prior work and search record](PRIORITY.md)

## Verify the proofs

Use the Lean toolchain in `lean-toolchain` and the mathlib revision recorded in `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Nonoverlap.lean
```

[ThresholdBounds.lean](ThresholdBounds.lean) proves the limiting ratio and explicit linear remainder for the *least threshold over actual finite word codes*. For every $n\ge564$, it proves $n^2<2q_0(n)+4n$ and $2q_0(n)\le n^2+286n+2$. [Representation.lean](Representation.lean) supplies the word-to-integer reduction and [WordLower.lean](WordLower.lean) constructs the exceptional family for every $n\ge12$. [ExactFiveWords.lean](ExactFiveWords.lean) proves $q_0(5)=4$ and the maxima for all alphabet sizes. [TwoMark.lean](TwoMark.lean) and [ExactSix.lean](ExactSix.lean) give the matching construction and upper bound for $S_6(9)$. [LowerExact.lean](LowerExact.lean) proves the explicit lower bound including the floor and ceiling, and [SixSummary.lean](SixSummary.lean) proves the length-six classification for every alphabet. The [verification report](VERIFICATION.txt) lists the audited declarations and source hashes.

## Related work

* Yeow Meng Chee, *A Proof of Blackburn's Conjecture on Non-Overlapping Codes*, §IV. [arXiv:2611.28776](https://arxiv.org/abs/2611.28776)
* Lidija Stanovnik, Miha Moškon and Miha Mraz, *In search of maximum non-overlapping codes*, Conjecture 1 and Remark 3. [Designs, Codes and Cryptography](https://doi.org/10.1007/s10623-023-01344-z)
* Simon R. Blackburn, *Non-overlapping codes*. [Author's preprint](https://arxiv.org/abs/1303.1026)

## GitHub topics

`coding-theory` `combinatorics` `cross-bifix-free-codes` `formal-verification` `information-theory` `lean4` `non-overlapping-codes` `theorem-proving`

[Original question, search terms, and citation](docs/discoverability.md)
