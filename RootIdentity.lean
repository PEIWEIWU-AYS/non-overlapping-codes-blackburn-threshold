import UpperBridge

open scoped BigOperators

namespace Nonoverlap.Bridge

private def lowPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((domain N) ×ˢ (domain N)).filter (fun p => p.1 + p.2 ≤ N + 3)

private def productTerm (l r : ℕ → ℝ) (x : ℝ) (p : ℕ × ℕ) : ℝ :=
  l p.1 * r p.2 * x ^ (p.1 + p.2)

private lemma homogeneous {N d : ℕ} (hd : d ≤ N + 3) (l r : ℕ → ℝ) (x : ℝ) :
    (∑ p ∈ (lowPairs N).filter (fun p => p.1 + p.2 = d), productTerm l r x p) =
      diag d l r * x ^ d := by
  unfold diag
  rw [Finset.sum_mul]
  symm
  apply Finset.sum_bij (fun i _ => (i+1, d-1-i))
  · intro i hi
    have := Finset.mem_range.mp hi
    simp [lowPairs, domain]
    omega
  · intro i _ j _ h
    exact Nat.add_right_cancel (congrArg Prod.fst h)
  · rintro ⟨a,b⟩ hab
    simp [lowPairs,domain] at hab
    refine ⟨a-1, Finset.mem_range.mpr (by omega), Prod.ext (by dsimp; omega) (by dsimp; omega)⟩
  · intro i hi
    have := Finset.mem_range.mp hi
    simp only [productTerm]
    rw [show i+1+(d-1-i)=d by omega]

private lemma low_sum (N : ℕ) (l r : ℕ → ℝ) (x : ℝ) :
    (∑ p ∈ lowPairs N, productTerm l r x p) =
      diag (N+3) l r * x^(N+3) + ∑ d ∈ domain N, diag d l r * x^d := by
  have hm (p : ℕ × ℕ) (hp : p ∈ lowPairs N) :
      p.1+p.2 ∈ insert (N+3) (domain N) := by
    simp only [lowPairs, Finset.mem_filter, Finset.mem_product, domain, Finset.mem_Icc] at hp
    simp only [Finset.mem_insert, domain, Finset.mem_Icc]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hm (productTerm l r x)]
  rw [Finset.sum_insert (by simp [domain])]
  rw [homogeneous (le_refl _) l r x]
  congr 1
  refine Finset.sum_congr rfl (fun d hd => homogeneous ?_ l r x)
  have : d ≤ N+2 := (Finset.mem_Icc.mp hd).2
  omega

/-- Finite product decomposition for the two layer polynomials, with the
    contributions of all degrees above the block length kept explicitly. -/
theorem generating_identity (N : ℕ) (l r : ℕ → ℝ)
    (first : l 1+r 1=1)
    (law : ∀ i, 2 ≤ i → i ≤ N+2 → l i+r i=diag i l r) (x : ℝ) :
    value N l x * value N r x + x =
      value N l x + value N r x + (diag (N+3) l r + tail N l r x) * x^(N+3) := by
  have hprod : value N l x * value N r x =
      ∑ p ∈ (domain N) ×ˢ (domain N), productTerm l r x p := by
    unfold value
    rw [Finset.sum_product, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [productTerm,pow_add]
    ring
  have hsplit := Finset.sum_filter_add_sum_filter_not ((domain N) ×ˢ (domain N))
    (fun p : ℕ × ℕ => p.1+p.2 ≤ N+3) (productTerm l r x)
  simp only [not_le] at hsplit
  change (∑ p ∈ lowPairs N, _) + (∑ p ∈ tailPairs N, _) = _ at hsplit
  have hh : (∑ p ∈ tailPairs N, productTerm l r x p) = tail N l r x * x^(N+3) := by
    unfold tail
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hdeg := (Finset.mem_filter.mp hp).2
    change N+3 < p.1+p.2 at hdeg
    simp only [productTerm, mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hdeg)]
  have hone : 1 ∈ domain N := by simp [domain]
  have hlayers : ∑ d ∈ domain N, (diag d l r * x^d + if d=1 then x else 0) =
      value N l x + value N r x := by
    unfold value
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have h := Finset.mem_Icc.mp hd
    by_cases he : d=1
    · subst d
      simp [diag]
      linear_combination -x*first
    · simp only [if_neg he, add_zero]
      rw [← law d (by omega) h.2, add_mul]
  rw [Finset.sum_add_distrib] at hlayers
  simp [hone] at hlayers
  rw [hprod, ← hsplit, low_sum, hh]
  linarith only [hlayers, add_mul (diag (N+3) l r) (tail N l r x) (x^(N+3))]

/-- The left layer polynomial attains one at a positive point, since its
    positive linear term alone attains one at the reciprocal coefficient. -/
private lemma positive_root (N : ℕ) (l : ℕ → ℝ) (hl : ∀ i, 0 ≤ l i) (h1 : 0 < l 1) :
    ∃ x : ℝ, 0 < x ∧ value N l x = 1 := by
  have zero_val : value N l 0 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
    simp [this]
  have hbig : 1 ≤ value N l (1/l 1) := by
    have h : ∀ i ∈ domain N, 0 ≤ l i * (1/l 1)^i :=
      fun i _ => mul_nonneg (hl i) (pow_nonneg (by positivity) _)
    have := Finset.single_le_sum h (by simp [domain] : 1 ∈ domain N)
    simpa [ne_of_gt h1, value] using this
  have hcont : Continuous (value N l) :=
    continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_id.pow i)
  have hin : 1 ∈ Set.Icc (value N l 0) (value N l (1/l 1)) :=
    ⟨by rw [zero_val]; norm_num, hbig⟩
  obtain ⟨x,hx,he⟩ := intermediate_value_Icc (show (0:ℝ) ≤ 1/l 1 by positivity)
    hcont.continuousOn hin
  refine ⟨x, ?_, he⟩
  have hn : x ≠ 0 := by rintro rfl; linarith
  exact lt_of_le_of_ne hx.1 (Ne.symm hn)

/-- The positive polynomial root and the normalized tail identity follow
    from the layer recurrence in either orientation. -/
theorem root_data_of_recurrence (N : ℕ) (l r : ℕ → ℝ)
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i) (h1 : 0 < l 1)
    (first : l 1+r 1=1)
    (law : ∀ i, 2 ≤ i → i ≤ N+2 → l i+r i=diag i l r) :
    RootData N l r (diag (N+3) l r) := by
  obtain ⟨x,hx,he⟩ := positive_root N l hl h1
  have h := generating_identity N l r first law x
  rw [he,one_mul] at h
  have hc : 0 ≤ diag (N+3) l r := Finset.sum_nonneg (fun _ _ => mul_nonneg (hl _) (hr _))
  have ht := tail_nonneg (N:=N) hl hr hx.le
  have hi : x-1=(diag (N+3) l r + tail N l r x)*x^(N+3) := by linarith only [h]
  have hge : 1 ≤ x := by
    linarith only [hi, mul_nonneg (add_nonneg hc ht) (pow_nonneg hx.le (N+3))]
  refine ⟨x,hge,he,?_⟩
  unfold Analytic.score
  rw [show N+3=(N+1+1)+1 by omega, pow_succ] at hi
  rw [div_pow,one_pow]
  field_simp
  nlinarith only [hi]

/-- Every moderate normalized layer recurrence is strictly improved by an
    integral split once q is at least 4n(n−1). -/
theorem moderate_excluded_of_recurrence (N q : ℕ) (hq : 4*(N+3)*(N+2) ≤ q)
    (l r : ℕ → ℝ) (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i)
    (first : l 1+r 1=1)
    (law : ∀ i, 2 ≤ i → i ≤ N+2 → l i+r i=diag i l r)
    (hmodL : l 1 ≤ ((N:ℝ)+1)/(N+2)) (hmodR : r 1 ≤ ((N:ℝ)+1)/(N+2)) :
    ∃ s : ℕ, 0 < s ∧ s < q ∧ diag (N+3) l r < Analytic.score (N+1) ((s:ℝ)/q) := by
  have hmax : ((N:ℝ)+1)/(N+2) < 1 := by
    apply (div_lt_iff₀ (by positivity)).2
    linarith
  apply moderate_excluded N q hq l r hl hr first law hmodL hmodR
  · exact root_data_of_recurrence N l r hl hr (by linarith) first law
  · rw [diag_swap (N+3) l r]
    apply root_data_of_recurrence N r l hr hl (by linarith) (by linarith)
    intro i h1 h2
    rw [add_comm, law i h1 h2, diag_swap]

end Nonoverlap.Bridge
