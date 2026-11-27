import BlackburnWords

open NonoverlapThreshold.WordLower Filter
namespace NonoverlapThreshold

/-- The least alphabet size from which Blackburn splits attain the actual word-code maximum. -/
noncomputable def q₀ (n : ℕ) : ℕ := sInf {Q : ℕ | AlwaysOptimal n Q}

theorem q₀_spec (n Q : ℕ) (h : AlwaysOptimal n Q) : AlwaysOptimal n (q₀ n) :=
  Nat.sInf_mem (s := {Q : ℕ | AlwaysOptimal n Q}) ⟨Q,h⟩

theorem q₀_le (n Q : ℕ) (h : AlwaysOptimal n Q) : q₀ n ≤ Q :=
  Nat.sInf_le (s := {Q : ℕ | AlwaysOptimal n Q}) h

/-- A dominating split for each word code gives a *single* optimal split for the alphabet. -/
theorem optimal_of_word_bound (n Q : ℕ) (hn : 1 ≤ n) (hQ : 2 ≤ Q)
    (bound : ∀ q ≥ Q, ∀ C : Finset (List (Fin q)), IsCode n C →
      ∃ s ≤ q, C.card ≤ s^(n-1)*(q-s)) : AlwaysOptimal n Q := by
  refine ⟨hQ,?_⟩
  intro q hq
  obtain ⟨s,hs,hmax⟩ := (Finset.range (q+1)).exists_max_image
    (fun a => a^(n-1)*(q-a)) (by simp)
  have hs' := Finset.mem_range.mp hs
  obtain ⟨B,hB,size⟩ := blackburn_words (n-1) q s (by omega)
  rw [show n-1+1 = n by omega] at hB
  refine ⟨s,by omega,B,hB,size,?_⟩
  intro C hC
  obtain ⟨j,hj,h⟩ := bound q hq C hC
  rw [size]
  exact h.trans (hmax j (Finset.mem_range.mpr (by omega)))

theorem threshold_lower_of_existence (n : ℕ) (hn : 12 ≤ n) {Q : ℕ} (existsQ : AlwaysOptimal n Q) :
    n^2 < 2 * q₀ n + 4*n := by
  obtain ⟨q,C,hq,hC,strict⟩ := quadratic_word_counterexamples n hn
  have spec := q₀_spec n Q existsQ
  by_contra! bad
  have leq : q₀ n ≤ q := by omega
  obtain ⟨s,hs,B,_,size,h⟩ := spec.2 q leq
  have hsmall := h C hC
  rw [size] at hsmall
  exact (not_lt_of_ge hsmall) (strict s hs)

/-- The finite two-sided linear remainder implies convergence of the threshold ratio. -/
theorem limit_of_linear_remainder (Q : ℕ → ℕ)
    (bounds : ∀ n ≥ 564, n^2 < 2*Q n + 4*n ∧ 2*Q n ≤ n^2+286*n+2) :
    Tendsto (fun n : ℕ => (Q n : ℝ)/(n:ℝ)^2) atTop (nhds (1/2)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (144/ε)
  refine ⟨max N 564,?_⟩
  intro n hn
  have hn' : 564 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (564:ℝ) ≤ n := by exact_mod_cast hn'
  have pos : 0 < (n:ℝ) := by linarith
  have small : (144:ℝ) < ε*n := by
    have leR : (N:ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hn
    have := (div_lt_iff₀ hε).mp (hN.trans_le leR)
    linarith
  obtain ⟨lo,hi⟩ := bounds n hn'
  have lo' : (n:ℝ)^2 < 2*(Q n:ℝ)+4*n := by exact_mod_cast lo
  have hi' : 2*(Q n:ℝ) ≤ (n:ℝ)^2+286*n+2 := by exact_mod_cast hi
  rw [Real.dist_eq,abs_lt]
  have mulB := mul_lt_mul_of_pos_right small pos
  constructor
  · rw [lt_sub_iff_add_lt,lt_div_iff₀ (sq_pos_of_pos pos)]
    nlinarith
  · rw [sub_lt_iff_lt_add,div_lt_iff₀ (sq_pos_of_pos pos)]
    nlinarith

end NonoverlapThreshold
