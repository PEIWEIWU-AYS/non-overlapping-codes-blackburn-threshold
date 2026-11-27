import LayerData

open scoped BigOperators
namespace Nonoverlap.Bridge

private def reserve (h : ℝ) (L : ℕ → ℝ) (j : ℕ) :=
  ∑ i ∈ Finset.range j, L i * (1 - ((j : ℝ) - i) * h)

private lemma reserve_step (h : ℝ) (L : ℕ → ℝ) (j : ℕ) :
    reserve h L (j+1) =
      reserve h L j + L j - h * ∑ i ∈ Finset.range (j+1), L i := by
  unfold reserve
  simp only [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
  rw [mul_add, Finset.mul_sum]
  have he : (∑ i ∈ Finset.range j, L i * (1 - ((j : ℝ) + 1 - (i:ℝ)) * h)) =
      ∑ i ∈ Finset.range j, (L i * (1 - ((j:ℝ) - (i:ℝ)) * h) - h * L i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Finset.sum_sub_distrib] at he
  linear_combination he

/-- A finite renewal inequality for left layers whose first coefficient is one. -/
theorem skew_renewal (K : ℕ) (h : ℝ) (L R W : ℕ → ℝ) (hh : 0 ≤ h)
    (skew : (K : ℝ)*h ≤ 1) (pos : ∀ i, 0 ≤ L i)
    (base : W 0=h) (rbase : R 0=h)
    (decomp : ∀ i < K, R (i+1) = W i - L i)
    (law : ∀ j < K, W (j+1) = R (j+1) + ∑ i ∈ Finset.range (j+1), L i*R (j-i)) :
    W K ≤ h := by
  have reserve_pos (j : ℕ) (hj : j ≤ K) : 0 ≤ reserve h L j := by
    apply Finset.sum_nonneg
    intro i hi
    have h1 : (j:ℝ)-(i:ℝ) ≤ K := by
      have v : (j:ℝ) ≤ K := by exact_mod_cast hj
      linarith [Nat.cast_nonneg (α:=ℝ) i]
    exact mul_nonneg (pos _) (by linarith [mul_le_mul_of_nonneg_right h1 hh])
  have cert : ∀ j ≤ K, W j + reserve h L j ≤ h := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      cases j with
      | zero => simp [base,reserve]
      | succ k =>
        have hk : k < K := by omega
        have hr (x : ℕ) (hx : x ≤ k) : R x ≤ h := by
          cases x with
          | zero => rw [rbase]
          | succ x =>
            rw [decomp x (by omega)]
            linarith [ih x (by omega) (by omega), reserve_pos x (by omega),pos x]
        have bound : (∑ i ∈ Finset.range (k+1), L i * R (k-i)) ≤
            h*∑ i ∈ Finset.range (k+1), L i := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          simpa [mul_comm] using mul_le_mul_of_nonneg_left (hr (k-i) (by omega)) (pos i)
        rw [law k hk,decomp k hk,reserve_step]
        linarith [ih k (by omega) (by omega)]
  linarith [cert K le_rfl,reserve_pos K le_rfl]

/-- Chee's skew-partition bound follows from the finite layer recurrence. -/
theorem skew_bound (K : ℕ) (l r : ℕ → ℝ)
    (hl : ∀ i, 0 ≤ l i) (ha : 0 < l 1) (hb : 0 ≤ r 1)
    (skew : (K : ℝ)*r 1 ≤ l 1)
    (law : ∀ d, 2 ≤ d → d < K+2 → l d+r d=diag d l r) :
    diag (K+2) l r ≤ (l 1)^(K+1)*r 1 := by
  let a := l 1
  let h := r 1/a
  let L := fun i => l i/a^i
  let R := fun i => r i/a^i
  have a0 : 0 < a := ha
  have ld : L 1 = 1 := by dsimp [L,a]; simp [ne_of_gt ha]
  have scale (d : ℕ) : diag d L R = diag d l r / a^d := by
    unfold diag
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    dsimp [L,R]
    rw [div_mul_div_comm, ← pow_add,show i+1+(d-1-i)=d by omega]
  have dl (i : ℕ) (hi : i < K) : L (i+2) + R (i+2) = diag (i+2) L R := by
    rw [scale]
    dsimp [L,R]
    rw [← add_div,law (i+2) (by omega) (by omega)]
  have law' (j : ℕ) : diag (j+1+2) L R =
      R (j+1+1) + ∑ i ∈ Finset.range (j+1), L (i+2)*R (j-i+1) := by
    unfold diag
    change (∑ i ∈ Finset.range ((j+1)+1), L (i+1)*R (j+2-i)) = _
    rw [Finset.sum_range_succ',ld,one_mul,add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show j+2-(i+1)=j-i+1 by omega]
  have bound := skew_renewal K h (fun i => L (i+2)) (fun i => R (i+1))
    (fun i => diag (i+2) L R) (div_nonneg hb a0.le)
    (by dsimp [h]; rw [← mul_div_assoc]; exact (div_le_one a0).mpr skew)
    (fun i => div_nonneg (hl _) (pow_nonneg a0.le _))
    (by simp [diag,ld,R,h]) (by simp [R,h])
    (by intro i hi; linarith [dl i hi]) (by intro j _; exact law' j)
  change diag (K+2) L R ≤ h at bound
  rw [scale] at bound
  have out := (div_le_iff₀ (pow_pos a0 (K+2))).mp bound
  convert out using 1
  dsimp [h,a]
  rw [pow_succ _ (K+1)]
  field_simp [ne_of_gt ha]
  ring

end Nonoverlap.Bridge
