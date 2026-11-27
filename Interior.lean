import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace NonoverlapThreshold.Interior

/-- Adjacent levels force a product on one of the next two diagonals. -/
theorem adjacent_tail {m x y lx rx ly ry : ℝ}
    (hm : 0 ≤ m) (hm' : m ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hlx : 0 ≤ lx) (hrx : 0 ≤ rx) (hly : 0 ≤ ly) (hry : 0 ≤ ry)
    (hstepx : m * x ≤ lx + rx) (hstepy : m * y ≤ ly + ry) :
    (m / 2)^2 * (x*y) ≤ lx*y + x*ry + rx*ly := by
  have hhalf : 0 ≤ m/2 := by linarith
  have hsmall : m/2 ≤ 1 := by linarith
  have hsmallx : m/2*x ≤ x := by simpa using mul_le_mul_of_nonneg_right hsmall hx
  have hsmally : m/2*y ≤ y := by simpa using mul_le_mul_of_nonneg_right hsmall hy
  have hprod : (m/2)^2*(x*y) = (m/2*x)*(m/2*y) := by ring
  rw [hprod]
  by_cases leftLarge : m/2*x ≤ lx
  · have h := mul_le_mul leftLarge hsmally (mul_nonneg hhalf hy) hlx
    linarith [mul_nonneg hx hry, mul_nonneg hrx hly]
  by_cases rightLarge : m/2*y ≤ ry
  · have h := mul_le_mul hsmallx rightLarge (mul_nonneg hhalf hy) hx
    linarith [mul_nonneg hlx hy, mul_nonneg hrx hly]
  have hxl : m/2*x ≤ rx := by linarith
  have hyl : m/2*y ≤ ly := by linarith
  have h := mul_le_mul hxl hyl (mul_nonneg hhalf hy) hrx
  linarith [mul_nonneg hlx hy, mul_nonneg hx hry]

/-- In a block length of N+3, inner pairs on the main diagonal have indices
    (i+2,N+1-i) for i<N. Their combined mass is paid for by pairs on
    diagonals N+4 and N+5. An index on the first tail diagonal occurs at most
    twice; the second one is enumerated in reverse order. -/
theorem diagonal_tail_bound (N : ℕ) (l r : ℕ → ℝ) (m : ℝ)
    (hm : 0 ≤ m) (hm' : m ≤ 1) (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i)
    (hlstep : ∀ i, 2 ≤ i → i ≤ N+1 → m*l i ≤ l (i+1) + r (i+1))
    (hrstep : ∀ i, 2 ≤ i → i ≤ N+1 → m*r i ≤ l (i+1) + r (i+1)) :
    m^2/8 * (∑ i ∈ Finset.range N, l (i+2) * r (N+1-i)) ≤
      (∑ i ∈ Finset.range (N+1), l (i+2) * r (N+2-i)) +
        ∑ i ∈ Finset.range N, r (i+3) * l (N+2-i) := by
  let a := fun i : ℕ => l (i+2) * r (N+2-i)
  let b := fun i : ℕ => r (i+3) * l (N+2-i)
  have ha i : 0 ≤ a i := mul_nonneg (hl _) (hr _)
  have hb i : 0 ≤ b i := mul_nonneg (hr _) (hl _)
  have pointwise (i : ℕ) (hi : i ∈ Finset.range N) :
      (m/2)^2 * (l (i+2) * r (N+1-i)) ≤ a (i+1) + a i + b i := by
    have hi' := Finset.mem_range.mp hi
    have e₁ : N+1-i+1 = N+2-i := by omega
    have e₂ : N+2-(i+1) = N+1-i := by omega
    simpa only [a, b, e₁, e₂, Nat.add_assoc] using
      adjacent_tail hm hm' (hl (i+2)) (hr (N+1-i))
        (hl (i+2+1)) (hr (i+2+1)) (hl (N+1-i+1)) (hr (N+1-i+1))
        (hlstep (i+2) (by omega) (by omega))
        (hrstep (N+1-i) (by omega) (by omega))
  have h := Finset.sum_le_sum pointwise
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib] at h
  have base : (∑ i ∈ Finset.range N, a i) ≤ ∑ i ∈ Finset.range (N+1), a i := by
    rw [Finset.sum_range_succ]
    linarith [ha N]
  have shift : (∑ i ∈ Finset.range N, a (i+1)) ≤ ∑ i ∈ Finset.range (N+1), a i := by
    rw [Finset.sum_range_succ']
    linarith [ha 0]
  change _ ≤ (∑ i ∈ Finset.range (N+1), a i) + ∑ i ∈ Finset.range N, b i
  nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.range N) => hb i)]

end NonoverlapThreshold.Interior
