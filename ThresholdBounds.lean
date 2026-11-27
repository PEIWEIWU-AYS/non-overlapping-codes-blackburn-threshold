import AlphabetThreshold
import Representation
import SharpThreshold

open NonoverlapThreshold.WordLower Filter
open Nonoverlap.Bridge Nonoverlap.Representation
namespace NonoverlapThreshold

private theorem transfer (N Q : ℕ) (hQ : 2 ≤ Q)
    (ub : ∀ q ≥ Q, ∀ l r : ℕ → ℕ, l 1+r 1=q →
      (∀ i, 2 ≤ i → i ≤ N+2 → l i+r i=intDiag i l r) →
      ∃ s : ℕ, 0 < s ∧ s < q ∧ intDiag (N+3) l r ≤ s^(N+2)*(q-s)) :
    AlwaysOptimal (N+3) Q := by
  apply optimal_of_word_bound (N+3) Q (by omega) hQ
  intro q hq C valid
  obtain ⟨l,r,first,law,hC⟩ := word_code_profile (N+3) (by omega) C valid
  obtain ⟨s,_,hs,win⟩ := ub q hq l r first (fun i hi _ => law i hi)
  exact ⟨s,hs.le,hC.trans win⟩

theorem finite_upper (n : ℕ) (hn : 3 ≤ n) : AlwaysOptimal n (4*n*(n-1)) := by
  obtain ⟨N,rfl⟩ : ∃ N, n=N+3 := ⟨n-3,by omega⟩
  rw [show N+3-1=N+2 by omega]
  apply transfer _ _ (by nlinarith)
  exact fun q hq => integer_quadratic_upper N q hq

theorem sharp_upper (n : ℕ) (hn : 564 ≤ n) :
    AlwaysOptimal n ((n^2+286*n)/2+1) := by
  obtain ⟨N,rfl⟩ : ∃ N, n=N+3 := ⟨n-3,by omega⟩
  have lower : 2 ≤ (N+3)^2+286*(N+3) := by nlinarith
  apply transfer _ _ (by omega)
  intro q hq
  apply integer_sharp_upper N q hn
  omega

/-- Absolute linear remainder for the least threshold, stated purely on actual finite word sets. -/
theorem linear_remainder (n : ℕ) (hn : 564 ≤ n) :
    n^2 < 2*q₀ n + 4*n ∧ 2*q₀ n ≤ n^2+286*n+2 := by
  refine ⟨threshold_lower_of_existence n (by omega) (sharp_upper n hn),?_⟩
  have up := q₀_le n _ (sharp_upper n hn)
  omega

/-- The threshold ratio converges to one half. It quantifies over all non-overlapping codes. -/
theorem alphabet_threshold_limit :
    Tendsto (fun n : ℕ => (q₀ n : ℝ)/(n:ℝ)^2) atTop (nhds (1/2)) :=
  limit_of_linear_remainder q₀ linear_remainder

#print axioms alphabet_threshold_limit
end NonoverlapThreshold
