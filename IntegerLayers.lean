import UpperBridge
import Skew

/-! Integer partition cardinalities, their normalization, and reduction to the
moderate first-layer case. -/
open scoped BigOperators
namespace Nonoverlap.Bridge
open Nonoverlap.Analytic

def intDiag (d : ℕ) (L R : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d-1), L (i+1)*R (d-1-i)

noncomputable def density (q : ℕ) (L : ℕ → ℕ) (i : ℕ) : ℝ := (L i:ℝ)/(q:ℝ)^i

theorem diagonal_density (d q : ℕ) (L R : ℕ → ℕ) :
    diag d (density q L) (density q R) = (intDiag d L R:ℝ)/(q:ℝ)^d := by
  unfold diag intDiag density
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [div_mul_div_comm, ← pow_add,show i+1+(d-1-i)=d by omega]

private lemma split_density (N q s : ℕ) (hq : 0 < q) (hs : s ≤ q) :
    score (N+1) ((s:ℝ)/q) = ((s^(N+2)*(q-s):ℕ):ℝ)/(q:ℝ)^(N+3) := by
  have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  unfold score
  push_cast [Nat.cast_sub hs]
  rw [div_pow, show (q:ℝ)^(N+3)=(q:ℝ)^(N+2)*q by ring]
  field_simp

/-- A bound on a normalized word density gives the corresponding integer
cardinality bound, including both endpoint splits. -/
theorem cardinality_of_score {N q s : ℕ} (hq : 0 < q) (hs : s ≤ q) (L R : ℕ → ℕ)
    (h : diag (N+3) (density q L) (density q R) ≤ score (N+1) ((s:ℝ)/q)) :
    intDiag (N+3) L R ≤ s^(N+2)*(q-s) := by
  rw [diagonal_density,split_density N q s hq hs] at h
  have hp : (0:ℝ) < q := by exact_mod_cast hq
  exact_mod_cast (div_le_div_iff_of_pos_right (pow_pos hp (N+3))).mp h

/-- For any integral layer recurrence, a certificate excluding all moderate
states implies that an integral Blackburn split attains at least its size. -/
theorem integer_layers_of_moderate (N q : ℕ) (hq : 2 ≤ q)
    (better : ∀ l r : ℕ → ℝ, (∀ i, 0 ≤ l i) → (∀ i, 0 ≤ r i) →
      l 1+r 1=1 → (∀ i, 2 ≤ i → i ≤ N+2 → l i+r i=diag i l r) →
      l 1 ≤ ((N:ℝ)+1)/(N+2) → r 1 ≤ ((N:ℝ)+1)/(N+2) →
      ∃ s : ℕ, 0 < s ∧ s < q ∧ diag (N+3) l r < score (N+1) ((s:ℝ)/q))
    (L R : ℕ → ℕ) (first : L 1+R 1=q)
    (law : ∀ d, 2 ≤ d → d ≤ N+2 → L d+R d=intDiag d L R) :
    ∃ s : ℕ, 0 < s ∧ s < q ∧ intDiag (N+3) L R ≤ s^(N+2)*(q-s) := by
  let l := density q L
  let r := density q R
  have hqp : 0 < q := by omega
  have hq' : (0:ℝ) < q := by exact_mod_cast hqp
  have hl : ∀ i, 0 ≤ l i := fun i => by dsimp [l,density]; positivity
  have hr : ∀ i, 0 ≤ r i := fun i => by dsimp [r,density]; positivity
  have hfirst : l 1+r 1=1 := by
    simp only [l,r,density,pow_one,← add_div,← Nat.cast_add,first,div_self (ne_of_gt hq')]
  have step (d : ℕ) (h1 : 2 ≤ d) (h2 : d ≤ N+2) : l d+r d=diag d l r := by
    rw [diagonal_density]
    simp only [l,r,density,← add_div,← Nat.cast_add,law d h1 h2]
  let c := ((N:ℝ)+1)/(N+2)
  have hc : 0 < c := by dsimp [c]; positivity
  have skew (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
      (one : a 1+b 1=1) (h : c < a 1)
      (partition : ∀ i, 2 ≤ i → i ≤ N+2 → a i+b i=diag i a b) :
      diag (N+3) a b ≤ score (N+1) (a 1) := by
    have hle : ((N+1:ℕ):ℝ)*b 1 ≤ a 1 := by
      have hh := (div_lt_iff₀ (by positivity : 0<(N:ℝ)+2)).mp h
      push_cast
      nlinarith [congrArg (fun z : ℝ => ((N:ℝ)+1)*z) one]
    have hbnd := skew_bound (N+1) a b ha (hc.trans h) (hb _) hle
      (fun d hd1 hd2 => partition d hd1 (by omega))
    unfold score
    rwa [show 1-a 1=b 1 by linarith]
  have integral (s : ℕ) (hs : s ≤ q)
      (bd : diag (N+3) l r ≤ score (N+1) ((s:ℝ)/q)) :
      ∃ j : ℕ, 0 < j ∧ j < q ∧ intDiag (N+3) L R ≤ j^(N+2)*(q-j) := by
    have hcard := cardinality_of_score hqp hs L R bd
    by_cases h1 : s=0
    · subst s
      simp at hcard
      exact ⟨1,by omega,by omega,by rw [hcard]; omega⟩
    by_cases h2 : s=q
    · subst s
      simp at hcard
      exact ⟨1,by omega,by omega,by rw [hcard]; omega⟩
    exact ⟨s,by omega,by omega,hcard⟩
  by_cases hL : l 1 ≤ c
  · by_cases hR : r 1 ≤ c
    · obtain ⟨s,hs,hq',h⟩ := better l r hl hr hfirst step hL hR
      exact integral s hq'.le h.le
    · have hn := skew r l hr hl (by linarith) (lt_of_not_ge hR)
          (fun i h1 h2 => by rw [add_comm,step i h1 h2,diag_swap])
      rw [diag_swap (N+3) r l] at hn
      apply integral (R 1) (by omega)
      simpa only [r,density,pow_one] using hn
  · have hn := skew l r hl hr hfirst (lt_of_not_ge hL) step
    apply integral (L 1) (by omega)
    simpa only [l,density,pow_one] using hn

end Nonoverlap.Bridge
