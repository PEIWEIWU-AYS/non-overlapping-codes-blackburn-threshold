import UpperBridge

open scoped BigOperators
namespace Nonoverlap.Bridge
open Nonoverlap.Analytic

def inner (N : ℕ) (l r : ℕ → ℝ) : ℝ :=
   ∑ i ∈ Finset.range N, l (i+2)*r (N+1-i)

theorem asymmetric_penalty {N : ℕ} {l r : ℕ → ℝ} {ρ : ℝ}
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i) (first : l 1+r 1=1)
    (law : ∀ i, 2 ≤ i → i ≤ N+2 → l i+r i=diag i l r) (hρ : 1 ≤ ρ) :
    l 1*r 1/8*inner N l r ≤ tail N l r ρ := by
  have h := NonoverlapThreshold.Interior.diagonal_tail_asymmetric N l r (l 1) (r 1)
    (hl _) (by linarith [hr 1]) (hr _) (by linarith [hl 1]) hl hr
    (fun i h1 h2 => by nlinarith [step_endpoints hl hr law i h1 h2,mul_nonneg (hl 1) (hr i)])
    (fun i h1 h2 => by linarith [step_endpoints hl hr law i h1 h2,mul_nonneg (hl i) (hr 1)])
  exact h.trans (diagonals_le_tail hl hr hρ)

private lemma oriented_profile {N : ℕ} {l r : ℕ → ℝ} {M F : ℝ}
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i)
    (cut : l 1 ≤ ((N:ℝ)+1)/(N+2)) (lower : 0 ≤ M-F) (upper : M-F ≤ r (N+2))
    (root : RootData N l r M) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ M ≤ score (N+1) t ∧
      (M-F)*(t-((N:ℝ)+1)/(N+2)) ≤ score (N+1) t-M := by
  obtain ⟨ρ,hρ,hv,he⟩ := root
  have hp : 0 < ρ := by linarith
  have ha : l 1 ≤ 1/ρ := by
    apply (le_div_iff₀ hp).2
    have hs := Finset.single_le_sum (s:=domain N) (f:=fun i => l i*ρ^i)
        (fun i _ => mul_nonneg (hl i) (pow_nonneg hp.le i))
        (a:=1) (by simp [domain])
    unfold value at hv
    simpa only [pow_one,hv] using hs
  refine ⟨1/ρ, by positivity, (div_le_iff₀ hp).2 (by linarith), ?_, ?_⟩
  · linarith [tail_nonneg (N:=N) hl hr hp.le]
  · have b := boundary_tail hl hr hρ hv
    have q := mul_le_mul_of_nonneg_left (sub_le_sub_left cut (1/ρ)) lower
    have w := mul_le_mul_of_nonneg_right upper (sub_nonneg.mpr ha)
    linarith

/-- A quantitative pair of bounds for the sharp threshold. The first controls
interior mass; the second retains the full endpoint mass (M-F) at a single root. -/
theorem sharp_profile (N : ℕ) (l r : ℕ → ℝ) (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i)
    (first : l 1+r 1=1) (law : ∀ i, 2 ≤ i → i ≤ N+2 → l i+r i=diag i l r)
    (hmodL : l 1 ≤ ((N:ℝ)+1)/(N+2)) (hmodR : r 1 ≤ ((N:ℝ)+1)/(N+2))
    (rootL : RootData N l r (diag (N+3) l r)) (rootR : RootData N r l (diag (N+3) l r)) :
    let M := diag (N+3) l r
    let F := inner N l r
    0 ≤ F ∧ F ≤ M ∧ F/(16*((N:ℝ)+2)) ≤ score (N+1) (peak (N+1))-M ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ M ≤ score (N+1) t ∧
      (M-F)*(t-((N:ℝ)+1)/(N+2)) ≤ score (N+1) t-M := by
  let M := diag (N+3) l r
  let F := inner N l r
  have split := diag_split N l r
  change M=l 1*r (N+2)+l (N+2)*r 1+F at split
  have hf : 0 ≤ F := Finset.sum_nonneg fun i _ => mul_nonneg (hl _) (hr _)
  have hfm : F ≤ M := by linarith [mul_nonneg (hl 1) (hr (N+2)),mul_nonneg (hl (N+2)) (hr 1)]
  refine ⟨hf,hfm,?_,?_⟩
  · obtain ⟨ρ,hρ,_,he⟩ := rootL
    have hpen := asymmetric_penalty hl hr first law hρ
    change l 1*r 1/8*F ≤ _ at hpen
    have hp := score_peak (N+1) (by positivity : 0 ≤ 1/ρ)
    have eq : 1/((N:ℝ)+2)+((N:ℝ)+1)/(N+2)=1 := by field_simp; ring
    have prod : (1/((N:ℝ)+2))*(1/2) ≤ l 1*r 1 := by
      rcases le_total (l 1) (r 1) with h|h
      · apply mul_le_mul (by linarith : 1/((N:ℝ)+2) ≤ l 1) (by linarith) (by norm_num) (hl _)
      · rw [mul_comm (l 1)]
        apply mul_le_mul (by linarith : 1/((N:ℝ)+2) ≤ r 1) (by linarith) (by norm_num) (hr _)
    have h := mul_le_mul_of_nonneg_right prod hf
    have ea : F/(16*((N:ℝ)+2))= (1/((N:ℝ)+2))*(1/2)*F/8 := by field_simp; ring_nf; simp
    change F/(16*((N:ℝ)+2)) ≤ _-M
    rw [ea]
    linarith
  · rcases le_total (r (N+2)) (l (N+2)) with h|h
    · apply oriented_profile hr hl hmodR (sub_nonneg.mpr hfm) _ rootR
      nlinarith [mul_le_mul_of_nonneg_left h (hl 1),
        show (l 1+r 1)*l (N+2)=l (N+2) by rw [first,one_mul]]
    · apply oriented_profile hl hr hmodL (sub_nonneg.mpr hfm) _ rootL
      nlinarith [mul_le_mul_of_nonneg_left h (hr 1),
        show (l 1+r 1)*r (N+2)=r (N+2) by rw [first,one_mul]]

end Nonoverlap.Bridge
