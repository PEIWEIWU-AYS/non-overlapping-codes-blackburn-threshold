import IntegerLayers
import RootIdentity
import SharpProfile
import SharpAnalysis

/-! The upper thresholds for arbitrary integral partition data. -/
namespace Nonoverlap.Bridge
open Nonoverlap.Analytic

/-- From n=564 onward a moderate recurrence is strictly improved by a grid
point above q=n²/2+143n. Here n=N+3. -/
theorem sharp_moderate_excluded (N q : ℕ) (hn : 564 ≤ N+3)
    (hq : (N+3)^2+286*(N+3) < 2*q)
    (l r : ℕ → ℝ) (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i)
    (first : l 1+r 1=1)
    (law : ∀ i, 2 ≤ i → i ≤ N+2 → l i+r i=diag i l r)
    (hmodL : l 1 ≤ ((N:ℝ)+1)/(N+2)) (hmodR : r 1 ≤ ((N:ℝ)+1)/(N+2)) :
    ∃ s : ℕ, 0 < s ∧ s < q ∧ diag (N+3) l r < score (N+1) ((s:ℝ)/q) := by
  classical
  have hn' : (564:ℝ) ≤ (N:ℝ)+3 := by exact_mod_cast hn
  have hq' : ((N:ℝ)+3)^2+286*((N:ℝ)+3) < 2*(q:ℝ) := by exact_mod_cast hq
  have hg : 2*(N+1+2) ≤ q := by omega
  have hqpos : 0 < (q:ℝ) := by linarith [sq_nonneg ((N:ℝ)+3)]
  obtain ⟨s,hsp,hsq,hd,_⟩ := Upper.nearest_split_with_distance (N+1) q hg
  refine ⟨s,hsp,hsq,?_⟩
  by_contra! bad
  have hmax : ((N:ℝ)+1)/(N+2) < 1 := by
    apply (div_lt_iff₀ (by positivity)).2
    linarith
  have rtL := root_data_of_recurrence N l r hl hr (by linarith) first law
  have rtR : RootData N r l (diag (N+3) l r) := by
    rw [diag_swap (N+3) l r]
    apply root_data_of_recurrence N r l hr hl (by linarith) (by linarith)
    intro i h1 h2
    rw [add_comm,law i h1 h2,diag_swap]
  obtain ⟨hF,hFM,hi,t,ht0,ht1,hm,ht⟩ :=
    sharp_profile N l r hl hr first law hmodL hmodR rtL rtR
  have hx : (s:ℝ)/q ∈ Set.Icc 0 1 :=
    ⟨by positivity, (div_le_one hqpos).2 (by exact_mod_cast hsq.le)⟩
  have en : ((N+1:ℕ):ℝ)+2=(N:ℝ)+3 := by push_cast; ring
  have ek : ((N+1:ℕ):ℝ)+1=(N:ℝ)+2 := by push_cast; ring
  have hlo : ((N+1:ℕ):ℝ)+2 ≥ 564 := by simpa only [en] using hn'
  have hqlo : (((N+1:ℕ):ℝ)+2)^2/2 ≤ q := by rw [en]; linarith
  have lim := SharpAnalysis.exceptional_le (N+1) hlo hqlo hx hd bad hF hFM
        (by simpa only [ek] using hi) ⟨ht0.le,ht1⟩ hm
        (by rw [ek]; simpa only [Nat.cast_add,Nat.cast_one] using ht)
  rw [en] at lim
  linarith

/-- Every integral partition cardinality of length n≥3 is bounded by one of
the genuine nontrivial Blackburn split sizes for q≥4n(n−1). -/
theorem integer_quadratic_upper (N q : ℕ) (hq : 4*(N+3)*(N+2) ≤ q)
    (L R : ℕ → ℕ) (first : L 1+R 1=q)
    (law : ∀ d, 2 ≤ d → d ≤ N+2 → L d+R d=intDiag d L R) :
    ∃ s : ℕ, 0 < s ∧ s < q ∧ intDiag (N+3) L R ≤ s^(N+2)*(q-s) :=
  integer_layers_of_moderate N q (by nlinarith) (moderate_excluded_of_recurrence N q hq)
    L R first law

/-- For n≥564 every integral layer cardinality is bounded by a Blackburn
split whenever 2q>n²+286n. -/
theorem integer_sharp_upper (N q : ℕ) (hn : 564 ≤ N+3)
    (hq : (N+3)^2+286*(N+3) < 2*q) (L R : ℕ → ℕ) (first : L 1+R 1=q)
    (law : ∀ d, 2 ≤ d → d ≤ N+2 → L d+R d=intDiag d L R) :
    ∃ s : ℕ, 0 < s ∧ s < q ∧ intDiag (N+3) L R ≤ s^(N+2)*(q-s) :=
  integer_layers_of_moderate N q (by omega) (sharp_moderate_excluded N q hn hq)
    L R first law

#print axioms integer_quadratic_upper
#print axioms integer_sharp_upper
end Nonoverlap.Bridge
