import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Analytic estimates for the Blackburn size polynomial. The exponent k corresponds
to word length n = k + 2. -/
noncomputable section
namespace Nonoverlap.Analytic

def score (k : ℕ) (x : ℝ) := x^(k+1) * (1-x)
def peak (k : ℕ) : ℝ := (k+1 : ℝ)/(k+2)

private lemma peak_spec (k : ℕ) : ((k:ℝ)+2)*peak k = k+1 := by
  unfold peak
  field_simp

private lemma peak_mem (k : ℕ) : peak k ∈ Set.Icc 0 1 := by
  constructor
  · unfold peak; positivity
  · unfold peak; apply (div_le_iff₀ (by positivity)).2; linarith

lemma hder (k : ℕ) (x : ℝ) :
    HasDerivAt (score k) (((k:ℝ)+2)*(peak k-x)*x^k) x := by
  have h := ((hasDerivAt_id x).pow (k+1)).mul ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))
  convert h using 1
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, id_eq, mul_one, zero_sub, mul_neg,
    pow_succ]
  linear_combination (x^k) * peak_spec k

private def tilted (k : ℕ) (v x : ℝ) := score k x + (((k:ℝ)+2)*v/2)*(x-peak k)^2

private lemma dtilt (k : ℕ) (v x : ℝ) :
    HasDerivAt (tilted k v) (((k:ℝ)+2)*(peak k-x)*(x^k-v)) x := by
  have h := (hder k x).add ((((hasDerivAt_id x).sub (hasDerivAt_const x (peak k))).pow 2).const_mul (((k:ℝ)+2)*v/2))
  convert h using 1
  simp
  ring

private lemma co (k : ℕ) (v : ℝ) : Continuous (tilted k v) :=
  continuous_iff_continuousAt.mpr fun x => (dtilt k v x).continuousAt

/-- A point at distance h from the continuous maximizer costs at most n h² / 2. -/
theorem rounding_loss (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    score k (peak k) - score k x ≤ (((k:ℝ)+2)/2)*(x-peak k)^2 := by
  have hc := peak_mem k
  have bound : tilted k 1 (peak k) ≤ tilted k 1 x := by
    rcases le_total x (peak k) with hh|hh
    · apply (antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (peak k))
        (co k 1).continuousOn (fun z _ => (dtilt k 1 z).hasDerivWithinAt) ?_)
        ⟨hx.1,hh⟩ ⟨hc.1,le_rfl⟩ hh
      intro y hy
      have h : y ∈ Set.Icc 0 (peak k) := interior_subset hy
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) (sub_nonneg.mpr h.2))
        (sub_nonpos.mpr (pow_le_one₀ h.1 (h.2.trans hc.2)))
    · apply (monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (peak k) 1)
        (co k 1).continuousOn (fun z _ => (dtilt k 1 z).hasDerivWithinAt) ?_)
        ⟨le_rfl,hc.2⟩ ⟨hh,hx.2⟩ hh
      intro y hy
      have h : y ∈ Set.Icc (peak k) 1 := interior_subset hy
      exact mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr h.1))
        (sub_nonpos.mpr (pow_le_one₀ (hc.1.trans h.1) h.2))
  unfold tilted at bound
  simp at bound
  linarith

/-- On an interval to the left of the peak the quadratic loss has an explicit lower bound. -/
theorem left_loss (k : ℕ) {x : ℝ} (hx : 0 ≤ x) (hc : x ≤ peak k) :
    (((k:ℝ)+2)*x^k/2)*(x-peak k)^2 ≤ score k (peak k) - score k x := by
  have bound : tilted k (x^k) x ≤ tilted k (x^k) (peak k) := by
    apply (monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x (peak k))
       (co k _).continuousOn (fun z _ => (dtilt k _ z).hasDerivWithinAt) ?_)
       ⟨le_rfl,hc⟩ ⟨hc,le_rfl⟩ hc
    intro y hy
    have h : y ∈ Set.Icc x (peak k) := interior_subset hy
    exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr h.2))
      (sub_nonneg.mpr (pow_le_pow_left₀ hx h.1 _))
  simpa [tilted,le_sub_iff_add_le,add_comm] using bound

/-- If the lower integer grid point is nearer to the peak, it beats the upper one. -/
theorem lower_grid_better (k : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxc : x ≤ peak k)
    (hcy : peak k ≤ y) (hd : peak k-x ≤ y-peak k) : score k y ≤ score k x := by
  have hxy := hxc.trans hcy
  have bound : tilted k ((peak k)^k) y ≤ tilted k ((peak k)^k) x := by
    apply (antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x y)
       (co k _).continuousOn (fun z _ => (dtilt k _ z).hasDerivWithinAt) ?_)
       ⟨le_rfl,hxy⟩ ⟨hxy,le_rfl⟩ hxy
    intro z hz
    have h : z ∈ Set.Icc x y := interior_subset hz
    rcases le_total z (peak k) with hh|hh
    · exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) (sub_nonneg.mpr hh))
        (sub_nonpos.mpr (pow_le_pow_left₀ (hx.trans h.1) hh _))
    · exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hh))
        (sub_nonneg.mpr (pow_le_pow_left₀ (peak_mem k).1 hh _))
  have hs : (x-peak k)^2 ≤ (y-peak k)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hxy)]
  have hcoef : 0 ≤ (((k:ℝ)+2)*(peak k)^k/2) := by have := (peak_mem k).1; positivity
  unfold tilted at bound
  linarith [mul_le_mul_of_nonneg_left hs hcoef]

/-- An elementary dimension-independent lower bound on the curvature factor. -/
theorem curvature_third {k : ℕ} (hk : 0 < k) :
    (1:ℝ)/3 ≤ ((k:ℝ)/(k+1))^k := by
  have h : 0 < (k:ℝ) := by exact_mod_cast hk
  have he := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1/(k:ℝ)+1)
    (Real.add_one_le_exp (1/(k:ℝ))) k
  rw [← Real.exp_nat_mul,show (k:ℝ)*(1/k)=1 by field_simp] at he
  have hu : (1/(k:ℝ)+1)^k ≤ 3 := he.trans (by linarith [Real.exp_one_lt_d9])
  have prod : ((1/(k:ℝ)+1)^k)*(((k:ℝ)/(k+1))^k)=1 := by
    rw [← mul_pow,show (1/(k:ℝ)+1)*((k:ℝ)/(k+1))=1 by field_simp; ring,one_pow]
  have := mul_le_mul_of_nonneg_right hu (by positivity : 0 ≤ ((k:ℝ)/(k+1))^k)
  linarith

#print axioms rounding_loss
#print axioms left_loss
#print axioms lower_grid_better
#print axioms curvature_third
end Nonoverlap.Analytic
