import Analytic
import Mathlib.Algebra.Order.Round

namespace Nonoverlap.Upper
open Nonoverlap.Analytic

/-- Halfway between the largest moderate first-level ratio and the score maximizer. -/
noncomputable def midpoint (k : ℕ) : ℝ := (peak k + (k:ℝ)/(k+1))/2

private lemma midpoint_diff (k : ℕ) :
    midpoint k - peak k = -1/(2*((k:ℝ)+2)*(k+1)) := by
  unfold midpoint peak
  field_simp
  ring

theorem midpoint_gap (k : ℕ) (hk : 0 < k) {M : ℝ} (hM : M ≤ score k (midpoint k)) :
    1/(24*((k:ℝ)+2)*(k+1)^2) ≤ score k (peak k) - M := by
  have hd := midpoint_diff k
  have h0 : 0 ≤ midpoint k := by unfold midpoint peak; positivity
  have hc : midpoint k ≤ peak k := by
    have hneg : -1 / (2 * ((k:ℝ)+2) * (k+1)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
    linarith
  have hfloor : (k:ℝ)/(k+1) ≤ midpoint k := by
    unfold midpoint at hc ⊢
    linarith
  have hcurv := (curvature_third hk).trans (pow_le_pow_left₀ (by positivity) hfloor k)
  have hloss := left_loss k h0 hc
  rw [hd] at hloss
  calc
    _ = (((k:ℝ)+2)*(1/3)/2) * (-1/(2*((k:ℝ)+2)*(k+1)))^2 := by field_simp; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcurv (by positivity)) (by norm_num : (0:ℝ) ≤ 2))
      (sq_nonneg _)).trans (hloss.trans (by linarith))

/-- The two endpoint and interior estimates use different powers of the distance
to the peak. Under the normalization u=1/n, v=1/(n-1), all imply uv²/96. -/
theorem three_gap_cases {u v M m gap : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hvu : v ≤ 2*u) (hM : u/6 ≤ M) (hm : v ≤ m)
    (cases : u*v^2/24 ≤ gap ∨ M*u*v/4 ≤ gap ∨ M*m^2/16 ≤ gap) :
    u*v^2/96 ≤ gap := by
  have hpos : 0 ≤ u*v^2 := mul_nonneg hu.le (sq_nonneg _)
  rcases cases with h | h | h
  · linarith
  · have huv := mul_le_mul_of_nonneg_left hvu (mul_nonneg hu.le hv.le)
    have hmass := mul_le_mul_of_nonneg_right hM (mul_nonneg hu.le hv.le)
    nlinarith
  · have hsq := pow_le_pow_left₀ hv.le hm 2
    have hm0 : 0 ≤ M := by linarith
    have hc := mul_le_mul hM hsq (sq_nonneg v) hm0
    nlinarith

private lemma grid_loss_lt {d q : ℝ} (hd : 2 ≤ d) (hq : 4*d*(d-1) ≤ q) :
    d/(8*q^2) < 1/(96*d*(d-1)^2) := by
  have h1 : 0 < d-1 := by linarith
  have h2 : 0 < d := by linarith
  have h3 : 0 < 4*d*(d-1) := by positivity
  calc
    d/(8*q^2) ≤ d/(8*(4*d*(d-1))^2) := by gcongr
    _ = 1/(128*d*(d-1)^2) := by field_simp; ring
    _ < 1/(96*d*(d-1)^2) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith [mul_pos h2 (sq_pos_of_pos h1)]

private theorem peak_lower (k : ℕ) :
    1/(3*((k:ℝ)+2)) ≤ score k (peak k) := by
  have h := curvature_third (k := k+1) (by omega)
  have hs : (1:ℝ)/3 ≤ (peak k)^(k+1) := by
    convert h using 1
    push_cast
    unfold peak
    ring_nf
  have hdiff : 1-peak k = 1/((k:ℝ)+2) := by unfold peak; field_simp; ring
  unfold score
  rw [hdiff]
  convert mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ 1/((k:ℝ)+2)) using 1
  field_simp

/-- A permissible integer alphabet split realizes the quadratic rounding loss. -/
theorem nearest_split (k q : ℕ) (hq : 2*(k+2) ≤ q) :
    ∃ s : ℕ, 0 < s ∧ s < q ∧
      score k (peak k)-score k ((s:ℝ)/q) ≤ ((k:ℝ)+2)/(8*(q:ℝ)^2) := by
  let p := peak k
  have hd : 0 < (k:ℝ)+2 := by positivity
  have haq : 2*((k:ℝ)+2) ≤ q := by exact_mod_cast hq
  have hqpos : 0 < (q:ℝ) := by linarith
  have hp : 0 ≤ p := by dsimp [p,peak]; positivity
  have hp' : 0 ≤ 1-p := by
    dsimp [p,peak]
    rw [sub_nonneg,div_le_iff₀ hd]
    linarith
  have eqp : ((k:ℝ)+2)*p = (k:ℝ)+1 := by unfold p peak; field_simp
  have hleft : 2 ≤ (q:ℝ)*p := by
    nlinarith [mul_le_mul_of_nonneg_right haq hp,Nat.cast_nonneg (α := ℝ) k]
  have hright : 2 ≤ (q:ℝ)*(1-p) := by nlinarith [mul_le_mul_of_nonneg_right haq hp']
  let z : ℤ := round ((q:ℝ)*p)
  have hz := abs_le.mp (abs_sub_round ((q:ℝ)*p))
  change -(1/2:ℝ) ≤ (q:ℝ)*p-z ∧ (q:ℝ)*p-z ≤ 1/2 at hz
  have hz0 : 0 < (z:ℝ) := by linarith
  have hz1 : (z:ℝ) < q := by linarith
  have hz' : 0 ≤ z := by exact_mod_cast hz0.le
  let s := z.toNat
  have hs : (s:ℤ) = z := Int.toNat_of_nonneg hz'
  have hs' : (s:ℝ) = (z:ℝ) := by exact_mod_cast hs
  rw [← hs'] at hz hz0 hz1
  refine ⟨s, by exact_mod_cast hz0, by exact_mod_cast hz1, ?_⟩
  have hmem : (s:ℝ)/q ∈ Set.Icc 0 1 :=
    ⟨by positivity, (div_le_iff₀ hqpos).2 (by linarith)⟩
  have approx := rounding_loss k hmem
  have hdif : |(s:ℝ)/q-p| ≤ 1/(2*q) := by
    rw [abs_le]
    constructor
    · rw [show -(1/(2*(q:ℝ))) = (-1/2)/q by ring,le_sub_iff_add_le,
          show (-1/2:ℝ)/q + p = ((-1/2)+(q:ℝ)*p)/q by field_simp; ring,div_le_div_iff_of_pos_right hqpos]
      linarith
    · rw [show 1/(2*(q:ℝ)) = (1/2)/q by ring,sub_le_iff_le_add,
          show (1/2:ℝ)/q + p = ((1/2)+(q:ℝ)*p)/q by field_simp; ring,div_le_div_iff_of_pos_right hqpos]
      linarith
  have hsquare := pow_le_pow_left₀ (abs_nonneg _) hdif 2
  rw [sq_abs] at hsquare
  calc
    _ ≤ _ := approx
    _ ≤ (((k:ℝ)+2)/2)*(1/(2*(q:ℝ)))^2 := mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = _ := by
      field_simp [ne_of_gt hqpos]
      ring_nf
      simp

/-- If a moderate code has one of the three structural certificates, it falls
strictly below the rounded grid score whenever q ≥ 4 n(n-1), with n=k+2.
Here B is a grid score and M a normalized code size. -/
theorem quadratic_exclusion (k q : ℕ) (hk : 0 < k)
    (hq : 4*(k+2)*(k+1) ≤ q) {B M m : ℝ}
    (hgrid : score k (peak k)-B ≤ ((k:ℝ)+2)/(8*(q:ℝ)^2))
    (hm : 1/((k:ℝ)+1) ≤ m)
    (cases : M ≤ score k (midpoint k) ∨
       M*(1/((k:ℝ)+2))*(1/((k:ℝ)+1))/4 ≤ score k (peak k)-M ∨
       M*m^2/16 ≤ score k (peak k)-M) : M < B := by
  by_contra! hMB
  let d : ℝ := (k:ℝ)+2
  have hd : 2 ≤ d := by dsimp [d]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hd0 : 0 < d := by linarith
  have hd1 : 0 < d-1 := by linarith
  have he : d-1 = (k:ℝ)+1 := by dsimp [d]; ring
  have hqr : 4*d*(d-1) ≤ (q:ℝ) := by
    rw [he]; dsimp [d]; exact_mod_cast hq
  have hsmall := grid_loss_lt hd hqr
  have small' : 1/(96*d*(d-1)^2) ≤ 1/(6*d) := by
    apply one_div_le_one_div_of_le (by positivity)
    have h1 : 1 ≤ (d-1)^2 := by nlinarith [sq_nonneg (d-2)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hd0.le]
  have hpeak := peak_lower k
  change 1/(3*d) ≤ _ at hpeak
  change _ ≤ d/(8*(q:ℝ)^2) at hgrid
  have hm0 : (1/d)/6 ≤ M := by
    have h : 1/(3*d)-1/(6*d) = (1/d)/6 := by field_simp; ring
    linarith [hsmall.trans_le small']
  have huv : 1/(d-1) ≤ 2*(1/d) := by
    rw [show 2*(1/d) = 2/d by ring]
    apply (div_le_div_iff₀ hd1 hd0).2
    linarith
  have cases' : (1/d)*(1/(d-1))^2/24 ≤ score k (peak k)-M ∨
      M*(1/d)*(1/(d-1))/4 ≤ score k (peak k)-M ∨ M*m^2/16 ≤ score k (peak k)-M := by
    rcases cases with h | h | h
    · left
      have hh := midpoint_gap k hk h
      rw [he]
      convert hh using 1
      dsimp [d]
      field_simp
      ring
    · exact Or.inr (Or.inl (by simpa only [he,d] using h))
    · exact Or.inr (Or.inr h)
  have hh := three_gap_cases (by positivity : 0 < 1/d) (by positivity : 0 < 1/(d-1))
      huv hm0 (he.symm ▸ hm) cases'
  have eq : (1/d)*(1/(d-1))^2/96 = 1/(96*d*(d-1)^2) := by field_simp; ring
  linarith

/-- Eliminate the continuous grid approximation: an actual integer split
    beats any moderate score satisfying one of the three certificates. -/
theorem exists_better_split (k q : ℕ) (hk : 0 < k)
    (hq : 4*(k+2)*(k+1) ≤ q) {M m : ℝ} (hm : 1/((k:ℝ)+1) ≤ m)
    (cases : M ≤ score k (midpoint k) ∨
       M*(1/((k:ℝ)+2))*(1/((k:ℝ)+1))/4 ≤ score k (peak k)-M ∨
       M*m^2/16 ≤ score k (peak k)-M) :
    ∃ s : ℕ, 0 < s ∧ s < q ∧ M < score k ((s:ℝ)/q) := by
  have hg : 2*(k+2) ≤ q := le_trans (by nlinarith) hq
  obtain ⟨s, hsp, hsq, hs⟩ := nearest_split k q hg
  exact ⟨s, hsp, hsq, quadratic_exclusion k q hk hq hs hm cases⟩

end Nonoverlap.Upper
