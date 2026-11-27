import Analytic

/-! Two-sided pointwise control of the Blackburn polynomial and the finite
scalar estimates for the linear error in the alphabet threshold. -/
noncomputable section
namespace Nonoverlap.SharpAnalysis
open Nonoverlap.Analytic

private def tilt (k : ℕ) (v x : ℝ) :=
  score k x + (((k:ℝ)+2)*v/2)*(x-peak k)^2

private lemma deriv_tilt (k : ℕ) (v x : ℝ) :
    HasDerivAt (tilt k v) (((k:ℝ)+2)*(peak k-x)*(x^k-v)) x := by
  have h := (hder k x).add ((((hasDerivAt_id x).sub (hasDerivAt_const x (peak k))).pow 2).const_mul (((k:ℝ)+2)*v/2))
  convert h using 1
  simp
  ring

private lemma cont_tilt (k : ℕ) (v : ℝ) : Continuous (tilt k v) :=
  continuous_iff_continuousAt.mpr fun x => (deriv_tilt k v x).continuousAt

/-- If the power factor in the derivative lies between L and H along the
segment, the peak loss lies between the two corresponding quadratics on
either side of the peak. -/
theorem two_sided_loss (k : ℕ) (x L H : ℝ)
    (bounds : ∀ z ∈ Set.uIcc x (peak k), L ≤ z^k ∧ z^k ≤ H) :
    (((k:ℝ)+2)*L/2)*(x-peak k)^2 ≤ score k (peak k)-score k x ∧
    score k (peak k)-score k x ≤ (((k:ℝ)+2)*H/2)*(x-peak k)^2 := by
  have lc : tilt k L x ≤ tilt k L (peak k) := by
    rcases le_total x (peak k) with h|h
    · rw [Set.uIcc_of_le h] at bounds
      apply (monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x (peak k))
        (cont_tilt k L).continuousOn (fun z _ => (deriv_tilt k L z).hasDerivWithinAt) ?_)
        ⟨le_rfl,h⟩ ⟨h,le_rfl⟩ h
      intro z hz
      have hz' : z ∈ Set.Icc x (peak k) := interior_subset hz
      exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hz'.2))
        (sub_nonneg.mpr (bounds z hz').1)
    · rw [Set.uIcc_of_ge h] at bounds
      apply (antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (peak k) x)
        (cont_tilt k L).continuousOn (fun z _ => (deriv_tilt k L z).hasDerivWithinAt) ?_)
        ⟨le_rfl,h⟩ ⟨h,le_rfl⟩ h
      intro z hz
      have hz' : z ∈ Set.Icc (peak k) x := interior_subset hz
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hz'.1))
        (sub_nonneg.mpr (bounds z hz').1)
  have hc : tilt k H (peak k) ≤ tilt k H x := by
    rcases le_total x (peak k) with h|h
    · rw [Set.uIcc_of_le h] at bounds
      apply (antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x (peak k))
        (cont_tilt k H).continuousOn (fun z _ => (deriv_tilt k H z).hasDerivWithinAt) ?_)
        ⟨le_rfl,h⟩ ⟨h,le_rfl⟩ h
      intro z hz
      have hz' : z ∈ Set.Icc x (peak k) := interior_subset hz
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) (sub_nonneg.mpr hz'.2))
        (sub_nonpos.mpr (bounds z hz').2)
    · rw [Set.uIcc_of_ge h] at bounds
      apply (monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (peak k) x)
        (cont_tilt k H).continuousOn (fun z _ => (deriv_tilt k H z).hasDerivWithinAt) ?_)
        ⟨le_rfl,h⟩ ⟨h,le_rfl⟩ h
      intro z hz
      have hz' : z ∈ Set.Icc (peak k) x := interior_subset hz
      exact mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hz'.1))
        (sub_nonpos.mpr (bounds z hz').2)
  unfold tilt at lc hc
  simp at lc hc
  constructor <;> linarith

/-- The power occurring in the derivative is k-Lipschitz on the unit interval. -/
theorem power_difference (k : ℕ) {x y : ℝ} (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    |x^k-y^k| ≤ |x-y| * k := by
  have h := abs_pow_sub_pow_le x y k
  rw [abs_of_nonneg hx.1, abs_of_nonneg hy.1] at h
  have hb : (max x y)^(k-1) ≤ 1 := pow_le_one₀ (le_max_of_le_left hx.1) (max_le hx.2 hy.2)
  exact h.trans (mul_le_of_le_one_right (by positivity) hb)

/-- A radius r/n² gives relative control on curvature with an additive
error r/n. This applies to the root and to the nearest alphabet split. -/
theorem local_peak_loss (k : ℕ) {x r : ℝ} (hx : x ∈ Set.Icc 0 1) (hr : 0 ≤ r)
    (near : |x-peak k| ≤ r/((k:ℝ)+2)^2) :
    let n := (k:ℝ)+2
    let P := (peak k)^k
    (n*(P-r/n)/2)*(x-peak k)^2 ≤ score k (peak k)-score k x ∧
    score k (peak k)-score k x ≤ (n*(P+r/n)/2)*(x-peak k)^2 := by
  dsimp only
  apply two_sided_loss
  intro z hz
  have hc : peak k ∈ Set.Icc 0 1 := by
    constructor
    · unfold peak; positivity
    · unfold peak; apply (div_le_iff₀ (by positivity)).2; linarith
  have hz01 : z ∈ Set.Icc 0 1 := (Set.uIcc_subset_Icc hx hc) hz
  have hd : |z-peak k| ≤ |x-peak k| := by
    simpa only [← Real.dist_eq] using Real.dist_right_le_of_mem_uIcc hz
  have h1 := (power_difference k hz01 hc).trans
    (mul_le_mul_of_nonneg_right (hd.trans near) (Nat.cast_nonneg k))
  have h2 : r/((k:ℝ)+2)^2*k ≤ r/((k:ℝ)+2) := by
    have h3 : (k:ℝ) ≤ (k:ℝ)+2 := by linarith
    calc
      _ ≤ r/((k:ℝ)+2)^2*((k:ℝ)+2) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by field_simp; ring
  have h3 := abs_le.mp (h1.trans h2)
  constructor <;> linarith

/-- Moving toward the peak along the interval cannot lower the score. -/
private theorem toward_peak (k : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : y ∈ Set.uIcc x (peak k)) :
    score k x ≤ score k y := by
  have hc : 0 ≤ peak k := by unfold peak; positivity
  rcases le_total x (peak k) with h|h
  · rw [Set.uIcc_of_le h] at hy
    apply (monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x (peak k))
      (continuous_iff_continuousAt.mpr (fun z => (hder k z).continuousAt)).continuousOn
      (fun z _ => (hder k z).hasDerivWithinAt) ?_) ⟨le_rfl,h⟩ hy hy.1
    intro z hz
    have zz : z ∈ Set.Icc x (peak k) := interior_subset hz
    exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr zz.2))
      (pow_nonneg (hx.trans zz.1) _)
  · rw [Set.uIcc_of_ge h] at hy
    apply (antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (peak k) x)
      (continuous_iff_continuousAt.mpr (fun z => (hder k z).continuousAt)).continuousOn
      (fun z _ => (hder k z).hasDerivWithinAt) ?_) hy ⟨h,le_rfl⟩ hy.2
    intro z hz
    have zz : z ∈ Set.Icc (peak k) x := interior_subset hz
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr zz.1))
      (pow_nonneg (hc.trans zz.1) _)

/-- A root whose loss is at most half an inverse cube is within three inverse
squares of the peak. Only a local derivative estimate is needed. -/
theorem localize (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hn : 564 ≤ (k:ℝ)+2) (hp : 1/3 ≤ (peak k)^k)
    (hgap : score k (peak k)-score k t ≤ 1/(2*((k:ℝ)+2)^3)) :
    |t-peak k| ≤ 3/((k:ℝ)+2)^2 := by
  classical
  let n := (k:ℝ)+2
  change 564 ≤ n at hn
  change _ ≤ 1/(2*n^3) at hgap
  change |t-peak k| ≤ 3/n^2
  have npos : 0 < n := by linarith
  have rpos : 0 ≤ 3/n^2 := by positivity
  have hcoef : 1/4 ≤ (peak k)^k-3/n := by
    have hsmall : 3/n ≤ 1/12 := by
      rw [div_le_iff₀ npos]
      calc
        (3:ℝ) = 1/12*36 := by norm_num
        _ ≤ (1/12)*n := mul_le_mul_of_nonneg_left ((by norm_num : (36:ℝ) ≤ 564).trans hn) (by norm_num)
    linarith
  by_cases hclose : |t-peak k| ≤ 3/n^2
  · exact hclose
  have h := lt_of_not_ge hclose
  obtain ⟨y,hy,hyabs⟩ : ∃ y ∈ Set.uIcc t (peak k), |y-peak k|=3/n^2 := by
    rcases le_total t (peak k) with hh|hh
    · rw [Set.uIcc_of_le hh]
      rw [abs_of_nonpos (sub_nonpos.mpr hh)] at h
      refine ⟨peak k-3/n^2, ⟨by linarith,by linarith⟩, ?_⟩
      rw [abs_of_nonpos (by linarith)]; ring
    · rw [Set.uIcc_of_ge hh]
      rw [abs_of_nonneg (sub_nonneg.mpr hh)] at h
      refine ⟨peak k+3/n^2, ⟨by linarith,by linarith⟩, ?_⟩
      rw [abs_of_nonneg (by linarith)]; ring
  have hc : peak k ∈ Set.Icc 0 1 := by
    constructor
    · unfold peak; positivity
    · unfold peak; apply (div_le_iff₀ (by positivity)).2; linarith
  have hc' := (local_peak_loss k (Set.uIcc_subset_Icc ht hc hy) (by norm_num : (0:ℝ) ≤ 3)
    (le_of_eq hyabs)).1
  have hmove := toward_peak k ht.1 hy
  have hsq : (y-peak k)^2=(3/n^2)^2 := by rw [← sq_abs,hyabs]
  change n*((peak k)^k-3/n)/2 * _ ≤ _ at hc'
  rw [hsq] at hc'
  have hbad : n*(1/4)/2*(3/n^2)^2 ≤ 1/(2*n^3) :=
    (mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hcoef npos.le] :
      n*(1/4)/2 ≤ n*((peak k)^k-3/n)/2) (sq_nonneg _)).trans (by linarith)
  have exactCost : n*(1/4)/2*(3/n^2)^2=9/(8*n^3) := by field_simp; ring
  rw [exactCost,div_le_div_iff₀ (by positivity) (by positivity)] at hbad
  exact (by nlinarith only [hbad,pow_pos npos 3] : False).elim

/-- The normalized root displacement need not have either sign. The
quadratic and endpoint lower bounds cost at most 141/n in total. -/
theorem normalized_loss {n u w h d : ℝ} (hn : 0 < n) (hu : |u| ≤ 3)
    (hw : |w-1| ≤ 25/n)
    (hshape : (1-9/n)*u^2/2 ≤ h)
    (htail : w*(1-u) ≤ d) : 1/2-141/n ≤ h+d := by
  have hu' := abs_le.mp hu
  have hu2 : u^2 ≤ 9 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 3-u) (by linarith : 0 ≤ 3+u)]
  have h1u : |1-u| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  have hmul : |(w-1)*(1-u)| ≤ (25/n)*4 := by
    rw [abs_mul]
    exact mul_le_mul hw h1u (abs_nonneg _) (by positivity)
  have he := (abs_le.mp hmul).1
  have herr := mul_le_mul_of_nonneg_left hu2 (show (0:ℝ) ≤ 9/n by positivity)
  have hninv : 0 ≤ 1/n := by positivity
  simp only [div_eq_mul_inv] at he herr hshape hninv ⊢
  nlinarith [sq_nonneg (u-1)]

/-- An explicit upper bound for the exceptional alphabet, from the two
normalized score estimates. The constants are uniform in the length. -/
theorem linear_error {n q gap : ℝ} (hn : 564 ≤ n)
    (hlo : 1/2-141/n ≤ gap)
    (hhi : gap*(8*q^2) ≤ n^4*(1+3/n)) :
    q ≤ n^2/2+143*n := by
  classical
  have npos : 0 < n := by linarith
  have hcross := (mul_le_mul_of_nonneg_right hlo (by positivity : (0:ℝ) ≤ 8*q^2)).trans hhi
  have hclean : (n-282)*(4*q^2) ≤ n^4*(n+3) := by
    convert mul_le_mul_of_nonneg_right hcross npos.le using 1 <;> field_simp
    ring
  by_contra! h
  have hpoly : n^4*3+n^5 < (n-282)*(n^2+286*n)^2 := by
    have h1 : 0 ≤ n^2 := sq_nonneg n
    have h2 : 0 ≤ n^2*(n-564) := mul_nonneg h1 (by linarith)
    have h3 : 0 ≤ n^2*(n-564)^2 := mul_nonneg h1 (sq_nonneg _)
    nlinarith
  have hn' : 0 ≤ n^2+286*n := by positivity
  have hsq := pow_lt_pow_left₀ (show n^2+286*n < 2*q by linarith) hn' (by decide : (2:ℕ) ≠ 0)
  have hstrict := mul_lt_mul_of_pos_left hsq (by linarith : 0 < n-282)
  nlinarith

set_option maxHeartbeats 1200000 in
/-- Sharp finite exclusion, starting with the root and interior bounds of a
moderate profile and a nearest-grid competitor. Here the word length is k+2. -/
theorem exceptional_le (k : ℕ) {q x M F t : ℝ} (hn : 564 ≤ (k:ℝ)+2)
    (hq : ((k:ℝ)+2)^2/2 ≤ q) (hx : x ∈ Set.Icc 0 1)
    (hxnear : |x-peak k| ≤ 1/(2*q)) (hgrid : score k x ≤ M)
    (hf : 0 ≤ F) (hfm : F ≤ M)
    (hinterior : F/(16*((k:ℝ)+1)) ≤ score k (peak k)-M)
    (ht : t ∈ Set.Icc 0 1) (hm : M ≤ score k t)
    (htail : (M-F)*(t-(k:ℝ)/(k+1)) ≤ score k t-M) :
    q ≤ ((k:ℝ)+2)^2/2+143*((k:ℝ)+2) := by
  classical
  let n : ℝ := (k:ℝ)+2
  let c := peak k
  let P := c^k
  let g := score k c-M
  change 564 ≤ n at hn
  change n^2/2 ≤ q at hq
  change q ≤ n^2/2+143*n
  have np : 0 < n := by linarith
  have qp : 0 < q := lt_of_lt_of_le (div_pos (sq_pos_of_pos np) (by norm_num)) hq
  have kpos : 0 < (k:ℝ) := by dsimp [n] at hn; linarith
  have hp : 1/3 ≤ P := by
    have b := curvature_third (k:=k) (by exact_mod_cast kpos)
    apply b.trans (pow_le_pow_left₀ (by positivity) _ _)
    dsimp [c,peak]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have pp : 0 < P := by linarith
  have cs : 1-c=1/n := by dsimp [c,peak,n]; field_simp; ring
  have cp : n*score k c=P*c := by
    dsimp only [score,P]; rw [pow_succ,cs]; field_simp
  have cpos : 0 ≤ c := by dsimp [c,peak]; positivity
  have gt : 0 ≤ g := by
    have u := toward_peak k ht.1 (Set.right_mem_uIcc : peak k ∈ Set.uIcc t (peak k))
    dsimp only [g,c]; linarith
  have hqn : n^2 ≤ 2*q := by simpa only [mul_comm q] using (div_le_iff₀ (by norm_num : (0:ℝ)<2)).1 hq
  have close0 : 1/(2*q) ≤ 1/n^2 := one_div_le_one_div_of_le (sq_pos_of_pos np) hqn
  have xn := hxnear.trans close0
  have xs := pow_le_pow_left₀ (abs_nonneg _) xn 2
  rw [sq_abs] at xs
  have basic : g ≤ 1/(2*n^3) := calc
    g ≤ n/2*(x-c)^2 := by
      have b := rounding_loss k hx
      change score k c-score k x ≤ n/2*(x-c)^2 at b
      dsimp only [g]; linarith
    _ ≤ n/2*(1/n^2)^2 := mul_le_mul_of_nonneg_left xs (by positivity)
    _ = _ := by field_simp; ring
  have tn := localize k ht hn hp (by dsimp only [g,c] at basic; linarith)
  let u := n^2*(c-t)
  let w := n*(M-F)/P
  have uabs : |u| ≤ 3 := by
    dsimp only [u]; rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_sub_comm]
    apply (le_div_iff₀' (sq_pos_of_pos np)).1
    exact tn
  have fw : 0 ≤ w := div_nonneg (mul_nonneg np.le (sub_nonneg.mpr hfm)) pp.le
  have ineqF : F ≤ 16*(n-1)*g := by
    have h := (div_le_iff₀ (by positivity)).1 hinterior
    dsimp only [n,g,c]; nlinarith
  have mass : n*(g+F) ≤ 8/n := calc
    n*(g+F) ≤ n*(16*n*g) := mul_le_mul_of_nonneg_left (by nlinarith only [ineqF,gt]) np.le
    _ ≤ n*(16*n*(1/(2*n^3))) := by gcongr
    _ = _ := by field_simp; ring
  have wid : 1-w=1/n+n*(g+F)/P := by
    rw [← cs]
    dsimp only [w,g]
    field_simp [ne_of_gt pp]
    nlinarith only [cp]
  have wclose : |w-1| ≤ 25/n := by
    have mp : 0 ≤ n*(g+F)/P := div_nonneg (mul_nonneg np.le (add_nonneg gt hf)) pp.le
    have mb : n*(g+F)/P ≤ 24/n := by
      apply (div_le_iff₀ pp).2
      apply mass.trans
      have v := mul_le_mul_of_nonneg_left hp (show 0 ≤ 24/n by positivity)
      convert v using 1; ring
    have invpos : 0 ≤ n⁻¹ := inv_nonneg.mpr np.le
    simp only [div_eq_mul_inv] at wid mp mb ⊢
    rw [abs_le]; constructor <;> linarith only [wid,mp,mb,invpos]
  have tloc := (local_peak_loss k ht (by norm_num : (0:ℝ) ≤ 3) tn).1
  change n*(P-3/n)/2*(t-c)^2 ≤ score k c-score k t at tloc
  have coeff : (1-9/n)*P ≤ P-3/n := by
    have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ 9/n by positivity)
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith only [h]
  have shape : (1-9/n)*u^2/2 ≤ n^3*(score k c-score k t)/P := by
    apply (le_div_iff₀ pp).2
    calc
      _ = n^3*(n*((1-9/n)*P)/2*(t-c)^2) := by dsimp only [u]; ring
      _ ≤ n^3*(n*(P-3/n)/2*(t-c)^2) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left tloc (by positivity)
  have cut : 1/n^2 ≤ c-(k:ℝ)/(k+1) := by
    have a : c-(k:ℝ)/(k+1) = 1/(n*((k:ℝ)+1)) := by dsimp [n,c,peak]; field_simp; ring
    rw [a]
    apply one_div_le_one_div_of_le (by positivity)
    dsimp [n]; nlinarith
  have dist : 1-u ≤ n^2*(t-(k:ℝ)/(k+1)) := by
    have h := (div_le_iff₀ (sq_pos_of_pos np)).1 cut
    dsimp only [u]; nlinarith
  have tail : w*(1-u) ≤ n^3*(score k t-M)/P := calc
    _ ≤ w*(n^2*(t-(k:ℝ)/(k+1))) := mul_le_mul_of_nonneg_left dist fw
    _ = n^3*((M-F)*(t-(k:ℝ)/(k+1)))/P := by dsimp only [w]; ring
    _ ≤ _ := by gcongr
  have low := normalized_loss np uabs wclose shape tail
  apply linear_error (gap:=n^3*g/P) hn
  · convert low using 1; dsimp only [g]; ring
  · have xloc := (local_peak_loss k hx (by norm_num : (0:ℝ) ≤ 1) xn).2
    change score k c-score k x ≤ n*(P+1/n)/2*(x-c)^2 at xloc
    have y := pow_le_pow_left₀ (abs_nonneg _) hxnear 2
    rw [sq_abs] at y
    have gb : g ≤ n*(P+1/n)/2*(1/(2*q))^2 := calc
      g ≤ score k c-score k x := by dsimp only [g]; linarith
      _ ≤ _ := xloc.trans (mul_le_mul_of_nonneg_left y (by positivity))
    have c1 : P+1/n ≤ P*(1+3/n) := by
      have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ 3/n by positivity)
      simp only [div_eq_mul_inv] at h ⊢
      nlinarith only [h]
    calc
      n^3*g/P*(8*q^2) ≤ n^3*(n*(P+1/n)/2*(1/(2*q))^2)/P*(8*q^2) := by gcongr
      _ = n^4*(P+1/n)/P := by field_simp; ring
      _ ≤ n^4*(P*(1+3/n))/P := by gcongr
      _ = _ := by field_simp; ring

#print axioms exceptional_le

#print axioms two_sided_loss
#print axioms local_peak_loss
#print axioms normalized_loss
#print axioms linear_error
end Nonoverlap.SharpAnalysis
