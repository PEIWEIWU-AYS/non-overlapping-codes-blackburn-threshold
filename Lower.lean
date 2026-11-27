import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace NonoverlapThreshold.Lower

/-- Coefficients of the inverse of 1 - a z - z². -/
def tile (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => a
  | j + 2 => a * tile a (j+1) + tile a j

/-- The same recurrence after dividing the jth term by a^j, with d=a⁻². -/
def normTile (d : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | j+2 => normTile d (j+1) + d * normTile d j

theorem scale_tile {a : ℝ} (ha : 0 < a) (j : ℕ) :
    tile a j = a^j * normTile (1/a^2) j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [tile,normTile]
  | one => simp [tile,normTile]
  | more j hprev hnext =>
    rw [tile, normTile, hprev, hnext]
    rw [show a^(j+1) = a^j*a by ring, show a^(j+2) = a^j*a^2 by ring]
    field_simp
    ring

/-- Linear bounds for a weakly perturbed Fibonacci recurrence throughout the
    required range; the last term can grow by at most 2d per step. -/
theorem normTile_bounds {d : ℝ} {N : ℕ} (hd : 0 ≤ d) (hN : 2*(N:ℝ)*d ≤ 1)
    (j : ℕ) (hj : j ≤ N) :
    1 ≤ normTile d j ∧ normTile d j ≤ 2 ∧
    1 + ((j:ℝ)-1)*d ≤ normTile d j ∧ normTile d j ≤ 1+2*(j:ℝ)*d := by
  induction j using Nat.twoStepInduction with
  | zero => simp [normTile]; linarith
  | one =>
    simp only [normTile, Nat.cast_one, sub_self, zero_mul, add_zero, mul_one]
    exact ⟨le_rfl, by norm_num, le_rfl, by linarith⟩
  | more j hprev hnext =>
    obtain ⟨hp1,hp2,_,_⟩ := hprev (by omega)
    obtain ⟨hn1,_,hnl,hnu⟩ := hnext (by omega)
    have inc1 := mul_le_mul_of_nonneg_left hp1 hd
    have inc2 := mul_le_mul_of_nonneg_left hp2 hd
    have castj : (j:ℝ)+2 ≤ (N:ℝ) := by exact_mod_cast hj
    have bd := mul_le_mul_of_nonneg_right castj hd
    rw [normTile]
    push_cast at hnl hnu ⊢
    refine ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

/-- For the split with one level-two left word and no further left words,
    R_j = b F_{j−1} − F_{j−2}, j≥2, where F_j=tile a j. -/
def perturbed (a b : ℝ) (j : ℕ) := b * tile a (j+1) - tile a j

/-- Here n = j+4. The inequality compares the perturbed construction to
    the Blackburn code with the same one-letter split. -/
theorem perturbation_beats_split {a b : ℝ} (j : ℕ) (ha : 0 < a) (hb : 0 ≤ b)
    (hlarge : 2*((j:ℝ)+4) ≤ a^2)
    (hgain : 2*((j:ℝ)+2) < (((j:ℝ)+2)*b-a)*a) :
    b*a^(j+3) < perturbed a b (j+2) := by
  have hd : 0 ≤ 1/a^2 := by positivity
  have hN : 2*((j+4:ℕ):ℝ)*(1/a^2) ≤ 1 := by
    push_cast
    rwa [← mul_div_assoc, mul_one, div_le_one (by positivity : 0<a^2)]
  obtain ⟨_,_,hl,_⟩ := normTile_bounds hd hN (j+3) (by omega)
  obtain ⟨_,_,_,hu⟩ := normTile_bounds hd hN (j+2) (by omega)
  push_cast at hl hu
  dsimp [perturbed]
  rw [scale_tile ha,scale_tile ha]
  change b*a^(j+3) < b * (a^(j+3)*normTile (1/a^2) (j+3)) - a^(j+2)*normTile (1/a^2) (j+2)
  have aux : b*a < b*a*normTile (1/a^2) (j+3) - normTile (1/a^2) (j+2) := by
    have hlo := mul_le_mul_of_nonneg_left hl (show 0 ≤ b*a by positivity)
    rw [show (j:ℝ)+3-1 = (j:ℝ)+2 by ring] at hlo
    have hstep : b*a < b*a*(1+((j:ℝ)+2)*(1/a^2))-(1+2*((j:ℝ)+2)*(1/a^2)) := by
      field_simp
      rw [lt_div_iff₀ (by positivity : 0 < a^2)]
      nlinarith
    linarith
  have hh := mul_lt_mul_of_pos_left aux (show 0 < a^(j+2) by positivity)
  nlinarith [show a^(j+3) = a^(j+2)*a by ring]

/-- Integer cardinality at length j+2 with exactly one word assigned to L₂
    and all later left levels empty. R₂=a*b−1, R₃=a*R₂+b. -/
def rightCount (a b : ℕ) : ℕ → ℕ
  | 0 => a*b-1
  | 1 => a*(a*b-1)+b
  | j+2 => a*rightCount a b (j+1)+rightCount a b j

theorem rightCount_eq (a b : ℕ) (hab : 1 ≤ a*b) (j : ℕ) :
    (rightCount a b j : ℝ) = perturbed a b j := by
  induction j using Nat.twoStepInduction with
  | zero =>
    simp [rightCount,perturbed,tile,Nat.cast_sub hab]
    ring
  | one =>
    simp [rightCount,perturbed,tile,Nat.cast_sub hab]
    ring
  | more j hp hn =>
    simp only [rightCount,Nat.cast_add,Nat.cast_mul,hp,hn]
    unfold perturbed
    rw [show tile (a:ℝ) (j+2+1) = a * tile (a:ℝ) (j+2) + tile (a:ℝ) (j+1) by rfl]
    rw [show tile (a:ℝ) (j+2) = a * tile (a:ℝ) (j+1) + tile (a:ℝ) j by rfl]
    ring

/-- n=2k+4+e for e=0 or 1. These splits cover every length n≥12. -/
theorem quadratic_family (k e : ℕ) (hk : 4 ≤ k) (he : e ≤ 1) :
    let j := 2*k+e
    let a := k*(j+4)+1+e
    let b := k+1
    b*a^(j+3) < rightCount a b (j+2) := by
  let j := 2*k+e
  let a := k*(j+4)+1+e
  let b := k+1
  change b*a^(j+3) < rightCount a b (j+2)
  have hab : 1 ≤ a*b := by
    apply Nat.one_le_iff_ne_zero.mpr
    dsimp [a,b]
    positivity
  have hΔ : ((j:ℝ)+2)*(b:ℝ)-(a:ℝ) = 1 := by
    dsimp [a,b,j]
    push_cast
    ring
  have hka : 2*(j+4) < a := by
    have hmul := Nat.mul_le_mul_right (j+4) (show 2 ≤ k by omega)
    dsimp [a]
    omega
  have hka' : 2*((j:ℝ)+4) < (a:ℝ) := by exact_mod_cast hka
  have ha : 0 < (a:ℝ) := by positivity
  have ha1 : 1 ≤ (a:ℝ) := by exact_mod_cast (show 1 ≤ a by omega)
  have hs : 2*((j:ℝ)+4) ≤ (a:ℝ)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) ha.le]
  have hg : 2*((j:ℝ)+2) < (((j:ℝ)+2)*(b:ℝ)-(a:ℝ))*(a:ℝ) := by rw [hΔ]; linarith
  have h := perturbation_beats_split j ha (Nat.cast_nonneg b) hs hg
  rw [← rightCount_eq a b hab (j+2)] at h
  exact_mod_cast h

/-- The remainder dictates the two nearest integer Blackburn splits.
    q=kn+r with r=k+2+e and n=2k+4+e, so n/2≤r<n. -/
theorem family_parameters (k e : ℕ) (hk : 4 ≤ k) (he : e ≤ 1) :
    let n := 2*k+4+e
    let r := k+2+e
    let a := k*n+1+e
    let b := k+1
    let q := k*n+r
    a+b=q ∧ n≤2*r ∧ r<n ∧ n/2-2=k ∧ (n+1)/2=r ∧ 1≤a*b := by
  dsimp only
  refine ⟨by omega,by omega,by omega,by omega,by omega,?_⟩
  apply Nat.one_le_iff_ne_zero.mpr
  positivity

/-- For each length n≥12 the explicit perturbation beats its one-letter split
    at an alphabet size q satisfying 2q≥n²−4n. -/
theorem every_length (n : ℕ) (hn : 12 ≤ n) :
    ∃ k r a b q : ℕ, k=n/2-2 ∧ r=(n+1)/2 ∧ q=k*n+r ∧ a+b=q ∧
      n≤2*r ∧ r<n ∧ n^2≤2*q+4*n ∧
      b*a^(n-1) < rightCount a b (n-2) := by
  let k := n/2-2
  let e := n%2
  have hk : 4≤k := by dsimp [k]; omega
  have he : e≤1 := by dsimp [e]; omega
  have hrep : n=2*k+4+e := by dsimp [k,e]; omega
  set N := 2*k+4+e
  have hnN : n=N := hrep
  let r := k+2+e
  let a := k*N+1+e
  let b := k+1
  let q := k*N+r
  obtain ⟨hsum,hmiddle,hr,_,hceil,_⟩ := family_parameters k e hk he
  have hquad : N^2 ≤ 2*q+4*N := by
    have hh : e=0 ∨ e=1 := by omega
    rcases hh with hh|hh <;> dsimp [q,r,N] <;> rw [hh] <;> nlinarith
  have hwin := quadratic_family k e hk he
  dsimp only at hwin
  have h3 : 2*k+e+3=n-1 := by omega
  have h2 : 2*k+e+2=n-2 := by omega
  have h4 : 2*k+e+4=N := by dsimp [N]; omega
  rw [h3,h2,h4] at hwin
  exact ⟨k,r,a,b,q,rfl,by simpa [hnN,r,N] using hceil.symm,by rw [hnN],
    hsum,by simpa [hnN,r,N] using hmiddle,by simpa [hnN,r,N] using hr,
    by simpa [hnN] using hquad,hwin⟩

end NonoverlapThreshold.Lower
