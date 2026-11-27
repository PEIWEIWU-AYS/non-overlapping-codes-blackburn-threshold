import ExactSix
import ThresholdBounds

open NonoverlapThreshold.WordLower Nonoverlap.Representation Nonoverlap.Bridge
open NonoverlapThreshold
namespace Nonoverlap.Six

def sixGrid (q s : ℕ) := s^5*(q-s)
def smallUpperTarget (q : ℕ) : ℕ :=
  if q=2 then 3 else if q=3 then 41 else if q=4 then 251 else if q=9 then 33872 else
  max (sixGrid q (5*q/6)) (sixGrid q (5*q/6+1))

/-- An interval upper bound for the envelope after completing the square
in the third-level split. The left layer x ranges from lo to hi. -/
private def box (a b lo hi : ℕ) :=
  let yh := a*b-lo
  let yl := a*b-hi
  let H := max (a*a+hi) (a*b+yh)
  let L := max (a*a+lo) (a*b+yl)
  let T := a*yh+b*lo
  let B := a*yh+T-(L*(a-b)+a*lo)
  H*(a*T+hi*yh)+a*hi*T+B^2/4

private theorem box_sound {a b x y u v lo hi : ℕ}
    (hab : b≤a) (hlo : lo≤x) (hhi : x≤hi)
    (hxy : x+y=a*b) (huv : u+v=a*y+b*x) :
    envelope a b x y u v ≤ box a b lo hi := by
  let D := max (a*a+x) (a*b+y)
  let H := max (a*a+hi) (a*b+(a*b-lo))
  let L := max (a*a+lo) (a*b+(a*b-hi))
  let T := a*(a*b-lo)+b*lo
  let B := a*(a*b-lo)+T-(L*(a-b)+a*lo)
  have hy : y ≤ a*b-lo := by omega
  have ylo : a*b-hi ≤ y := by omega
  have hD : D ≤ H := max_le_max (by omega) (by omega)
  have hL : L ≤ D := max_le_max (by omega) (by omega)
  have hT : u+v ≤ T := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hab
    obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le hlo
    have ey : a*b-lo=y+e := by omega
    dsimp [T]
    rw [huv,ey,he,hd]
    nlinarith only [Nat.zero_le (d*e)]
  have hN : L*(a-b)+a*lo ≤ D*(a-b)+a*x :=
    Nat.add_le_add (Nat.mul_le_mul_right _ hL) (Nat.mul_le_mul_left _ hlo)
  have hpos : a*y+(u+v) ≤ B+(D*(a-b)+a*x) := by
    have e := Nat.add_le_add (Nat.mul_le_mul_left a hy) hT
    dsimp [B]
    omega
  have eqab : D*(a-b)+D*b=D*a := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hab]
  have hcoef : (D*b+a*y+(u+v))*u ≤ (D*a+a*x+B)*u :=
    Nat.mul_le_mul_right _ (by omega)
  have hbnd : D*(a*(u+v)+x*y)+a*x*(u+v) ≤ H*(a*T+hi*(a*b-lo))+a*hi*T :=
    Nat.add_le_add (Nat.mul_le_mul hD (Nat.add_le_add (Nat.mul_le_mul_left _ hT)
      (Nat.mul_le_mul hhi hy))) (Nat.mul_le_mul (Nat.mul_le_mul_left _ hhi) hT)
  have heq : envelope a b x y u v + u*u + (D*a+a*x)*u =
      D*(a*(u+v)+x*y)+a*x*(u+v)+(D*b+a*y+(u+v))*u := by
    unfold envelope
    rw [max_eq_left hab]
    change D * _ + _ + _ + _ + _ = _
    ring
  have sq : 4*(B*u) ≤ B^2+4*(u*u) := by
    zify
    nlinarith only [sq_nonneg ((B:ℤ)-2*(u:ℤ))]
  have ha4 : 4*envelope a b x y u v ≤ 4*(H*(a*T+hi*(a*b-lo))+a*hi*T)+B^2 := by
    nlinarith only [heq,hcoef,hbnd,sq]
  change envelope a b x y u v ≤ H*(a*T+hi*(a*b-lo))+a*hi*T+B^2/4
  omega

private def checkBox (a b K : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, lo, hi => decide (box a b lo hi ≤ K)
  | d+1, lo, hi =>
    if box a b lo hi ≤ K then true else
      checkBox a b K d lo ((lo+hi)/2) && checkBox a b K d ((lo+hi)/2+1) hi

private theorem check_sound {a b x y u v K : ℕ} (hab : b≤a)
    (hxy : x+y=a*b) (huv : u+v=a*y+b*x) (d lo hi : ℕ)
    (hlo : lo≤x) (hhi : x≤hi) (pass : checkBox a b K d lo hi = true) :
    envelope a b x y u v ≤ K := by
  induction d generalizing lo hi with
  | zero => exact (box_sound hab hlo hhi hxy huv).trans (of_decide_eq_true pass)
  | succ d ih =>
    unfold checkBox at pass
    split at pass
    · exact (box_sound hab hlo hhi hxy huv).trans (by assumption)
    · simp only [Bool.and_eq_true] at pass
      obtain ⟨p,r⟩ := pass
      by_cases hm : x≤(lo+hi)/2
      · exact ih lo ((lo+hi)/2) hlo hm p
      · exact ih ((lo+hi)/2+1) hi (by omega) hhi r

private def feasible (q : ℕ) : Bool :=
  (List.range (q+1)).all fun a =>
    let b := q-a
    decide (a<b) || checkBox a b (smallUpperTarget q) 14 0 (a*b)

-- A finite, kernel-checked interval certificate for each alphabet below
-- the uniform bound 4 · 6 · 5. Each row uses at most fourteen subdivisions.
private theorem cap_from_row {q a b x y u v : ℕ} (pass : feasible q = true)
    (first : a+b=q) (order : b≤a) (two : x+y=a*b) (three : u+v=a*y+b*x) :
    envelope a b x y u v ≤ smallUpperTarget q := by
  have e := List.all_eq_true.mp pass a (List.mem_range.mpr (by omega))
  change (decide (a<q-a) || checkBox a (q-a) (smallUpperTarget q) 14 0 (a*(q-a)))=true at e
  rw [show q-a=b by omega] at e
  simp only [show ¬a<b by omega,decide_false,Bool.false_or] at e
  exact check_sound order two three 14 0 (a*b) (by omega) (by omega) e

private theorem bound_from_row {q a b x y u v : ℕ} (pass : feasible q = true)
    (first : a+b=q) (two : x+y=a*b) (three : u+v=a*y+b*x) :
    envelope a b x y u v ≤ smallUpperTarget q := by
  rcases le_total b a with h|h
  · exact cap_from_row pass first h two three
  · have sw := cap_from_row pass (a:=b) (b:=a) (x:=y) (y:=x) (u:=v) (v:=u)
      (by omega) h (by simpa [Nat.add_comm,Nat.mul_comm] using two)
      (by simpa [Nat.add_comm] using three)
    convert sw using 1
    unfold envelope
    dsimp only
    rw [max_comm b a]
    rw [max_comm ((max a b)*b+y) ((max a b)*a+x)]
    ring

private theorem small_six_upper_of_row {q : ℕ} (pass : feasible q = true)
    (C : Finset (List (Fin q))) (hc : IsCode 6 C) : C.card ≤ smallUpperTarget q := by
  obtain ⟨l,r,first,law,hcap⟩ := word_code_profile 6 (by decide) C hc
  have h2 := law 2 (by decide)
  have h3 := law 3 (by decide)
  have h4 := law 4 (by decide)
  have h5 := law 5 (by decide)
  norm_num [convolution,Finset.sum_range_succ] at h2 h3 h4 h5 hcap
  apply hcap.trans
  apply le_trans _ (bound_from_row pass first h2 (show l 3+r 3=l 1*r 2 + r 1*l 2 by rw [h3]; ring))
  have bound := eliminate_last (k:=l 4) (z:=r 4) (p:=l 5) (s:=r 5)
    (show l 4+r 4=l 1*r 3+l 2*r 2+r 1*l 3 by rw [h4]; ring)
    (show l 5+r 5=l 1*r 4+l 2*r 3+l 3*r 2+r 1*l 4 by rw [h5]; ring)
  simpa only [Nat.add_assoc] using bound

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finite_table : (List.range 120).all feasible = true := by decide +kernel

theorem small_six_upper {q : ℕ} (hq : q < 120)
    (C : Finset (List (Fin q))) (hc : IsCode 6 C) : C.card ≤ smallUpperTarget q :=
  small_six_upper_of_row (List.all_eq_true.mp finite_table q (List.mem_range.mpr hq)) C hc

#print axioms small_six_upper
end Nonoverlap.Six
