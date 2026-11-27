import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace NonoverlapFive

def f0 (a b x : ℝ) : ℝ := a^4*b+a^2*(3*b-a)*x-(2*a-b)*x^2
def f1 (a b x : ℝ) : ℝ := 2*a^3*b^2-2*a*b*(a-b)*x-b*x^2

/-- Substitution of the four length-five level recurrences. -/
theorem eliminate (a b x y u v s t : ℝ)
    (hab : b ≤ a) (hst : 0 ≤ s) (hx : x+y=a*b)
    (hu : u+v=a*y+b*x) (hs : s+t=a*v+x*y+b*u)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) :
    a*t+x*v+u*y+s*b ≤ max (f0 a b x) (f1 a b x) := by
  have hy : y = a*b-x := by linarith
  have hv : v = a*y+b*x-u := by linarith
  have ht : t = a*v+x*y+b*u-s := by linarith
  by_cases h : 0 ≤ 2*a*b-a^2-2*x
  · apply le_trans _ (le_max_right _ _)
    have hnon := mul_nonneg h hv0
    have hsnon := mul_nonneg (sub_nonneg.mpr hab) hst
    rw [ht,hv,hy]
    rw [hv,hy] at hnon
    dsimp [f1]
    nlinarith only [hnon,hsnon]
  · apply le_trans _ (le_max_left _ _)
    have hnon := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hu0
    have hsnon := mul_nonneg (sub_nonneg.mpr hab) hst
    rw [ht,hv,hy]
    dsimp [f0]
    nlinarith only [hnon,hsnon]

theorem skew (a b x : ℝ) (hb : 0 ≤ b) (hx : 0 ≤ x) (h : 3*b ≤ a) :
    max (f0 a b x) (f1 a b x) ≤ a^4*b := by
  have ha : 0 ≤ a := by linarith
  apply max_le
  · dsimp [f0]
    have hs := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) (show 3*b-a ≤ 0 by linarith)) hx
    have ht := mul_nonneg (show 0 ≤ 2*a-b by linarith) (sq_nonneg x)
    nlinarith only [hs,ht]
  · dsimp [f1]
    have hs := mul_nonneg (show 0 ≤ a-2*b by linarith) (show 0 ≤ a^3*b by positivity)
    have ht := mul_nonneg (show 0 ≤ a-b by linarith) (show 0 ≤ 2*a*b*x by positivity)
    have hz := mul_nonneg hb (sq_nonneg x)
    nlinarith only [hs,ht,hz]

theorem moderate (a b x : ℝ) (hb : 0 < b) (hx : 0 ≤ x)
    (hba : b ≤ a) (hab : a ≤ 3*b) :
    1024 * max (f0 a b x) (f1 a b x) ≤ 81*(a+b)^5 := by
  let d := (a-b)/2
  let y := (3*b-a)/2
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have ha' : a = 3*d+y := by dsimp [d,y]; ring
  have hb' : b = d+y := by dsimp [d,y]; ring
  have hf : 0 < 2*a-b := by linarith
  rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1024)]
  apply max_le
  · have hD : 0 ≤ 81*(2*a-b)*(a+b)^5-256*a^4*((a+b)^2+4*b^2) := by
      rw [ha',hb']
      have eqn : 81*(2*(3*d+y)-(d+y))*((3*d+y)+(d+y))^5-
          256*(3*d+y)^4*(((3*d+y)+(d+y))^2+4*(d+y)^2) =
          32*y*(2160*d^5+4320*d^4*y+3480*d^3*y^2+1370*d^2*y^3+255*d*y^4+17*y^5) := by ring
      rw [eqn]; positivity
    have fac : 0 ≤ 4*(2*a-b)*(81*(a+b)^5-1024*(f0 a b x)) := by
      have e : 4*(2*a-b)*(81*(a+b)^5-1024*(f0 a b x)) =
          4*(81*(2*a-b)*(a+b)^5-256*a^4*((a+b)^2+4*b^2))+
          1024*(2*(2*a-b)*x - a^2*(3*b-a))^2 := by unfold f0; ring
      rw [e]; positivity
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right fac (by positivity))
  · have hE : 0 ≤ 81*(a+b)^5 - 2048*a^3*b^2 := by
      rw [ha',hb']
      have e : 81*((3*d+y)+(d+y))^5-2048*(3*d+y)^3*(d+y)^2 =
          32*(864*d^5+1296*d^4*y+720*d^3*y^2+296*d^2*y^3+106*d*y^4+17*y^5) := by ring
      rw [e]; positivity
    have ha : 0 ≤ a := by linarith
    have hX := mul_nonneg (show 0 ≤ a-b by linarith) (show 0 ≤ a*b*x by positivity)
    have hB := mul_nonneg hb.le (sq_nonneg x)
    unfold f1
    nlinarith only [hE,hX,hB]


/-- Best Blackburn code size among all integral first-level splits. -/
def blackburn (q : ℕ) : ℕ := (Finset.range (q+1)).sup (fun a => a^4*(q-a))

theorem blackburn_candidate {q t : ℕ} (h : t ≤ q) :
    t^4*(q-t) ≤ blackburn q := by
  exact Finset.le_sup (f := fun a => a^4*(q-a)) (Finset.mem_range.mpr (by omega))

/-- Above 19 the interval [3q/4,4q/5] contains an integer. -/
theorem round_bound (q : ℕ) (hq : 20 ≤ q) :
    81*(q:ℝ)^5 ≤ 1024*(blackburn q : ℝ) := by
  let t := 4*q/5
  have ht : t ≤ q := by dsimp [t]; omega
  have hu : 3*q ≤ 4*t := by dsimp [t]; omega
  have hv : 5*t ≤ 4*q := by dsimp [t]; omega
  let u : ℝ := 4*(t:ℝ)-3*(q:ℝ)
  let v : ℝ := 4*(q:ℝ)-5*(t:ℝ)
  have hu' : 0 ≤ u := by dsimp [u]; exact sub_nonneg.mpr (by exact_mod_cast hu)
  have hv' : 0 ≤ v := by dsimp [v]; exact sub_nonneg.mpr (by exact_mod_cast hv)
  have hq' : (q:ℝ) = 4*v+5*u := by dsimp [u,v]; ring
  have ht' : (t:ℝ) = 3*v+4*u := by dsimp [u,v]; ring
  have e : 1024*(3*v+4*u)^4*((4*v+5*u)-(3*v+4*u))-81*(4*v+5*u)^5 =
      u*(6912*v^4+31104*v^3*u+51168*v^2*u^2+36076*v*u^3+9019*u^4) := by ring
  have he : 81*(q:ℝ)^5 ≤ 1024*(t:ℝ)^4*((q:ℝ)-(t:ℝ)) := by
    rw [hq',ht']
    apply sub_nonneg.mp
    rw [e]; positivity
  have hb : (t:ℝ)^4*((q:ℝ)-(t:ℝ)) ≤ (blackburn q:ℝ) := by
    have h := blackburn_candidate ht
    have h' : ((t^4*(q-t):ℕ):ℝ) ≤ (blackburn q:ℝ) := by exact_mod_cast h
    simpa [Nat.cast_sub ht] using h'
  linarith

/-- Computable integer forms of the two endpoints of the third-level partition. -/
def f0Z (a b x : ℤ) : ℤ := a^4*b+a^2*(3*b-a)*x-(2*a-b)*x^2
def f1Z (a b x : ℤ) : ℤ := 2*a^3*b^2-2*a*b*(a-b)*x-b*x^2

def smallTarget (q : ℕ) : ℕ :=
  if q = 2 then 2 else if q = 3 then 17 else blackburn q

def smallCheck (q : ℕ) : Bool :=
  (List.range (q+1)).all fun a =>
    let b := q-a
    if 0 < b ∧ b ≤ a then
      (List.range (a*b+1)).all fun x =>
        decide (f0Z a b x ≤ (smallTarget q : ℤ) ∧ f1Z a b x ≤ (smallTarget q : ℤ))
    else true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem small_table : (List.range 20).all smallCheck = true := by decide +kernel

theorem small_bounds (a b x : ℕ) (hb : 0 < b) (hba : b ≤ a)
    (h : a+b < 20) (hx : x ≤ a*b) :
    max (f0 a b x) (f1 a b x) ≤ (smallTarget (a+b):ℝ) := by
  have H := List.all_eq_true.mp small_table (a+b) (List.mem_range.mpr h)
  simp only [smallCheck] at H
  have K := List.all_eq_true.mp H a (List.mem_range.mpr (by omega))
  have e : a + b - a = b := by omega
  simp only [e, hb, hba, and_self, if_true] at K
  have P := List.all_eq_true.mp K x (List.mem_range.mpr (by omega))
  have V := of_decide_eq_true P
  have h0 : f0 a b x ≤ (smallTarget (a+b):ℝ) := by
    have hcast : ((f0Z a b x : ℤ) : ℝ) ≤ (((smallTarget (a+b):ℕ):ℤ):ℝ) := by
      exact_mod_cast V.1
    simpa [f0,f0Z] using hcast
  have h1 : f1 a b x ≤ (smallTarget (a+b):ℝ) := by
    have hcast : ((f1Z a b x : ℤ) : ℝ) ≤ (((smallTarget (a+b):ℕ):ℤ):ℝ) := by
      exact_mod_cast V.2
    simpa [f1,f1Z] using hcast
  exact max_le h0 h1


theorem ordered_upper (a b x y u v s t : ℕ) (hb : 0 < b) (hba : b ≤ a)
    (hx : x+y=a*b) (hu : u+v=a*y+b*x) (hs : s+t=a*v+x*y+b*u) :
    a*t+x*v+u*y+s*b ≤ smallTarget (a+b) := by
  have ea : (b:ℝ) ≤ a := by exact_mod_cast hba
  have eb : (0:ℝ) < b := by exact_mod_cast hb
  have h := eliminate (a:ℝ) b x y u v s t ea (by positivity)
    (by exact_mod_cast hx) (by exact_mod_cast hu) (by exact_mod_cast hs)
    (by positivity) (by positivity)
  have goalR : (a:ℝ)*t+x*v+u*y+s*b ≤ (smallTarget (a+b):ℝ) := by
    by_cases hq : a+b < 20
    · exact h.trans (small_bounds a b x hb hba hq (by omega))
    · rw [smallTarget,if_neg (by omega),if_neg (by omega)]
      by_cases hratio : 3*(b:ℝ) ≤ a
      · have hcan := blackburn_candidate (show a ≤ a+b by omega)
        simp only [Nat.add_sub_cancel_left] at hcan
        have hcast : (a:ℝ)^4*b ≤ (blackburn (a+b):ℝ) := by exact_mod_cast hcan
        exact (h.trans (skew a b x eb.le (by positivity) hratio)).trans hcast
      · have hm := moderate a b x eb (by positivity) ea (le_of_not_ge hratio)
        have hr := round_bound (a+b) (by omega)
        rw [Nat.cast_add] at hr
        linarith
  exact_mod_cast goalR

/-- All choices of integer cardinalities in the nested partitions through level four. -/
def Attain (q size : ℕ) : Prop :=
  ∃ a b x y u v s t : ℕ,
    0 < a ∧ 0 < b ∧ a+b=q ∧ x+y=a*b ∧ u+v=a*y+b*x ∧
      s+t=a*v+x*y+b*u ∧ size=a*t+x*v+u*y+s*b

theorem upper {q m : ℕ} (hm : Attain q m) : m ≤ smallTarget q := by
  obtain ⟨a,b,x,y,u,v,s,t,ha,hb,rfl,hx,hu,hs,rfl⟩ := hm
  by_cases e : b ≤ a
  · exact ordered_upper a b x y u v s t hb e hx hu hs
  · have H := ordered_upper b a y x v u t s ha (by omega)
        (by simpa [add_comm,mul_comm] using hx)
        (by simpa [add_comm,mul_comm] using hu)
        (by simpa only [add_comm,add_left_comm,add_assoc,mul_comm] using hs)
    convert H using 1 <;> ring_nf

theorem attain_blackburn (q : ℕ) (hq : 2 ≤ q) : Attain q (blackburn q) := by
  have hpos := blackburn_candidate (show 1 ≤ q by omega)
  simp at hpos
  have hne : (Finset.range (q+1)).Nonempty := Finset.nonempty_range_succ
  obtain ⟨a,ha,hA⟩ := Finset.exists_mem_eq_sup _ hne (fun a => a^4*(q-a))
  have hsize : blackburn q = a^4*(q-a) := hA
  have ham : a ≤ q := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using ha
  have hap : 0 < a := by
    by_contra! h
    have hh : a=0 := by omega
    simp [hh] at hsize
    omega
  have hbp : 0 < q-a := by
    by_contra! h
    have hh : q-a=0 := by omega
    simp [hh] at hsize
    omega
  refine ⟨a,q-a,0,a*(q-a),0,a^2*(q-a),0,a^3*(q-a),hap,hbp,by omega,?_,?_,?_,?_⟩
  · ring
  · ring
  · ring
  · rw [hsize]; ring

theorem attain_exact (q : ℕ) (hq : 2 ≤ q) : Attain q (smallTarget q) := by
  by_cases e : q=2
  · subst q; exact ⟨1,1,0,1,1,0,0,1,by decide⟩
  by_cases e' : q=3
  · subst q; exact ⟨2,1,1,1,0,3,0,7,by decide⟩
  simpa [smallTarget,e,e'] using attain_blackburn q hq

theorem five_partition_maximum {q : ℕ} (hq : 2 ≤ q) :
    Attain q (smallTarget q) ∧ ∀ m, Attain q m → m ≤ smallTarget q :=
  ⟨attain_exact q hq,fun _ => upper⟩

theorem exceptional_alphabets {q : ℕ} (hq : 2 ≤ q) :
    blackburn q < smallTarget q ↔ q=2 ∨ q=3 := by
  by_cases e : q=2
  · subst q; decide
  by_cases e' : q=3
  · subst q; decide
  simp [smallTarget,e,e']

#print axioms five_partition_maximum
#print axioms exceptional_alphabets
end NonoverlapFive
