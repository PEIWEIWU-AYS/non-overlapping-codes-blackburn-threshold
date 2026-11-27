import Representation

open NonoverlapThreshold.WordLower Nonoverlap.Representation
namespace Nonoverlap.Six

/-- Upper envelope after optimizing the two final splits at a fixed choice
of the first three levels. -/
private def envelope (a b x y u v : ℕ) : ℕ :=
  let d := max a b
  max (d*a+x) (d*b+y) * (a*v+x*y+b*u) + d*(x*v+u*y)+u*v

private def row (a : ℕ) : Bool :=
  let b := 9-a
  (List.range (a*b+1)).all fun x =>
    let y := a*b-x
    let T := a*y+b*x
    (List.range (T+1)).all fun u => decide (envelope a b x y u (T-u) ≤ 33872)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private lemma table : (List.range 10).all row = true := by decide +kernel

private lemma finite_envelope {a b x y u v : ℕ} (h1 : a+b=9)
    (h2 : x+y=a*b) (h3 : u+v=a*y+b*x) : envelope a b x y u v ≤ 33872 := by
  have hrow := List.all_eq_true.mp table a (List.mem_range.mpr (by omega))
  unfold row at hrow
  have hb : 9-a=b := by omega
  simp only [hb] at hrow
  have col := List.all_eq_true.mp hrow x (List.mem_range.mpr (by omega))
  have hy : a*b-x=y := by omega
  simp only [hy] at col
  have ent := List.all_eq_true.mp col u (List.mem_range.mpr (by omega))
  have hv : a*y+b*x-u=v := by omega
  simpa only [hv,decide_eq_true_eq] using ent

private lemma eliminate_last {a b x y u v k z p s : ℕ}
    (h4 : k+z=a*v+x*y+b*u) (h5 : p+s=a*z+x*v+u*y+b*k) :
    a*s+x*z+u*v+k*y+p*b ≤ envelope a b x y u v := by
  let d := max a b
  let D := max (d*a+x) (d*b+y)
  have ha : a ≤ d := le_max_left _ _
  have hb : b ≤ d := le_max_right _ _
  have hDa : d*a+x ≤ D := le_max_left _ _
  have hDb : d*b+y ≤ D := le_max_right _ _
  have hend : a*s+p*b ≤ d*(p+s) := by
    nlinarith only [Nat.mul_le_mul_right s ha,Nat.mul_le_mul_left p hb]
  have hmid : (d*a+x)*z+(d*b+y)*k ≤ D*(k+z) := by
    nlinarith only [Nat.mul_le_mul_right z hDa,Nat.mul_le_mul_right k hDb]
  rw [h5] at hend
  rw [h4] at hmid
  change _ ≤ D*(a*v+x*y+b*u)+d*(x*v+u*y)+u*v
  nlinarith only [hend,hmid]

/-- Every six-letter non-overlapping code over nine symbols has at most
33,872 codewords. -/
theorem nine_letter_upper (C : Finset (List (Fin 9))) (hc : IsCode 6 C) : C.card ≤ 33872 := by
  obtain ⟨l,r,h1,law,cap⟩ := word_code_profile 6 (by decide) C hc
  have h2 := law 2 (by decide)
  have h3 := law 3 (by decide)
  have h4 := law 4 (by decide)
  have h5 := law 5 (by decide)
  norm_num [convolution,Finset.sum_range_succ] at h2 h3 h4 h5 cap
  apply cap.trans
  have env := finite_envelope h1 h2 (show l 3+r 3=l 1*r 2 + r 1*l 2 by rw [h3]; ring)
  apply le_trans _ env
  have bound := eliminate_last (k:=l 4) (z:=r 4) (p:=l 5) (s:=r 5)
    (show l 4+r 4=l 1*r 3+l 2*r 2+r 1*l 3 by rw [h4]; ring)
    (show l 5+r 5=l 1*r 4+l 2*r 3+l 3*r 2+r 1*l 4 by rw [h5]; ring)
  simpa only [Nat.add_assoc] using bound

#print axioms nine_letter_upper
end Nonoverlap.Six
