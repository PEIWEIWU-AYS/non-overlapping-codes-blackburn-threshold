import Representation
import AlphabetThreshold
import LengthFive

open NonoverlapThreshold NonoverlapThreshold.WordLower
open Nonoverlap.Representation
open scoped BigOperators
namespace NonoverlapFive

theorem code_of_checks {q n : ℕ} (C : Finset (List (Fin q)))
    (len : ∀ w ∈ C, w.length=n)
    (verify : ∀ w ∈ C, ∀ z ∈ C, ∀ k ∈ Finset.range (n-1),
      w.take (k+1) ≠ z.drop (n-(k+1))) : IsCode n C := by
  refine ⟨len,?_⟩
  intro u pre post hne hu hp hs
  have hpos := List.length_pos_iff.mpr hne
  have hlen := len _ hs
  simp only [List.length_append] at hlen
  have check := verify _ hp _ hs (u.length-1) (Finset.mem_range.mpr (by omega))
  rw [show u.length-1+1=u.length by omega,show n-u.length=pre.length by omega,
    List.take_left,List.drop_left] at check
  exact check rfl

private def binaryWitness : Finset (List (Fin 2)) :=
  {[0,0,1,0,1], [0,0,1,1,1]}

private def ternaryWitness : Finset (List (Fin 3)) :=
  {[0,0,0,1,2],
   [0,0,1,1,2],
   [0,0,0,2,2],
   [0,1,0,1,2],
   [0,1,1,1,2],
   [0,1,0,2,2],
   [0,0,2,1,2],
   [1,0,0,1,2],
   [1,0,1,1,2],
   [1,0,0,2,2],
   [1,1,0,1,2],
   [1,1,1,1,2],
   [1,1,0,2,2],
   [1,0,2,1,2],
   [0,2,0,1,2],
   [0,2,1,1,2],
   [0,2,0,2,2]}

private theorem binary_word_witness : IsCode 5 binaryWitness ∧ binaryWitness.card=2 := by
  exact ⟨code_of_checks _ (by decide +kernel) (by decide +kernel),by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem ternary_word_witness : IsCode 5 ternaryWitness ∧ ternaryWitness.card=17 := by
  exact ⟨code_of_checks _ (by decide +kernel) (by decide +kernel),by decide +kernel⟩

private theorem finite_word_upper {q : ℕ} (C : Finset (List (Fin q))) (hc : IsCode 5 C) :
    C.card ≤ smallTarget q := by
  obtain ⟨l,r,first,law,cap⟩ := word_code_profile 5 (by decide) C hc
  have h2 := law 2 (by decide)
  have h3 := law 3 (by decide)
  have h4 := law 4 (by decide)
  norm_num [convolution,Finset.sum_range_succ] at h2 h3 h4 cap
  by_cases h0 : l 1=0 ∨ r 1=0
  · rcases h0 with h|h <;> simp [h] at h2 <;> obtain ⟨hl,hr⟩ := h2 <;>
      simp [h,hl,hr] at h3 <;> obtain ⟨hl',hr'⟩ := h3 <;> simp [h,hl,hr,hl',hr'] at h4 <;>
      obtain ⟨hl'',hr''⟩ := h4 <;> simp [h,hl,hr,hl',hr',hl'',hr''] at cap <;> simp [cap]
  · apply cap.trans
    apply upper
    refine ⟨l 1,r 1,l 2,r 2,l 3,r 3,l 4,r 4,by omega,by omega,first,h2,?_,?_,?_⟩
    · rw [h3]; ring
    · rw [h4]; ring
    · ring

/-- The largest size of an actual five-letter non-overlapping code over
    an alphabet of size q is 2 at q=2, 17 at q=3, and Blackburn's split
    optimum for every q at least four. -/
theorem five_word_maximum {q : ℕ} (hq : 2≤q) :
    (∃ B : Finset (List (Fin q)), IsCode 5 B ∧ B.card=smallTarget q) ∧
      ∀ C : Finset (List (Fin q)), IsCode 5 C → C.card ≤ smallTarget q := by
  refine ⟨?_,fun C hc => finite_word_upper C hc⟩
  by_cases eq2 : q=2
  · subst q; exact ⟨_,binary_word_witness⟩
  by_cases eq3 : q=3
  · subst q; exact ⟨_,ternary_word_witness⟩
  obtain ⟨s,hs,hS⟩ := Finset.exists_mem_eq_sup _ (Finset.nonempty_range_succ (n:=q))
    (fun s => s^4*(q-s))
  obtain ⟨B,hB,hcard⟩ := blackburn_words 4 q s (by have := Finset.mem_range.mp hs; omega)
  exact ⟨B,hB,by simpa [smallTarget,eq2,eq3,blackburn] using hcard.trans hS.symm⟩

/-- Four is the least threshold for length five over actual finite alphabets. -/
theorem threshold_five : q₀ 5 = 4 := by
  have opt : AlwaysOptimal 5 4 := by
    apply optimal_of_word_bound 5 4 (by decide) (by decide)
    intro q hq C hc
    obtain ⟨s,hs,hS⟩ := Finset.exists_mem_eq_sup _ (Finset.nonempty_range_succ (n:=q))
      (fun s => s^4*(q-s))
    refine ⟨s,by have := Finset.mem_range.mp hs; omega,?_⟩
    have bound := (five_word_maximum (q:=q) (by omega)).2 C hc
    have he : smallTarget q = s^4*(q-s) := by
      simpa [smallTarget,show q≠2 by omega,show q≠3 by omega,blackburn] using hS
    exact bound.trans_eq he
  apply le_antisymm (q₀_le 5 4 opt)
  by_contra! bad
  obtain ⟨s,hs,B,_,size,dominates⟩ := (q₀_spec 5 4 opt).2 3 (by omega)
  have upperB := blackburn_candidate (q:=3) hs
  have exceeds := dominates ternaryWitness ternary_word_witness.1
  rw [ternary_word_witness.2,size] at exceeds
  have b3 : blackburn 3=16 := by decide +kernel
  rw [b3] at upperB
  exact (by omega : ¬ 17≤16) (exceeds.trans upperB)

end NonoverlapFive
