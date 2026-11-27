import ThresholdSix
import SmallSixWords
import TwoMark

open NonoverlapThreshold NonoverlapThreshold.WordLower
namespace Nonoverlap.Six

def splitMaximum (q : ℕ) :=
  (Finset.range (q+1)).sup (fun s => s^5*(q-s))

def sixMaximum (q : ℕ) :=
  if q=2 then 3 else if q=3 then 41 else if q=4 then 251 else if q=9 then 33872 else splitMaximum q

private theorem split_le (q s : ℕ) (h : s ≤ q) : s^5*(q-s) ≤ splitMaximum q :=
  Finset.le_sup (f := fun s : ℕ => s^5*(q-s)) (Finset.mem_range.mpr (by omega : s < q+1))

private theorem cap_le {q : ℕ} (hq : 2 ≤ q) : smallUpperTarget q ≤ sixMaximum q := by
  by_cases e2 : q=2
  · simp [e2,smallUpperTarget,sixMaximum]
  by_cases e3 : q=3
  · simp [e3,smallUpperTarget,sixMaximum]
  by_cases e4 : q=4
  · simp [e4,smallUpperTarget,sixMaximum]
  by_cases e9 : q=9
  · simp [e9,smallUpperTarget,sixMaximum]
  simp only [smallUpperTarget,sixMaximum,e2,e3,e4,e9,if_false]
  apply max_le
  · apply split_le; omega
  · apply split_le; omega

private theorem have_split (q : ℕ) :
    ∃ s ≤ q, s^5*(q-s)=splitMaximum q := by
  obtain ⟨s,hs,hmax⟩ := Finset.exists_mem_eq_sup _ (Finset.nonempty_range_succ (n:=q))
    (fun a => a^5*(q-a))
  exact ⟨s,by have := Finset.mem_range.mp hs; omega,hmax.symm⟩

/-- The complete length-six extremal function, including attainment on each alphabet. -/
theorem six_word_maximum
    {q : ℕ} (hq : 2 ≤ q) :
    (∃ C : Finset (List (Fin q)), IsCode 6 C ∧ C.card=sixMaximum q) ∧
    ∀ C : Finset (List (Fin q)), IsCode 6 C → C.card ≤ sixMaximum q := by
  constructor
  · by_cases e2 : q=2
    · subst q; exact NonoverlapSix.binary_word_witness
    by_cases e3 : q=3
    · subst q; exact NonoverlapSix.ternary_word_witness
    by_cases e4 : q=4
    · subst q; exact NonoverlapSix.quaternary_word_witness
    by_cases e9 : q=9
    · subst q; exact ⟨TwoMark.witness,TwoMark.witness_isCode,TwoMark.witness_card⟩
    obtain ⟨s,hs,hmax⟩ := have_split q
    obtain ⟨C,hC,hsize⟩ := blackburn_words 5 q s hs
    exact ⟨C,hC,by simpa [sixMaximum,e2,e3,e4,e9] using hsize.trans hmax⟩
  · intro C hC
    by_cases h : q < 120
    · exact (small_six_upper h C hC).trans (cap_le hq)
    obtain ⟨s,hs,B,_,size,win⟩ := (finite_upper 6 (by decide)).2 q (by omega)
    have upper := win C hC
    rw [size] at upper
    have exactTarget : sixMaximum q=splitMaximum q := by
      simp [sixMaximum,show q ≠ 2 by omega,show q ≠ 3 by omega,show q ≠ 4 by omega,show q ≠ 9 by omega]
    rw [exactTarget]
    exact upper.trans (split_le q s hs)

/-- Exactly four alphabet sizes at length six admit codes larger than every Blackburn split. -/
theorem six_exceptional_alphabets
    {q : ℕ} (hq : 2 ≤ q) :
    (∃ C : Finset (List (Fin q)), IsCode 6 C ∧ splitMaximum q < C.card) ↔
    q=2 ∨ q=3 ∨ q=4 ∨ q=9 := by
  obtain ⟨⟨C,hC,size⟩,ub⟩ := six_word_maximum hq
  constructor
  · rintro ⟨D,hD,hwin⟩
    by_contra! h
    obtain ⟨e2,e3,e4,e9⟩ := h
    have bound := ub D hD
    simp [sixMaximum,e2,e3,e4,e9] at bound
    omega
  · intro h
    refine ⟨C,hC,?_⟩
    rw [size]
    rcases h with e|e|e|e <;> subst q <;> decide +kernel

/-- Ten is the least eventual optimality threshold at block length six. -/
theorem threshold_six :
    q₀ 6 = 10 := by
  have opt : AlwaysOptimal 6 10 := by
    apply optimal_of_word_bound 6 10 (by decide) (by decide)
    intro q hq C hc
    obtain ⟨s,hs,hmax⟩ := have_split q
    refine ⟨s,hs,?_⟩
    have h := (six_word_maximum (by omega : 2 ≤ q)).2 C hc
    simp only [sixMaximum,show q ≠ 2 by omega,show q ≠ 3 by omega,show q ≠ 4 by omega,
      show q ≠ 9 by omega,if_false] at h
    exact h.trans_eq hmax.symm
  apply le_antisymm (q₀_le 6 10 opt)
  by_contra! bad
  obtain ⟨s,hs,B,_,size,dominates⟩ := (q₀_spec 6 10 opt).2 9 (by omega)
  have c := dominates TwoMark.witness TwoMark.witness_isCode
  rw [TwoMark.witness_card,size] at c
  have g : splitMaximum 9=33614 := by decide +kernel
  have endBound := split_le 9 s hs
  rw [g] at endBound
  exact (by decide : ¬ 33872≤33614) (c.trans endBound)
#print axioms six_word_maximum
#print axioms threshold_six
end Nonoverlap.Six
