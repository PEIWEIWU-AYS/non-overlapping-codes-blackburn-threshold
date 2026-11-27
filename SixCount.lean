import ExplicitSix
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace SixPattern

abbrev SixLetters := Fin 9 × Fin 9 × Fin 9 × Fin 9 × Fin 9 × Fin 9

def letters (p : SixLetters) : List (Fin 9) :=
  [p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2]

def accepted (p : SixLetters) : Bool := code (letters p)

private def digitSum (f : Fin 4 → ℕ) := f 0 + 6*f 1 + f 2 + f 3

private theorem regroup (f : Fin 4 → ℕ) : (∑ i : Fin 9, f (category i)) = digitSum f := by
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change f 0 + (f 1 + (f 1 + (f 1 + (f 1 + (f 1 + (f 1 + (f 2 + f 3))))))) = _
  unfold digitSum
  ring

private def countByLetters : ℕ → List (Fin 4) → ℕ
  | 0, w => if valid w then 1 else 0
  | n+1, w => ∑ a : Fin 9, countByLetters n (w ++ [category a])

private def countByClass : ℕ → List (Fin 4) → ℕ
  | 0, w => if valid w then 1 else 0
  | n+1, w => digitSum (fun a => countByClass n (w ++ [a]))

private theorem weighted (n : ℕ) (w : List (Fin 4)) :
    countByLetters n w = countByClass n w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    simp only [countByLetters,countByClass,ih]
    exact regroup (fun a => countByClass n (w++[a]))

private theorem card_eq_count : Fintype.card {p : SixLetters // accepted p = true} =
    countByLetters 6 [] := by
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  rfl

/-- Different length-six tuples give different words. -/
theorem letters_injective : Function.Injective letters := by
  rintro ⟨a,b,c,d,e,f⟩ ⟨u,v,w,x,y,z⟩ h
  simpa [letters] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem six_card : Fintype.card {p : SixLetters // accepted p = true} = 33851 := by
  rw [card_eq_count, weighted]
  decide

theorem blackburn_nine : (∀ s : Fin 10, (s:ℕ)^5*(9-s) ≤ 33614) ∧ (7:ℕ)^5*2 = 33614 := by
  decide

theorem strict_counterexample :
    (∀ s : Fin 10, (s:ℕ)^5*(9-s) < Fintype.card {p : SixLetters // accepted p = true}) ∧
    (∀ (u pre post : List (Fin 9)), u ≠ [] → u.length < 6 →
      code (u++post) = true → code (pre++u) = true → False) := by
  constructor
  · intro s
    rw [six_card]
    exact (blackburn_nine.1 s).trans_lt (by decide)
  · exact no_overlap

/-- The counterexample as a finite set of words on the actual nine letters. -/
def nineCode : Finset (List (Fin 9)) :=
  (Finset.univ.filter (fun p : SixLetters => accepted p = true)).map
    ⟨letters, letters_injective⟩

theorem nineCode_card : nineCode.card = 33851 := by
  simpa only [nineCode, Finset.card_map, Fintype.card_subtype] using six_card

private lemma word_spec {w : List (Fin 9)} (h : w ∈ nineCode) :
    w.length = 6 ∧ code w = true := by
  obtain ⟨p,hp,he⟩ := Finset.mem_map.mp h
  change letters p = w at he
  subst w
  exact ⟨rfl,(Finset.mem_filter.mp hp).2⟩

theorem finite_counterexample :
    ∃ C : Finset (List (Fin 9)), C.card = 33851 ∧
      (∀ w ∈ C, w.length = 6) ∧
      (∀ u pre post, u ≠ [] → u.length < 6 → u++post ∈ C → pre++u ∈ C → False) ∧
      (∀ s : Fin 10, (s:ℕ)^5*(9-s) < C.card) := by
  refine ⟨nineCode, nineCode_card, fun _ hw => (word_spec hw).1, ?_, ?_⟩
  · intro u pre post hu hlen hp hs
    exact no_overlap u pre post hu hlen (word_spec hp).2 (word_spec hs).2
  · intro s
    rw [nineCode_card]
    exact (blackburn_nine.1 s).trans_lt (by decide)

#print axioms finite_counterexample
#print axioms strict_counterexample
#print axioms letters_injective
end SixPattern
