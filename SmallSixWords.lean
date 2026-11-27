import ExactFiveWords

open NonoverlapThreshold NonoverlapThreshold.WordLower

namespace NonoverlapSix

/-- A three-word binary witness at block length six. -/
theorem binary_word_witness : ∃ C : Finset (List (Fin 2)), IsCode 6 C ∧ C.card=3 := by
  let C : Finset (List (Fin 2)) := {[0,0,1,0,1,1], [0,0,1,1,0,1], [0,0,1,1,1,1]}
  exact ⟨C, NonoverlapFive.code_of_checks _ (by decide +kernel) (by decide +kernel),
    by decide +kernel⟩

private theorem single_mark (a : ℕ) (ha : 0<a) :
    ∃ C : Finset (List (Fin (a+1))), IsCode 6 C ∧ C.card=Lower.rightCount a 1 4 := by
  let x : Fin a := ⟨0,ha⟩
  let y : Fin 1 := 0
  let D := words x y 5
  have hD : IsCode 6 D := ⟨fun w h => (words_length_good x y 5 w h).1,
    words_nonoverlapping x y 5⟩
  obtain ⟨c,h⟩ := move_alphabet finSumFinEquiv D hD
  refine ⟨_,h,c.trans ?_⟩
  simpa [D] using words_card x y 4

/-- A single marked pair gives 41 actual ternary words of length six. -/
theorem ternary_word_witness : ∃ C : Finset (List (Fin 3)), IsCode 6 C ∧ C.card=41 :=
  single_mark 2 (by decide)

/-- A single marked pair gives 251 actual quaternary words of length six. -/
theorem quaternary_word_witness : ∃ C : Finset (List (Fin 4)), IsCode 6 C ∧ C.card=251 :=
  single_mark 3 (by decide)

end NonoverlapSix
