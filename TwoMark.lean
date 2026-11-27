import SixCount
import WordLower
import ExactSix

open SixPattern (SixLetters letters valid no_pattern_overlap letters_injective)
namespace Nonoverlap.TwoMark
/-- The two marked bigrams are 07 and 17. They share the left symbol class. -/
def category (i : Fin 9) : Fin 4 :=
  if i.val ≤ 1 then 0 else if i.val ≤ 6 then 1 else if i.val = 7 then 2 else 3

def accepted (p : SixLetters) : Bool := valid ((letters p).map category)

private def digitSum (f : Fin 4 → ℕ) := 2*f 0 + 5*f 1 + f 2 + f 3

private theorem regroup (f : Fin 4 → ℕ) : (∑ i : Fin 9, f (category i)) = digitSum f := by
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change f 0 + (f 0 + (f 1 + (f 1 + (f 1 + (f 1 + (f 1 + (f 2 + f 3))))))) = _
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

def witness : Finset (List (Fin 9)) :=
  (Finset.univ.filter (fun p : SixLetters => accepted p = true)).map
    ⟨letters, letters_injective⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_card : witness.card = 33872 := by
  change (Finset.map _ _).card = _
  rw [Finset.card_map]
  rw [← Fintype.card_subtype, card_eq_count, weighted]
  decide

private lemma mem_spec {w : List (Fin 9)} (hw : w ∈ witness) :
    w.length = 6 ∧ valid (w.map category) = true := by
  obtain ⟨p,hp,he⟩ := Finset.mem_map.mp hw
  change letters p = w at he
  subst w
  exact ⟨rfl,(Finset.mem_filter.mp hp).2⟩

theorem witness_isCode : NonoverlapThreshold.WordLower.IsCode 6 witness := by
  refine ⟨fun _ hw => (mem_spec hw).1,?_⟩
  intro u pre post hu hlen hp hs
  exact no_pattern_overlap (u.map category) (pre.map category) (post.map category)
    (by simpa using hu) (by simpa using hlen)
    (by simpa only [List.map_append] using (mem_spec hp).2)
    (by simpa only [List.map_append] using (mem_spec hs).2)

/-- Exact maximum for length six on nine letters, including attainment. -/
theorem exact_maximum : ∃ C : Finset (List (Fin 9)),
    NonoverlapThreshold.WordLower.IsCode 6 C ∧ C.card = 33872 ∧
    ∀ D : Finset (List (Fin 9)), NonoverlapThreshold.WordLower.IsCode 6 D → D.card ≤ C.card := by
  refine ⟨witness,witness_isCode,witness_card,?_⟩
  intro D hd
  rw [witness_card]
  exact Nonoverlap.Six.nine_letter_upper D hd

end Nonoverlap.TwoMark
