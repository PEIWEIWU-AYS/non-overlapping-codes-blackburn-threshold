import WordLower
import Mathlib.Data.List.OfFn

open NonoverlapThreshold.WordLower
namespace NonoverlapThreshold

private def blk {k s b : ℕ} (p : (Fin k → Fin s) × Fin b) : List (Fin s ⊕ Fin b) :=
  (List.ofFn (fun i => Sum.inl (p.1 i))) ++ [Sum.inr p.2]

private theorem blk_inj (k s b : ℕ) : Function.Injective (@blk k s b) := by
  rintro ⟨f,x⟩ ⟨g,y⟩ eq
  have last := congrArg List.getLast? eq
  have hxy : x=y := by simpa [blk] using last
  subst y
  have hp : (List.ofFn fun i => (Sum.inl (f i) : Fin s ⊕ Fin b)) =
      List.ofFn fun i => Sum.inl (g i) := List.append_cancel_right eq
  have := List.ofFn_injective hp
  have fg : f=g := by funext i; exact Sum.inl.inj (congrFun this i)
  rw [fg]

/-- Blackburn's split is realized as a finite set of words over the specified alphabet. -/
theorem blackburn_words (k q s : ℕ) (hs : s ≤ q) :
    ∃ C : Finset (List (Fin q)), IsCode (k+1) C ∧ C.card=s^k*(q-s) := by
  let b := q-s
  let C := (Finset.univ : Finset ((Fin k → Fin s) × Fin b)).image blk
  have card : C.card = s^k*b := by
    rw [Finset.card_image_of_injective _ (blk_inj k s b)]
    simp
  have valid : IsCode (k+1) C := by
    constructor
    · intro w hw
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hw
      simp [blk]
    · intro u pre post hu hlen hleft hright
      obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hleft
      obtain ⟨d,_,hd⟩ := Finset.mem_image.mp hright
      have last := congrArg List.getLast? hd
      rw [List.getLast?_append_of_ne_nil _ hu] at last
      have last_u : u.getLast? = some (Sum.inr d.2) := by simpa [blk] using last.symm
      have mem_u : Sum.inr d.2 ∈ u := List.mem_of_getLast? last_u
      have first := congrArg (List.take u.length) hp
      have hk : u.length ≤ (List.ofFn (fun i => (Sum.inl (p.1 i) : Fin s ⊕ Fin b))).length := by simp; omega
      unfold blk at first
      rw [List.take_append_of_le_length hk] at first
      simp only [List.take_left] at first
      rw [← first] at mem_u
      have in_pre := List.mem_of_mem_take mem_u
      simp at in_pre
  have eq : s+b=q := by dsimp [b]; omega
  let e : (Fin s ⊕ Fin b) ≃ Fin q := finSumFinEquiv.trans (finCongr eq)
  obtain ⟨hc,hcode⟩ := move_alphabet e C valid
  exact ⟨_,hcode,hc.trans card⟩

/-- A threshold means an actual Blackburn code attains the maximum at every larger alphabet. -/
def AlwaysOptimal (n Q : ℕ) : Prop :=
  2 ≤ Q ∧ ∀ q ≥ Q, ∃ s ≤ q, ∃ B : Finset (List (Fin q)),
    IsCode n B ∧ B.card=s^(n-1)*(q-s) ∧
    ∀ C : Finset (List (Fin q)), IsCode n C → C.card ≤ B.card

end NonoverlapThreshold
