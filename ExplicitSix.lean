import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic

namespace SixPattern

/-- The four symbol classes are the distinguished left letter, the other
left letters, the distinguished right letter, and the other right letter. -/
def category (i : Fin 9) : Fin 4 :=
  if i.val = 0 then 0 else if i.val ≤ 6 then 1 else if i.val = 7 then 2 else 3

def endsRight (w : List (Fin 4)) : Bool :=
  w.getLast? == some 2 || w.getLast? == some 3

def endsMarked (w : List (Fin 4)) : Bool :=
  [0,2].isSuffixOf w

/-- A proper prefix ending on the right must end in the distinguished pair;
the whole word ends on the right without the distinguished pair. -/
def valid (w : List (Fin 4)) : Bool :=
  w.length == 6 && endsRight w && !endsMarked w &&
    (List.range 6).all (fun i => !endsRight (w.take i) || endsMarked (w.take i))

def code (w : List (Fin 9)) : Bool := valid (w.map category)

/-- The same proper prefix/suffix may also be taken from a single codeword. -/
theorem no_pattern_overlap (u pre post : List (Fin 4))
    (hu : u ≠ []) (hlen : u.length < 6)
    (hp : valid (u++post) = true) (hs : valid (pre++u) = true) : False := by
  simp only [valid, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp hs
  have huEnd : endsRight u = true := by
    have he : u.getLast? ≠ none := by simpa using hu
    have hl : (pre++u).getLast? = u.getLast? := by
      rw [List.getLast?_append]
      cases h : u.getLast? with
      | none => exact (he h).elim
      | some z => rfl
    simpa only [endsRight,hl] using hs.1.1.2
  have ht := hp.2 u.length (List.mem_range.mpr hlen)
  have takeU : (u++post).take u.length = u := by
    rw [List.take_append_of_le_length le_rfl, List.take_length]
  rw [takeU,huEnd] at ht
  have hpair : [0,2] <:+ u := List.isSuffixOf_iff_suffix.mp (by simpa [endsMarked] using ht)
  have hfinal : [0,2] <:+ pre++u := hpair.trans (List.suffix_append pre u)
  have hmarked : endsMarked (pre++u) = true := List.isSuffixOf_iff_suffix.mpr hfinal
  exact Bool.noConfusion (hs.1.2.symm.trans hmarked)

/-- The four-class acceptance test pulls back to an actual non-overlapping
nine-letter code, including self-overlaps. -/
theorem no_overlap (u pre post : List (Fin 9))
    (hu : u ≠ []) (hlen : u.length < 6)
    (hp : code (u++post) = true) (hs : code (pre++u) = true) : False := by
  apply no_pattern_overlap (u.map category) (pre.map category) (post.map category)
  · simpa using hu
  · simpa using hlen
  · simpa only [code, List.map_append] using hp
  · simpa only [code, List.map_append] using hs

end SixPattern
