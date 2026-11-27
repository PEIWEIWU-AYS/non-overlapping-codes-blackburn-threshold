import WordLower

open scoped BigOperators
open NonoverlapThreshold.WordLower (IsCode)

namespace Nonoverlap.Representation

variable {q : ℕ}
private abbrev Word (q : ℕ) := List (Fin q)

private def Left (C : Finset (Word q)) (u : Word q) : Prop :=
  ∃ v, u ++ v ∈ C

private inductive Parsed (C : Finset (Word q)) : Word q → Prop
  | atom (x : Fin q) : Parsed C [x]
  | node {u v} : Parsed C u → Parsed C v → Left C u → ¬ Left C v → Parsed C (u++v)

private lemma Parsed.nonempty {C : Finset (Word q)} {u : Word q} (h : Parsed C u) : u ≠ [] := by
  induction h with
  | atom => simp
  | node _ _ _ _ hu _ => intro h; exact hu (List.append_eq_nil_iff.mp h).1

private lemma find_transition {α : Type} (P : α → Prop) (b : α) (hb : ¬P b)
    (middle : List α) (a : α) (ha : P a) :
    ∃ pre u v post, a :: (middle ++ [b]) = pre ++ u :: v :: post ∧ P u ∧ ¬P v := by
  induction middle generalizing a with
  | nil => exact ⟨[], a, b, [], rfl, ha, hb⟩
  | cons c cs ih =>
    by_cases hc : P c
    · obtain ⟨pre,u,v,post,he,hu,hv⟩ := ih c hc
      exact ⟨a::pre,u,v,post,congrArg (a :: ·) he,hu,hv⟩
    · exact ⟨[],a,c,cs++[b],rfl,ha,hc⟩

private theorem parse_chunks {n : ℕ} (hn : 2 ≤ n) {C : Finset (Word q)}
    (hc : IsCode n C) (s : List (Word q)) (hw : s.flatten ∈ C)
    (good : ∀ u ∈ s, Parsed C u) : Parsed C s.flatten := by
  classical
  have hlen := hc.1 _ hw
  cases s with
  | nil => simp at hlen; omega
  | cons a t =>
    cases ht : t with
    | nil => simpa [ht] using good a (by simp)
    | cons z zs =>
      have htn : t ≠ [] := by simp [ht]
      let b := t.getLast htn
      have hs : t = t.dropLast ++ [b] := (List.dropLast_append_getLast htn).symm
      have ha : Parsed C a := good a (by simp)
      have hb : Parsed C b := good b (by rw [hs]; simp)
      have first : Left C a := ⟨t.flatten,hw⟩
      have hflat : (a::t).flatten = (a++t.dropLast.flatten)++b := by
        rw [List.flatten_cons,hs]
        simp
      have hbLen : b.length < n := by
        rw [hflat] at hlen
        simp only [List.length_append] at hlen
        have : 0 < a.length := List.length_pos_iff.mpr ha.nonempty
        omega
      have last : ¬ Left C b := by
        rintro ⟨post,hp⟩
        rw [hflat] at hw
        exact hc.2 b _ post hb.nonempty hbLen hp hw
      obtain ⟨pre,u,v,post,he,fl,fr⟩ := find_transition (Left C) b last t.dropLast a first
      have he' : a::t = pre ++ u::v::post := by simpa only [←hs] using he
      have gm : ∀ z ∈ pre++u::v::post, Parsed C z := he' ▸ good
      let s' := pre ++ (u++v) :: post
      have heflat : s'.flatten = (a::t).flatten := by rw [he']; simp [s', List.append_assoc]
      have g' : ∀ z ∈ s', Parsed C z := by
        intro z hz
        simp only [s',List.mem_append,List.mem_cons] at hz
        rcases hz with hz | rfl | hz
        · exact gm z (by simp [hz])
        · exact .node (gm u (by simp)) (gm v (by simp)) fl fr
        · exact gm z (by simp [hz])
      have dec : s'.length < (a::t).length := by rw [he']; simp [s']
      rw [←ht, ←heflat]
      exact parse_chunks hn hc s' (heflat ▸ hw) g'
termination_by s.length
decreasing_by
  subst_vars
  simpa [s'] using dec

private lemma parse_codeword {n : ℕ} (hn : 2 ≤ n) {C : Finset (Word q)}
    (hc : IsCode n C) {w : Word q} (hw : w ∈ C) : Parsed C w := by
  let pieces := w.map (fun x => [x])
  have he : pieces.flatten=w := by
    change (w.map (fun x => [x])).flatten=w
    clear hw
    induction w with
    | nil => rfl
    | cons a w ih => simp [ih]
  rw [←he]
  apply parse_chunks hn hc pieces (he ▸ hw)
  intro u hu
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hu
  exact .atom x

noncomputable section

private def allWords (q d : ℕ) : Finset (Word q) :=
  Finset.univ.image (List.ofFn : (Fin d → Fin q) → Word q)

private theorem mem_allWords {d : ℕ} {w : Word q} :
    w ∈ allWords q d ↔ w.length=d := by
  constructor
  · intro hw
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hw
    exact List.length_ofFn
  · rintro rfl
    exact Finset.mem_image.mpr ⟨w.get,Finset.mem_univ _,List.ofFn_get _⟩

private def parsedWords (C : Finset (Word q)) (d : ℕ) : Finset (Word q) := by
  classical exact (allWords q d).filter (Parsed C)

private def leftWords (C : Finset (Word q)) (d : ℕ) : Finset (Word q) := by
  classical exact (parsedWords C d).filter (Left C)

private def rightWords (C : Finset (Word q)) (d : ℕ) : Finset (Word q) := by
  classical exact (parsedWords C d).filter (fun x => ¬ Left C x)

private theorem split_card (C : Finset (Word q)) (d : ℕ) :
    (leftWords C d).card + (rightWords C d).card = (parsedWords C d).card := by
  classical exact Finset.filter_card_add_filter_neg_card_eq_card _

private theorem parsed_one (C : Finset (Word q)) : (parsedWords C 1).card=q := by
  have he : parsedWords C 1=allWords q 1 := by
    classical
    apply Finset.filter_eq_self.mpr
    intro w hw
    have h := mem_allWords.mp hw
    obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp h
    exact .atom x
  rw [he,allWords, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

private def appWords (s t : Finset (Word q)) : Finset (Word q) :=
  (s ×ˢ t).image (fun p => p.1++p.2)

private lemma parsed_card_bound (C : Finset (Word q)) (d : ℕ) :
    (parsedWords C (d+2)).card ≤ ∑ i ∈ Finset.range (d+1),
      (leftWords C (i+1)).card * (rightWords C (d+1-i)).card := by
  classical
  let A := fun i => appWords (leftWords C (i+1)) (rightWords C (d+1-i))
  have sub : parsedWords C (d+2) ⊆ (Finset.range (d+1)).biUnion A := by
    intro w hw
    obtain ⟨hw,hp⟩ := Finset.mem_filter.mp hw
    have hlen := mem_allWords.mp hw
    cases hp with
    | atom x => simp at hlen
    | @node u v pu pv hu hv =>
      have uu := List.length_pos_iff.mpr pu.nonempty
      have vv := List.length_pos_iff.mpr pv.nonempty
      simp only [List.length_append] at hlen
      let i := u.length-1
      have hi : i∈Finset.range (d+1) := Finset.mem_range.mpr (by dsimp [i]; omega)
      have h1 : u.length=i+1 := by dsimp [i]; omega
      have h2 : v.length=d+1-i := by dsimp [i]; omega
      apply Finset.mem_biUnion.mpr
      refine ⟨i,hi,Finset.mem_image.mpr ⟨(u,v),Finset.mem_product.mpr ⟨?_,?_⟩,rfl⟩⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_allWords.mpr h1,pu⟩,hu⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_allWords.mpr h2,pv⟩,hv⟩
  refine (Finset.card_le_card sub).trans (Finset.card_biUnion_le.trans ?_)
  apply Finset.sum_le_sum
  intro i _
  exact Finset.card_image_le.trans_eq (Finset.card_product ..)

/-- Natural coefficients of an upper-bounding layer profile. -/
def convolution (d : ℕ) (l r : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d-1), l (i+1)*r (d-1-i)

private def rightCount (C : Finset (Word q)) : ℕ → ℕ
  | 0 => 0
  | 1 => (rightWords C 1).card
  | d+2 => (∑ i ∈ Finset.range (d+1), (leftWords C (i+1)).card * rightCount C (d+1-i)) -
      (leftWords C (d+2)).card
termination_by k => k
decreasing_by omega

private theorem right_dominates (C : Finset (Word q)) (d : ℕ) (hd : 1≤d) :
    (rightWords C d).card ≤ rightCount C d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    obtain _ | _ | k := d
    · omega
    · rw [rightCount]
    · have below := (split_card C (k+2)).le.trans (parsed_card_bound C k)
      have up : (∑ i ∈ Finset.range (k+1), (leftWords C (i+1)).card *
          (rightWords C (k+1-i)).card) ≤
          ∑ i ∈ Finset.range (k+1), (leftWords C (i+1)).card * rightCount C (k+1-i) := by
        refine Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (ih _ (by omega) ?_)
        have := Finset.mem_range.mp hi
        omega
      have := below.trans up
      change (rightWords C (k+2)).card ≤ rightCount C (k+2)
      rw [rightCount]
      omega

/-- Every actual fixed-length non-overlapping code is dominated by an integer
    layer profile. The proof merges adjacent parsed blocks from left and right
    prefix classes. Multiple parses of the same word only increase the bound. -/
theorem word_code_profile (n : ℕ) (hn : 2≤n) (C : Finset (List (Fin q))) (hc : IsCode n C) :
    ∃ l r : ℕ → ℕ, l 1+r 1=q ∧
      (∀ i, 2 ≤ i → l i+r i=convolution i l r) ∧ C.card ≤ convolution n l r := by
  classical
  let l := fun i => (leftWords C i).card
  let r := rightCount C
  have hlaw (k : ℕ) : l (k+2)+r (k+2)=convolution (k+2) l r := by
    have below := (split_card C (k+2)).le.trans (parsed_card_bound C k)
    have up : (∑ i ∈ Finset.range (k+1), (leftWords C (i+1)).card *
        (rightWords C (k+1-i)).card) ≤ convolution (k+2) l r := by
      apply Finset.sum_le_sum
      intro i hi
      have := Finset.mem_range.mp hi
      exact Nat.mul_le_mul_left _ (right_dominates C _ (by omega))
    have ha := below.trans up
    change l (k+2) + rightCount C (k+2) = _
    rw [rightCount]
    change (leftWords C (k+2)).card + (convolution (k+2) l r - _) = _
    omega
  have start : l 1+r 1=q := by
    change _+rightCount C 1=q
    rw [rightCount]
    exact (split_card C 1).trans (parsed_one C)
  have law (i : ℕ) (hi : 2 ≤ i) : l i + r i = convolution i l r := by
    simpa only [Nat.sub_add_cancel hi] using hlaw (i-2)
  have hsub : C ⊆ parsedWords C n := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨mem_allWords.mpr (hc.1 _ hw),parse_codeword hn hc hw⟩
  have hn' : n-2+2=n := by omega
  refine ⟨l,r,start,law,?_⟩
  rw [←hn', ← hlaw, hn']
  have hr := right_dominates C n (by omega)
  exact (Finset.card_le_card hsub).trans ((split_card C n).ge.trans (Nat.add_le_add_left hr _))

end
end Nonoverlap.Representation
