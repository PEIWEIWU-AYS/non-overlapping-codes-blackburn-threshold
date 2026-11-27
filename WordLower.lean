import Mathlib.Logic.Equiv.Fin.Basic
import Lower
import Analytic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.EquivFin

/-! The one-marked-pair construction on an actual alphabet, its non-overlap
property and the cardinality recurrence. -/
namespace NonoverlapThreshold.WordLower

variable {A B : Type}
abbrev Letter (A B : Type) := A ⊕ B

def marked (x : A) (y : B) : List (Letter A B) := [.inl x,.inr y]

private def EndsR (w : List (Letter A B)) : Prop := ∃ z : B, [.inr z] <:+ w

private def PrefixRule (x : A) (y : B) (w : List (Letter A B)) : Prop :=
  ∀ u v, v ≠ [] → u++v=w → EndsR u → marked x y <:+ u

private def Good (x : A) (y : B) (w : List (Letter A B)) : Prop :=
  EndsR w ∧ ¬ marked x y <:+ w ∧ PrefixRule x y w

private lemma prefix_rule_prepend {x : A} {y : B} {t w : List (Letter A B)}
    (ht : ∀ u, u <+: t → EndsR u → marked x y <:+ u)
    (hw : PrefixRule x y w) : PrefixRule x y (t++w) := by
  intro u v hv h uv
  have hp : u <+: t++w := ⟨v,h⟩
  by_cases hlen : u.length ≤ t.length
  · exact ht u (List.prefix_of_prefix_length_le hp (List.prefix_append t w) hlen) uv
  · obtain ⟨z,hz⟩ := List.prefix_of_prefix_length_le (List.prefix_append t w) hp (by omega)
    subst u
    have hzw : z++v=w := by simpa [List.append_assoc] using h
    obtain ⟨last,hl⟩ := uv
    have hzlen : 0<z.length := by simp only [List.length_append] at hlen; omega
    have he : [.inr last] <:+ z := List.suffix_of_suffix_length_le hl (List.suffix_append t z) (by simpa)
    exact (hw z v hv hzw ⟨last,he⟩).trans (List.suffix_append t z)

private lemma left_single_prefix (l x : A) (y : B) :
    ∀ u, u <+: [.inl l] → EndsR u → marked x y <:+ u := by
  rintro u hu ⟨z,hz⟩
  have h1 := hu.length_le
  have h2 := hz.length_le
  have hEq := hu.eq_of_length_le (by simpa using h2)
  subst u
  have he := hz.eq_of_length_le (by simp)
  simp at he

private lemma pair_prefix (x : A) (y : B) :
    ∀ u, u <+: marked x y → EndsR u → marked x y <:+ u := by
  rintro u hu ⟨z,hz⟩
  by_cases h : (marked x y).length ≤ u.length
  · rw [hu.eq_of_length_le h]
  · have hu1 : u.length = 1 := by
      have := hz.length_le
      simp [marked] at h this
      omega
    have he := hz.eq_of_length_le (by simp [hu1])
    subst u
    have h' := List.prefix_iff_eq_take.mp hu
    simp [marked] at h'

private lemma ends_prepend {t w : List (Letter A B)} (hw : EndsR w) : EndsR (t++w) := by
  obtain ⟨z,hw⟩ := hw
  exact ⟨z,hw.trans (List.suffix_append t w)⟩

private lemma long_unmarked {x : A} {y : B} {t w : List (Letter A B)}
    (hlen : 2≤w.length) (hw : ¬ marked x y <:+ w) : ¬ marked x y <:+ t++w := by
  intro h
  exact hw (List.suffix_of_suffix_length_le h (List.suffix_append t w) (by simpa [marked]))

private lemma left_prepend {x : A} {y : B} {w : List (Letter A B)}
    (l : A) (hlen : 2≤w.length) (hw : Good x y w) : Good x y (.inl l::w) :=
  ⟨ends_prepend (t:=[.inl l]) hw.1, long_unmarked (t:=[.inl l]) hlen hw.2.1,
   prefix_rule_prepend (left_single_prefix l x y) hw.2.2⟩

private lemma pair_prepend {x : A} {y : B} {w : List (Letter A B)}
    (hw : Good x y w) : Good x y (marked x y++w) := by
  refine ⟨ends_prepend hw.1,?_,prefix_rule_prepend (pair_prefix x y) hw.2.2⟩
  by_cases h : 2≤w.length
  · exact long_unmarked h hw.2.1
  · obtain ⟨z,hz⟩ := hw.1
    have he := hz.eq_of_length_le (by simp; omega)
    subst w
    intro hm
    have hh := List.suffix_of_suffix_length_le hm (List.suffix_append (α:=Letter A B) [.inl x] [.inr y,.inr z]) (by simp [marked])
    have eq := hh.eq_of_length_le (by simp [marked])
    simp [marked] at eq

private lemma singleton_good (x : A) (y z : B) : Good x y [.inr z] := by
  refine ⟨⟨z,⟨[],rfl⟩⟩,fun h => ?_,?_⟩
  · have := h.length_le; simp [marked] at this
  · rintro u v hv h ⟨z,hz⟩
    have a := congrArg List.length h
    have b := hz.length_le
    have c : 0<v.length := List.length_pos_iff.mpr hv
    simp at a b
    omega

private lemma pair_good (x : A) (y : B) (l : A) (z : B)
    (hneq : [.inl l,.inr z] ≠ marked x y) : Good x y [.inl l,.inr z] := by
  refine ⟨⟨z,List.suffix_append (α:=Letter A B) [.inl l] [.inr z]⟩,fun h => ?_,?_⟩
  · apply hneq
    exact (h.eq_of_length_le (by simp [marked])).symm
  · exact prefix_rule_prepend (left_single_prefix l x y) (singleton_good x y z).2.2

private def pairWord (p : A×B) : List (Letter A B) := [.inl p.1,.inr p.2]
private def prepend (p : A×List (Letter A B)) : List (Letter A B) := .inl p.1 :: p.2

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- words x y j consists of the words of length j+1. The length-one auxiliary
level contains the terminal letters. -/
def words (x : A) (y : B) : ℕ → Finset (List (Letter A B))
  | 0 => Finset.univ.image (fun z : B => [Sum.inr z])
  | 1 => (Finset.univ.image (@pairWord A B)).erase (marked x y)
  | j+2 => ((Finset.univ.product (words x y (j+1))).image prepend) ∪
      ((words x y j).image (fun w => marked x y++w))

theorem words_length_good (x : A) (y : B) (j : ℕ) (w : List (Letter A B)) (hw : w∈words x y j) :
    w.length=j+1 ∧ Good x y w := by
  induction j using Nat.twoStepInduction generalizing w with
  | zero =>
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hw
    exact ⟨rfl,singleton_good x y z⟩
  | one =>
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hw
    obtain ⟨⟨l,z⟩,_,rfl⟩ := Finset.mem_image.mp hm
    exact ⟨rfl,pair_good x y l z hne⟩
  | more j hp hn =>
    rcases Finset.mem_union.mp hw with h|h
    · obtain ⟨⟨l,v⟩,hv,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hlen,hg⟩ := hn v (Finset.mem_product.mp hv).2
      change v.length = j+1+1 at hlen
      exact ⟨by simp [prepend,hlen],left_prepend (w:=v) l (by omega) hg⟩
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hlen,hg⟩ := hp v hv
      exact ⟨by simp [marked,hlen],pair_prepend hg⟩

/-- No nonempty proper prefix of a constructed word is the suffix of another
word of the same length. The quantifiers also allow the same word twice. -/
theorem words_nonoverlapping (x : A) (y : B) (j : ℕ) (u pre post : List (Letter A B))
    (hu : u ≠ []) (hs : u.length < j+1)
    (h1 : u++post ∈ words x y j) (h2 : pre++u ∈ words x y j) : False := by
  obtain ⟨hl,hg⟩ := words_length_good x y j _ h1
  obtain ⟨_,gh⟩ := words_length_good x y j _ h2
  have hv : post≠[] := by intro h; subst post; simp at hl; omega
  obtain ⟨z,hz⟩ := gh.1
  have hru : [.inr z] <:+ u := List.suffix_of_suffix_length_le hz (List.suffix_append pre u) (by
    have hh : 0<u.length := List.length_pos_iff.mpr hu
    simpa)
  exact gh.2.1 ((hg.2.2 u post hv rfl ⟨z,hru⟩).trans (List.suffix_append pre u))



private lemma begins_left (x : A) (y : B) (j : ℕ) {w : List (Letter A B)}
    (hw : w ∈ words x y (j+1)) : ∃ l : A, ∃ v, w = .inl l :: v := by
  cases j with
  | zero =>
    obtain ⟨⟨l,z⟩,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hw).2
    exact ⟨l,[.inr z],rfl⟩
  | succ j =>
    rcases Finset.mem_union.mp hw with h|h
    · obtain ⟨⟨l,z⟩,_,rfl⟩ := Finset.mem_image.mp h
      exact ⟨l,z,rfl⟩
    · obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp h
      exact ⟨x,.inr y :: z,rfl⟩

theorem card_first (x : A) (y : B) : (words x y 0).card = Fintype.card B := by
  unfold words
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j h
    simpa using h

theorem card_second (x : A) (y : B) : (words x y 1).card = Fintype.card A * Fintype.card B - 1 := by
  unfold words
  rw [Finset.card_erase_of_mem,Finset.card_image_of_injective]
  · simp
  · rintro ⟨l,z⟩ ⟨l',z'⟩ h
    simpa [pairWord] using h
  · exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_univ _,rfl⟩

theorem card_rec (x : A) (y : B) (j : ℕ) : (words x y (j+2)).card =
    Fintype.card A * (words x y (j+1)).card + (words x y j).card := by
  rw [words, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective,Finset.card_image_of_injective]
    · simp
    · intro u v h
      simpa using h
    · rintro ⟨l,u⟩ ⟨l',u'⟩ h
      simpa [prepend] using h
  · apply Finset.disjoint_left.mpr
    rintro v hv hu
    obtain ⟨⟨l,w⟩,hw,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w',_,he⟩ := Finset.mem_image.mp hu
    obtain ⟨l',z,hz⟩ := begins_left x y j (Finset.mem_product.mp hw).2
    dsimp only at hz
    simp [marked,prepend,hz] at he

/-- The concrete word-set cardinalities coincide with the integer recurrence
    in the quantitative lower-bound argument. -/
theorem words_card (x : A) (y : B) (j : ℕ) : (words x y (j+1)).card =
    Lower.rightCount (Fintype.card A) (Fintype.card B) j := by
  induction j using Nat.twoStepInduction with
  | zero => exact card_second x y
  | one => rw [card_rec x y 0,card_first,card_second];rfl
  | more j hp hn => rw [card_rec x y (j+1),hn,hp];rfl


open Nonoverlap.Analytic

private lemma increasing_before (k : ℕ) {s x : ℝ} (hs : 0≤s) (hsx : s≤x) (hxc : x≤peak k) :
    score k s ≤ score k x := by
  apply (monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s x)
    (continuous_iff_continuousAt.mpr fun t => (hder k t).continuousAt).continuousOn
    (fun t _ => (hder k t).hasDerivWithinAt) ?_) ⟨le_rfl,hsx⟩ ⟨hsx,le_rfl⟩ hsx
  intro t ht
  have hh : t ∈ Set.Icc s x := interior_subset ht
  exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (hh.2.trans hxc)))
    (pow_nonneg (hs.trans hh.1) _)

private lemma scale_score (d q s : ℕ) (hq : 0<q) (hs : s≤q) :
    score d ((s:ℝ)/q)*(q:ℝ)^(d+2) = (s^(d+1)*(q-s):ℕ) := by
  have hq' : (q:ℝ)≠0 := by exact_mod_cast hq.ne'
  unfold score
  push_cast [Nat.cast_sub hs]
  rw [div_pow,show (q:ℝ)^(d+2) = (q:ℝ)^(d+1)*q by ring]
  field_simp

/-- If the lower grid point is at most half a grid step below the continuous
peak, every integer split scores no higher. The two hypotheses are integral. -/
theorem optimal_grid (d q a : ℕ) (hq : 0<q) (ha : a≤q)
    (hleft : (d+2)*a ≤ (d+1)*q)
    (hmid : 2*((d+1)*q) ≤ (d+2)*(2*a+1)) (s : ℕ) (hs : s≤q) :
    s^(d+1)*(q-s) ≤ a^(d+1)*(q-a) := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hd : (0:ℝ)<(d:ℝ)+2 := by positivity
  have hxc : (a:ℝ)/q ≤ peak d := by
    unfold peak
    apply (div_le_div_iff₀ hq' hd).2
    have hh : ((d:ℝ)+2)*a ≤ ((d:ℝ)+1)*q := by exact_mod_cast hleft
    linarith
  have hscore : score d ((s:ℝ)/q) ≤ score d ((a:ℝ)/q) := by
    by_cases hsa : s≤a
    · apply increasing_before d (by positivity) ?_ hxc
      exact (div_le_div_iff_of_pos_right hq').2 (by exact_mod_cast hsa)
    · have has : (a:ℝ)+1 ≤ s := by exact_mod_cast (show a+1 ≤s by omega)
      have hmid' : 2*(((d:ℝ)+1)*q) ≤ ((d:ℝ)+2)*(2*(a:ℝ)+1) := by exact_mod_cast hmid
      have mulcmp := mul_le_mul_of_nonneg_right has hd.le
      have midright : 2*(peak d) ≤ ((s:ℝ)+(a:ℝ))/q := by
        unfold peak
        rw [← mul_div_assoc]
        apply (div_le_div_iff₀ hd hq').2
        nlinarith
      apply lower_grid_better d (by positivity) hxc
      · rw [add_div] at midright
        linarith
      · rw [add_div] at midright
        linarith
  have realbound := mul_le_mul_of_nonneg_right hscore (show 0 ≤ (q:ℝ)^(d+2) by positivity)
  rw [scale_score d q s hq hs,scale_score d q a hq ha] at realbound
  exact_mod_cast realbound


/-- Fixed-length non-overlap on actual lists over the named alphabet. -/
def IsCode {D : Type} (n : ℕ) (C : Finset (List D)) : Prop :=
  (∀ w∈C, w.length=n) ∧
    ∀ u pre post, u ≠ [] → u.length<n → u++post ∈ C → pre++u ∈ C → False

private theorem map_back {D E : Type} (e : D≃E) (w : List D) :
    (w.map e).map e.symm = w := by simp [List.map_map]

theorem move_alphabet {D E : Type} [DecidableEq E] (e : D≃E)
    (C : Finset (List D)) {n : ℕ} (hc : IsCode n C) :
    let S := C.image (List.map e)
    S.card = C.card ∧ IsCode n S := by
  dsimp
  constructor
  · apply Finset.card_image_of_injective
    intro v w h
    simpa only [map_back] using congrArg (List.map e.symm) h
  · constructor
    · rintro w hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      simpa only [List.length_map] using hc.1 v hv
    · rintro u pre post hu hl h1 h2
      have mem_pre (w : List E) (h : w∈C.image (List.map e)) : w.map e.symm ∈ C := by
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
        simpa only [map_back] using hz
      exact hc.2 (u.map e.symm) (pre.map e.symm) (post.map e.symm) (by simpa using hu)
        (by simpa using hl) (by simpa only [List.map_append] using mem_pre _ h1)
        (by simpa only [List.map_append] using mem_pre _ h2)

set_option maxHeartbeats 1000000 in
/-- The explicit alphabet q = n(⌊n/2⌋−2)+⌈n/2⌉ admits a concrete
non-overlapping code strictly larger than every Blackburn split. -/
theorem explicit_word_counterexamples (n : ℕ) (hn : 12 ≤ n) :
    ∃ q : ℕ, ∃ C : Finset (List (Fin q)), q = n*(n/2-2)+(n+1)/2 ∧ n^2 ≤ 2*q+4*n ∧ IsCode n C ∧
      ∀ s ≤ q, s^(n-1)*(q-s) < C.card := by
  let k := n/2-2
  let e := n%2
  have hk : 4≤k := by dsimp [k]; omega
  have he : e≤1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  have hnrep : n=2*k+e+4 := by dsimp [k,e]; omega
  let j := 2*k+e
  let a := k*(j+4)+1+e
  let b := k+1
  let q := a+b
  have hN : n=j+4 := hnrep
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0<b := Nat.succ_pos k
  let x : Fin a := ⟨0,ha⟩
  let y : Fin b := ⟨0,hb⟩
  let D := words x y (j+3)
  let emb : (Fin a ⊕ Fin b) ≃ Fin q := finSumFinEquiv
  let C := D.image (List.map emb)
  have hD : IsCode n D := by
    refine ⟨?_,?_⟩
    · intro w hw
      simpa only [hN] using (words_length_good x y (j+3) w hw).1
    · intro u v w hu hl hv hw
      exact words_nonoverlapping x y (j+3) u v w hu (by omega) hv hw
  obtain ⟨hcard,hC⟩ := move_alphabet emb D hD
  have he01 : e=0 ∨ e=1 := by omega
  have hqbound : n^2 ≤ 2*q+4*n := by
    rw [hN]
    dsimp [q,a,b,j]
    rcases he01 with he'|he' <;> rw [he'] <;> nlinarith
  have hqexact : q = n*(n/2-2)+(n+1)/2 := by
    have hr : (n+1)/2 = k+2+e := by dsimp [k,e]; omega
    change a+b = n*k+(n+1)/2
    rw [hr,hN]
    dsimp [a,b]
    ring
  refine ⟨q,C,hqexact,hqbound,hC,?_⟩
  intro s hs
  have hleft : (j+2+2)*a ≤ (j+2+1)*q := by
    dsimp [q,a,b,j]
    rcases he01 with he'|he' <;> rw [he'] <;> nlinarith
  have hmid : 2*((j+2+1)*q) ≤ (j+2+2)*(2*a+1) := by
    dsimp [q,a,b,j]
    rcases he01 with he'|he' <;> rw [he'] <;> nlinarith
  have hg := optimal_grid (j+2) q a (by dsimp [q]; omega) (by dsimp [q]; omega) hleft hmid s hs
  have hwin : b*a^(j+3) < Lower.rightCount a b (j+2) := Lower.quadratic_family k e hk he
  have hreal : D.card = Lower.rightCount a b (j+2) := by
    simpa [D] using words_card x y (j+2)
  change s^(n-1)*(q-s) < (D.image (List.map emb)).card
  rw [hcard,hreal,show n-1=j+3 by omega]
  apply lt_of_le_of_lt _ hwin
  simpa [q,Nat.add_sub_cancel_left,Nat.mul_comm] using hg

/-- At every length n≥12 some alphabet of size q≥(n²-4n)/2 has a concrete
non-overlapping code strictly larger than every Blackburn split. -/
theorem quadratic_word_counterexamples (n : ℕ) (hn : 12 ≤ n) :
    ∃ q : ℕ, ∃ C : Finset (List (Fin q)), n^2 ≤ 2*q+4*n ∧ IsCode n C ∧
      ∀ s ≤ q, s^(n-1)*(q-s) < C.card := by
  obtain ⟨q,C,_,bound,valid,strict⟩ := explicit_word_counterexamples n hn
  exact ⟨q,C,bound,valid,strict⟩

#print axioms quadratic_word_counterexamples
end NonoverlapThreshold.WordLower
