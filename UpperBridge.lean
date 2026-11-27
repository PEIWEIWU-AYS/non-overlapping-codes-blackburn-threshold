import Interior
import Upper
import LayerData

open scoped BigOperators
namespace Nonoverlap.Bridge

private lemma memTail {N i j : ℕ} : (i,j) ∈ tailPairs N ↔
    1 ≤ i ∧ i ≤ N+2 ∧ 1 ≤ j ∧ j ≤ N+2 ∧ N+3 < i+j := by
  simp [tailPairs,domain,and_assoc]

private lemma weighted_nonneg {N : ℕ} {l r : ℕ → ℝ} {ρ : ℝ}
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i) (hρ : 0 ≤ ρ) (p : ℕ×ℕ) :
    0 ≤ l p.1*r p.2*ρ^(p.1+p.2-(N+3)) :=
  mul_nonneg (mul_nonneg (hl _) (hr _)) (pow_nonneg hρ _)

theorem tail_nonneg {N : ℕ} {l r : ℕ → ℝ} {ρ : ℝ}
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i) (hρ : 0 ≤ ρ) :
    0 ≤ tail N l r ρ := Finset.sum_nonneg (fun p _ => weighted_nonneg hl hr hρ p)

private def p1 (N i : ℕ) : ℕ × ℕ := (i+2, N+2-i)
private def p2 (N i : ℕ) : ℕ × ℕ := (N+2-i, i+3)

theorem diagonals_le_tail {N : ℕ} {l r : ℕ → ℝ} {ρ : ℝ}
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i) (hρ : 1 ≤ ρ) :
    (∑ i ∈ Finset.range (N+1), l (i+2)*r (N+2-i)) +
      (∑ i ∈ Finset.range N, r (i+3)*l (N+2-i)) ≤ tail N l r ρ := by
  let A := (Finset.range (N+1)).image (p1 N)
  let B := (Finset.range N).image (p2 N)
  let f := fun p : ℕ × ℕ => l p.1*r p.2
  have s1 (i) (hi : i ∈ Finset.range (N+1)) : p1 N i ∈ tailPairs N := by
    rw [p1,memTail]; have := Finset.mem_range.mp hi; omega
  have s2 (i) (hi : i ∈ Finset.range N) : p2 N i ∈ tailPairs N := by
    rw [p2,memTail]; have := Finset.mem_range.mp hi; omega
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p ha hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hb
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp [p1,p2] at h1 h2
    have := Finset.mem_range.mp hi
    have := Finset.mem_range.mp hj
    omega
  have hsub : A ∪ B ⊆ tailPairs N := by
    intro p hp
    rcases Finset.mem_union.mp hp with ha | hb
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      exact s1 i hi
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
      exact s2 i hi
  have point : (∑ p ∈ A ∪ B, f p) ≤ ∑ p ∈ tailPairs N, f p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => mul_nonneg (hl _) (hr _))
  have inj1 : Function.Injective (p1 N) := by
    intro i j e
    exact Nat.add_right_cancel (congrArg Prod.fst e)
  have inj2 : Function.Injective (p2 N) := by
    intro i j e
    exact Nat.add_right_cancel (congrArg Prod.snd e)
  unfold A B at point
  rw [Finset.sum_union hdis,Finset.sum_image inj1.injOn, Finset.sum_image inj2.injOn] at point
  have hweight : (∑ p ∈ tailPairs N, f p) ≤ tail N l r ρ := by
    apply Finset.sum_le_sum
    intro p _
    simpa [f] using mul_le_mul_of_nonneg_left
      (one_le_pow₀ hρ : 1 ≤ ρ^(p.1+p.2-(N+3))) (mul_nonneg (hl p.1) (hr p.2))
  simpa only [f,p1,p2,mul_comm] using point.trans hweight

theorem diag_split (N : ℕ) (l r : ℕ → ℝ) :
    diag (N+3) l r = l 1*r (N+2) + l (N+2)*r 1 +
      ∑ i ∈ Finset.range N, l (i+2)*r (N+1-i) := by
  unfold diag
  change (∑ i ∈ Finset.range ((N+1)+1), l (i+1)*r (N+2-i)) = _
  rw [Finset.sum_range_succ',Finset.sum_range_succ]
  simp
  ring

theorem diag_swap (d : ℕ) (l r : ℕ → ℝ) : diag d l r = diag d r l := by
  unfold diag
  rw [← Finset.sum_range_reflect (fun i => l (i+1)*r (d-1-i))]
  apply Finset.sum_congr rfl
  intro i hi
  have : i < d-1 := Finset.mem_range.mp hi
  rw [show d-1-1-i+1=d-1-i by omega,show d-1-(d-1-1-i)=i+1 by omega,mul_comm]

theorem step_endpoints {N : ℕ} {l r : ℕ → ℝ}
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i)
    (law : ∀ i, 2 ≤ i → i ≤ N+2 → l i + r i = diag i l r)
    (i : ℕ) (hi : 2 ≤ i) (hup : i ≤ N+1) :
    l 1*r i + l i*r 1 ≤ l (i+1)+r (i+1) := by
  rw [law (i+1) (by omega) (by omega)]
  obtain ⟨j,rfl⟩ : ∃ j, i=j+2 := ⟨i-2, by omega⟩
  rw [show j+2+1=j+3 by omega,diag_split]
  linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.range j) => mul_nonneg (hl (i+2)) (hr (j+1-i)))]


/-- Each of the two endpoint products in the next coefficient is present;
    their index slots are distinct once i is at least two. -/
theorem step_from_recurrence {N : ℕ} {l r : ℕ → ℝ} {m : ℝ}
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i)
    (hmL : m ≤ l 1) (hmR : m ≤ r 1)
    (law : ∀ i, 2 ≤ i → i ≤ N+2 → l i + r i = diag i l r) :
    (∀ i, 2 ≤ i → i ≤ N+1 → m*l i ≤ l (i+1)+r (i+1)) ∧
    (∀ i, 2 ≤ i → i ≤ N+1 → m*r i ≤ l (i+1)+r (i+1)) := by
  have h := step_endpoints hl hr law
  constructor
  · intro i h1 h2
    nlinarith [h i h1 h2, mul_le_mul_of_nonneg_right hmR (hl i), mul_nonneg (hl 1) (hr i)]
  · intro i h1 h2
    linarith [h i h1 h2, mul_le_mul_of_nonneg_right hmL (hr i), mul_nonneg (hl i) (hr 1)]


/-- Taking the final column of the exact weighted tail gives the endpoint penalty. -/
theorem boundary_tail {N : ℕ} {l r : ℕ → ℝ} {ρ : ℝ}
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i) (hρ : 1 ≤ ρ) (hv : value N l ρ=1) :
    r (N+2)*(1/ρ-l 1) ≤ tail N l r ρ := by
  have hpos : 0 < ρ := by linarith
  let S := Finset.Icc 2 (N+2)
  let f := fun i : ℕ => (i,N+2)
  let g := fun p : ℕ×ℕ => l p.1*r p.2*ρ^(p.1+p.2-(N+3))
  have hdom : domain N = insert 1 S := by
    ext i; simp [domain,S]; omega
  have hnot : 1 ∉ S := by simp [S]
  unfold value at hv
  rw [hdom,Finset.sum_insert hnot,pow_one] at hv
  have hsub : S.image f ⊆ tailPairs N := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    have hi' : 2 ≤ i ∧ i ≤ N+2 := Finset.mem_Icc.mp hi
    exact memTail.mpr (by omega)
  have hinj : Function.Injective f := by intro i j e; exact congrArg Prod.fst e
  have hsum : (∑ p ∈ S.image f, g p) ≤ tail N l r ρ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => weighted_nonneg hl hr (by linarith) p)
  rw [Finset.sum_image hinj.injOn] at hsum
  have hpart : ∀ i ∈ S, g (f i) = l i*ρ^i * (r (N+2)/ρ) := by
    intro i hi
    have hi' : 2 ≤ i ∧ i ≤ N+2 := Finset.mem_Icc.mp hi
    dsimp [f,g]
    rw [show i+(N+2)-(N+3)=i-1 by omega]
    field_simp
    rw [show i=(i-1)+1 by omega] at *
    ring_nf
    simp
  rw [Finset.sum_congr rfl hpart,← Finset.sum_mul] at hsum
  have he : r (N+2)*(1/ρ-l 1) = (∑ i ∈ S, l i * ρ^i)*(r (N+2)/ρ) := by
    rw [show (∑ i ∈ S, l i * ρ^i)=1-l 1*ρ by linarith]
    field_simp
    ring
  exact he ▸ hsum

open Nonoverlap.Analytic

private lemma score_mono_left (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ peak k) :
    score k a ≤ score k b := by
  have hpeak : ((k:ℝ)+2)*peak k = k+1 := by unfold peak; field_simp
  apply (monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (peak k))
    (f' := fun x : ℝ => ((k:ℝ)+2)*(peak k-x)*x^k)
    (by unfold score; fun_prop) ?_ ?_) ⟨ha,hab.trans hb⟩ ⟨ha.trans hab,hb⟩ hab
  · intro x _
    have h := ((hasDerivAt_id x).pow (k+1)).mul ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))
    apply HasDerivAt.hasDerivWithinAt
    convert h using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, id_eq, mul_one, zero_sub, mul_neg, pow_succ]
    linear_combination (x^k)*hpeak
  · intro x hx
    have hi : x ∈ Set.Icc 0 (peak k) := interior_subset hx
    exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hi.2)) (pow_nonneg hi.1 _)

theorem score_peak (k : ℕ) {t : ℝ} (ht : 0 ≤ t) : score k t ≤ score k (peak k) := by
  rcases le_total t (peak k) with h|h
  · exact score_mono_left k ht h le_rfl
  · exact lower_grid_better k (by unfold peak; positivity) le_rfl h (by linarith)


private lemma endpoint_cases (N : ℕ) {l r : ℕ → ℝ} {M : ℝ}
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i)
    (ha : l 1 ≤ ((N:ℝ)+1)/(N+2)) (hL : M/2 ≤ r (N+2))
    (root : RootData N l r M) :
    M ≤ score (N+1) (Upper.midpoint (N+1)) ∨
    M*(1/((N:ℝ)+3))*(1/((N:ℝ)+2))/4 ≤ score (N+1) (peak (N+1))-M := by
  obtain ⟨ρ,hρ,hv,he⟩ := root
  have hpos : 0 < ρ := by linarith
  let t := 1/ρ
  have ht : 0 ≤ t := by dsimp [t]; positivity
  change score (N+1) t = _ at he
  let δ : ℝ := 1/(2*((N:ℝ)+3)*(N+2))
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hdiff : Upper.midpoint (N+1) = ((N:ℝ)+1)/(N+2)+δ := by
    unfold Upper.midpoint peak δ
    push_cast
    field_simp
    ring
  have hdiff' : peak (N+1) = Upper.midpoint (N+1)+δ := by
    unfold Upper.midpoint peak δ
    push_cast
    field_simp
    ring
  rcases le_total t (Upper.midpoint (N+1)) with h|h
  · left
    have hmono := score_mono_left (N+1) ht h (by linarith : Upper.midpoint (N+1) ≤ peak (N+1))
    linarith [tail_nonneg hl hr (by linarith : 0 ≤ ρ) (N:=N)]
  · right
    have hstep : δ ≤ t-l 1 := by linarith
    have bound := boundary_tail hl hr hρ hv
    change r (N+2)*(t-l 1) ≤ _ at bound
    have hp := mul_le_mul hL hstep hδ (hr (N+2))
    have hpeak := score_peak (N+1) ht
    have eq : M*(1/((N:ℝ)+3))*(1/((N:ℝ)+2))/4 = M/2*δ := by dsimp [δ]; field_simp; ring_nf; simp
    linarith

/-- Moderate normalized partitions are beaten by an actual Blackburn split.
    The only external input besides their defining coefficient recurrence is
    the exact root identity in both orientations. -/
theorem moderate_excluded (N q : ℕ) (hq : 4*(N+3)*(N+2) ≤ q)
    (l r : ℕ → ℝ) (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, 0 ≤ r i)
    (first : l 1+r 1=1)
    (law : ∀ i, 2 ≤ i → i ≤ N+2 → l i+r i=diag i l r)
    (hmodL : l 1 ≤ ((N:ℝ)+1)/(N+2)) (hmodR : r 1 ≤ ((N:ℝ)+1)/(N+2))
    (rootL : RootData N l r (diag (N+3) l r)) (rootR : RootData N r l (diag (N+3) l r)) :
    ∃ s : ℕ, 0 < s ∧ s < q ∧ diag (N+3) l r < score (N+1) ((s:ℝ)/q) := by
  let m : ℝ := 1/((N:ℝ)+2)
  let M := diag (N+3) l r
  let I := ∑ i ∈ Finset.range N, l (i+2)*r (N+1-i)
  have hI : 0 ≤ I := Finset.sum_nonneg fun i _ => mul_nonneg (hl _) (hr _)
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => mul_nonneg (hl _) (hr _)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hm' : m ≤ 1 := by dsimp [m]; apply (div_le_iff₀ (by positivity)).2; linarith [Nat.cast_nonneg (α:=ℝ) N]
  have eq : m + ((N:ℝ)+1)/(N+2)=1 := by dsimp [m]; field_simp; ring
  have hmL : m ≤ l 1 := by linarith
  have hmR : m ≤ r 1 := by linarith
  apply Upper.exists_better_split _ q (by omega) hq (m:=m)
  · dsimp [m]; push_cast; ring_nf; exact le_rfl
  · change M ≤ score (N+1) (Upper.midpoint (N+1)) ∨ _ ∨ _
    rcases le_total (M/2) I with h|h
    · right; right
      obtain ⟨sl,sr⟩ := step_from_recurrence hl hr hmL hmR law
      have d1 := NonoverlapThreshold.Interior.diagonal_tail_bound N l r m hm hm' hl hr sl sr
      obtain ⟨ρ,hρ,_,he⟩ := rootL
      have d2 := diagonals_le_tail (N:=N) hl hr hρ
      have d := d1.trans d2
      change m^2/8*I ≤ _ at d
      have p := score_peak (N+1) (by positivity : 0 ≤ 1/ρ)
      nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg m)]
    · have split := diag_split N l r
      change M=l 1*r (N+2) + l (N+2)*r 1 + I at split
      have dis : M/2 ≤ r (N+2) ∨ M/2 ≤ l (N+2) := by
        rcases le_total (r (N+2)) (l (N+2)) with he|he
        · right
          nlinarith [mul_le_mul_of_nonneg_left he (hl 1),
            show (l 1+r 1)*l (N+2) = l (N+2) by rw [first,one_mul]]
        · left
          nlinarith [mul_le_mul_of_nonneg_left he (hr 1),
            show (l 1+r 1)*r (N+2) = r (N+2) by rw [first,one_mul]]
      have ep : M ≤ score (N+1) (Upper.midpoint (N+1)) ∨
          M*(1/((N:ℝ)+3))*(1/((N:ℝ)+2))/4 ≤ score (N+1) (peak (N+1))-M := by
        rcases dis with d|d
        · exact endpoint_cases N hl hr hmodL d rootL
        · exact endpoint_cases N hr hl hmodR d rootR
      rcases ep with e|e
      · exact Or.inl e
      · right; left
        convert e using 1
        push_cast
        dsimp [M]
        ring_nf

end Nonoverlap.Bridge
