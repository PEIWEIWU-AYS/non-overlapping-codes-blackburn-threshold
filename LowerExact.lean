import ThresholdBounds

namespace NonoverlapThreshold

/-- The explicit exceptional alphabet is strictly smaller than the least threshold. -/
theorem explicit_lower (n : ℕ) (hn : 12 ≤ n) :
    n*(n/2-2)+(n+1)/2 < q₀ n := by
  obtain ⟨q,C,eq,_,valid,strict⟩ := WordLower.explicit_word_counterexamples n hn
  rw [← eq]
  by_contra! bad
  have spec := q₀_spec n _ (finite_upper n (by omega))
  obtain ⟨s,hs,B,_,size,maximal⟩ := spec.2 q bad
  have bound := maximal C valid
  rw [size] at bound
  exact (not_lt_of_ge bound) (strict s hs)

#print axioms explicit_lower
end NonoverlapThreshold
