import Analytic

open scoped BigOperators
namespace Nonoverlap.Bridge

/-- At block length N+3, coefficient indices are 1,...,N+2. -/
def domain (N : ℕ) : Finset ℕ := Finset.Icc 1 (N+2)

def value (N : ℕ) (l : ℕ → ℝ) (ρ : ℝ) : ℝ := ∑ i ∈ domain N, l i * ρ^i

def tailPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((domain N) ×ˢ (domain N)).filter (fun p : ℕ × ℕ => N+3 < p.1+p.2)

def tail (N : ℕ) (l r : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  ∑ p ∈ tailPairs N, l p.1 * r p.2 * ρ^(p.1+p.2-(N+3))

def diag (d : ℕ) (l r : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (d-1), l (i+1)*r (d-1-i)

/-- Root and exact tail identity used in the quantitative argument. -/
def RootData (N : ℕ) (l r : ℕ → ℝ) (M : ℝ) : Prop :=
  ∃ ρ : ℝ, 1 ≤ ρ ∧ value N l ρ=1 ∧
    Analytic.score (N+1) (1/ρ) = M + tail N l r ρ

end Nonoverlap.Bridge
