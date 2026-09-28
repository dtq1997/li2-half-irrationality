module

public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Irrationality of the dilogarithm at one half

The result states that the real number
`Li₂(1/2) = ∑_{n ≥ 1} 2⁻ⁿ / n²` is irrational, with no extra hypotheses.
The series is written below with index `k = n - 1`.
Its statement uses only the standard Mathlib meanings of real numbers,
infinite summation, and irrationality.

This file specifies the statement for Comparator. Its deliberate proof hole
is replaced by the proof in `Solution.lean` during comparison.
-/

open scoped BigOperators

/-- The dilogarithm at one half, given by its real power series, is irrational. -/
public theorem li2_one_half_irrational :
    Irrational (∑' k : ℕ, (1/2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) ^ 2) := sorry
