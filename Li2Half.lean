import Li2Unified.Modular.Positive.Packed.P231

open scoped BigOperators

/-- `Li₂(1/2) = ∑_{n ≥ 1} 2⁻ⁿ / n²` is irrational. -/
theorem li2_one_half_irrational :
    Irrational (∑' k : ℕ, (1/2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) ^ 2) :=
  @Li2Unified.Instances.PosHalf.irrational_series

#print axioms li2_one_half_irrational
