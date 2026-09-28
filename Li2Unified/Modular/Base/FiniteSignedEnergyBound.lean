module
public import Li2Unified.Modular.Base.FiniteSignedEnergyAlgebra
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

set_option backward.privateInPublic true

@[expose] public section
open scoped BigOperators
namespace Li2
theorem finite_signed_energy_cross_sum_upper {h : ℕ} (T M ε : ℝ) (L : Fin h → ℝ)
    (E : Option (Fin h) → Option (Fin h) → ℝ)
    (hcross : ∀ i : Fin h, E (some i) none ≤ T * (L i + 2 * M * ε)) :
    (∑ i : Fin h, E (some i) none) ≤ T * ((∑ i : Fin h, L i) + 2 * M * ε * (h : ℝ)) := by
  classical
  calc
    _ ≤ ∑ i : Fin h, T * (L i + 2 * M * ε) := by
      apply Finset.sum_le_sum; intro i _; exact hcross i
    _ = T * (∑ i : Fin h, (L i + 2 * M * ε)) := by rw [Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
end Li2

end
