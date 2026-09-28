module
public import Li2Unified.Modular.Base.IntegralPolynomialSubstitution
public import Li2Unified.Modular.Base.PrimeNormReduction

set_option backward.privateInPublic true

@[expose] public section

/-! Transfer the actual disc-unit and substitution errors to a specified
Q_p leading value. All substitutions have integral eta. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem integralPolynomial_rational_constant_bound
    (F : (ℤ_[p])[X]) (v : ℤ_[p]) (q : ℚ_[p])
    (hF : ∀ n, ‖(F-C v).coeff n‖ ≤ ‖(p:ℤ_[p])‖)
    (hv : ‖(v:ℚ_[p])-q‖ ≤ ‖(p:ℚ_[p])‖) (n : ℕ) :
    ‖((F.map (algebraMap ℤ_[p] ℚ_[p]))-C q).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  have he : F.map (algebraMap ℤ_[p] ℚ_[p])-C q =
      (F-C v).map (algebraMap ℤ_[p] ℚ_[p])+C ((v:ℚ_[p])-q) := by
    simp only [Polynomial.map_sub, Polynomial.map_C, C_sub, PadicInt.algebraMap_apply]
    ring
  rw [he, coeff_add]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · simpa only [coeff_map] using! hF n
  · by_cases hn : n = 0
    · simpa [hn] using hv
    · simp [coeff_C, hn]

end
end Li2

end
