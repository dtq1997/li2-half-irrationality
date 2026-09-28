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

theorem primeDiscPole_U_substituted_rational (hp4 : 3 < p) (a : ℕ) (ha : a < p)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin 4 → ℤ_[p]) (eta : ℤ_[p]) (q : ℚ_[p])
    (hq : ‖(((primePoleU hp4 f r).eval 0:ℤ_[p]):ℚ_[p])-q‖ ≤ ‖(p:ℚ_[p])‖) (n : ℕ) :
    ‖(((primePoleU hp4
        (integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a ha) f r)
        (integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a ha) r)).comp
          (C ((p:ℤ_[p])^2)*(X-C eta))).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((primeDiscUnitConstant a ha:ℚ_[p])*q)).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  apply integralPolynomial_rational_constant_bound
    _ (primeDiscUnitConstant a ha*(primePoleU hp4 f r).eval 0) _
    (primeDiscPole_U_substituted_leading hp4 a ha f hf r eta)
  have hmul : ‖(primeDiscUnitConstant a ha:ℚ_[p]) *
      ((((primePoleU hp4 f r).eval 0:ℤ_[p]):ℚ_[p])-q)‖ ≤ ‖(p:ℚ_[p])‖ := by
    rw [norm_mul]
    exact (mul_le_mul (PadicInt.norm_le_one _) hq (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul _)
  simpa only [PadicInt.coe_mul, mul_sub] using hmul

theorem primeDiscPole_V_substituted_rational (hp4 : 3 < p) (a : ℕ) (ha : a < p)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin 4 → ℤ_[p]) (eta : ℤ_[p]) (q : ℚ_[p])
    (hq : ‖(((primePoleV hp4 f r).eval 0:ℤ_[p]):ℚ_[p])-q‖ ≤ ‖(p:ℚ_[p])‖) (n : ℕ) :
    ‖(((primePoleV hp4
        (integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a ha) f r)
        (integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a ha) r)).comp
          (C ((p:ℤ_[p])^2)*(X-C eta))).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((primeDiscUnitConstant a ha:ℚ_[p])*q)).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  apply integralPolynomial_rational_constant_bound
    _ (primeDiscUnitConstant a ha*(primePoleV hp4 f r).eval 0) _
    (primeDiscPole_V_substituted_leading hp4 a ha f hf r eta)
  have hmul : ‖(primeDiscUnitConstant a ha:ℚ_[p]) *
      ((((primePoleV hp4 f r).eval 0:ℤ_[p]):ℚ_[p])-q)‖ ≤ ‖(p:ℚ_[p])‖ := by
    rw [norm_mul]
    exact (mul_le_mul (PadicInt.norm_le_one _) hq (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul _)
  simpa only [PadicInt.coe_mul, mul_sub] using hmul

end
end Li2

end
