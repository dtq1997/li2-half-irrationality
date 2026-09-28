module
public import Li2Unified.Modular.Base.RestrictedSeriesCompat
public import Li2Unified.Modular.Base.PrimeMonomialScaledLeading
public import Li2Unified.Modular.Base.PrimeIntegralJetBounds

set_option backward.privateInPublic true

@[expose] public section

/-! Compare an actual integer test polynomial with a scaled monomial on the
same disc. The error passes through every regular correction and residue. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma primeDiscMonomial_from_test (hp4 : 3 < p) (a : Fin p) (k : ℕ) :
    integralPoleMulRegular (primePoleCenters p)
      ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p])
      (primeDiscRegular hp4 a) (primeDiscResidue hp4 a) = primeDiscMonomialRegular hp4 a k ∧
    integralPoleMulResidue (primePoleCenters p)
      ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p])
      (primeDiscResidue hp4 a) = primeDiscMonomialResidue hp4 a k := by
  have h := integralPoleMultiplier_assoc (primePoleCenters p) primePoleCenters_injective
    ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) (primeDiscUnit a.val a.isLt)
    (primeDiscBaseRegular a) (polynomial_isRestricted _)
    (primeDiscUnit_isRestricted a.val a.isLt) (primeDiscBaseRegular_isRestricted a)
    (primeDiscBaseResidue hp4 a)
  rw [mul_comm ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) (primeDiscUnit a.val a.isLt)] at h
  exact h

lemma primePoleU_multiplier_smul (hp4 : 3 < p) (g f : PowerSeries ℤ_[p])
    (hg : PowerSeries.IsRestricted 1 g) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin 4 → ℤ_[p]) (q : ℤ_[p]) :
    primePoleU hp4 (integralPoleMulRegular (primePoleCenters p) (q • g) f r)
      (integralPoleMulResidue (primePoleCenters p) (q • g) r) =
      C q*primePoleU hp4 (integralPoleMulRegular (primePoleCenters p) g f r)
        (integralPoleMulResidue (primePoleCenters p) g r) := by
  have h := integralPoleMultiplier_smul (primePoleCenters p) primePoleCenters_injective g f hg hf r q
  rw [h.1,h.2]
  exact restrictedPoleFunctional_smul _ _ _
    (integralPoleMulRegular_isRestricted _ g f hg hf r) _ q

lemma primePoleV_multiplier_smul (hp4 : 3 < p) (g f : PowerSeries ℤ_[p])
    (hg : PowerSeries.IsRestricted 1 g) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin 4 → ℤ_[p]) (q : ℤ_[p]) :
    primePoleV hp4 (integralPoleMulRegular (primePoleCenters p) (q • g) f r)
      (integralPoleMulResidue (primePoleCenters p) (q • g) r) =
      C q*primePoleV hp4 (integralPoleMulRegular (primePoleCenters p) g f r)
        (integralPoleMulResidue (primePoleCenters p) g r) := by
  have h := integralPoleMultiplier_smul (primePoleCenters p) primePoleCenters_injective g f hg hf r q
  rw [h.1,h.2]
  exact restrictedPoleFunctional_smul _ _ _
    (integralPoleMulRegular_isRestricted _ g f hg hf r) _ q

lemma integralDiscTest_series_error (T : ℤ[X]) (a : Fin p) (q : ℤ_[p]) (k : ℕ)
    (B : ℝ) (he : ∀ n, ‖(integralDiscTestPolynomial T a-C q*X^k).coeff n‖ ≤ B) (n : ℕ) :
    ‖PowerSeries.coeff n ((integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) -
      q • ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p]))‖ ≤ B := by
  rw [PowerSeries.smul_eq_C_mul, ← Polynomial.coe_C, ← Polynomial.coe_mul,
    ← Polynomial.coe_sub, Polynomial.coeff_coe]
  exact he n

theorem primeDiscTest_U_jet_error (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (q : ℤ_[p]) (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (he : ∀ n, ‖(integralDiscTestPolynomial T a-C q*X^k).coeff n‖ ≤ B) (n : ℕ) :
    ‖(primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T) -
      C q*primePoleU hp4 (primeDiscMonomialRegular hp4 a k)
        (primeDiscMonomialResidue hp4 a k)).coeff n‖ ≤ B := by
  have h : ‖(primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T) -
      primePoleU hp4 (integralPoleMulRegular (primePoleCenters p)
        (q • ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p])) (primeDiscRegular hp4 a) (primeDiscResidue hp4 a))
        (integralPoleMulResidue (primePoleCenters p)
          (q • ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p])) (primeDiscResidue hp4 a))).coeff n‖ ≤ B :=
    restrictedPoleFunctional_multiplier_difference _ primePoleCenters_injective _ _ _ _ _
      (polynomial_isRestricted _) (Li2.restrictedSeries_smul 1 (polynomial_isRestricted _) q)
      (primeDiscRegular_isRestricted hp4 a) _ B hB (integralDiscTest_series_error T a q k B he) n
  rw [primePoleU_multiplier_smul hp4 _ _ (polynomial_isRestricted _)
    (primeDiscRegular_isRestricted hp4 a),
    (primeDiscMonomial_from_test hp4 a k).1, (primeDiscMonomial_from_test hp4 a k).2] at h
  exact h

theorem primeDiscTest_V_jet_error (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (q : ℤ_[p]) (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (he : ∀ n, ‖(integralDiscTestPolynomial T a-C q*X^k).coeff n‖ ≤ B) (n : ℕ) :
    ‖(primePoleV hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T) -
      C q*primePoleV hp4 (primeDiscMonomialRegular hp4 a k)
        (primeDiscMonomialResidue hp4 a k)).coeff n‖ ≤ B := by
  have h : ‖(primePoleV hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T) -
      primePoleV hp4 (integralPoleMulRegular (primePoleCenters p)
        (q • ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p])) (primeDiscRegular hp4 a) (primeDiscResidue hp4 a))
        (integralPoleMulResidue (primePoleCenters p)
          (q • ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p])) (primeDiscResidue hp4 a))).coeff n‖ ≤ B :=
    restrictedPoleFunctional_multiplier_difference _ primePoleCenters_injective _ _ _ _ _
      (polynomial_isRestricted _) (Li2.restrictedSeries_smul 1 (polynomial_isRestricted _) q)
      (primeDiscRegular_isRestricted hp4 a) _ B hB (integralDiscTest_series_error T a q k B he) n
  rw [primePoleV_multiplier_smul hp4 _ _ (polynomial_isRestricted _)
    (primeDiscRegular_isRestricted hp4 a),
    (primeDiscMonomial_from_test hp4 a k).1, (primeDiscMonomial_from_test hp4 a k).2] at h
  exact h

end
end Li2

end
