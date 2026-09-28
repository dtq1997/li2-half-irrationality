module
public import Li2Unified.Modular.Base.RestrictedSeriesCompat
public import Li2Unified.Modular.Base.PrimeMonomialLeading
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

lemma integralDiscTest_series_error (T : ℤ[X]) (a : Fin p) (q : ℤ_[p]) (k : ℕ)
    (B : ℝ) (he : ∀ n, ‖(integralDiscTestPolynomial T a-C q*X^k).coeff n‖ ≤ B) (n : ℕ) :
    ‖PowerSeries.coeff n ((integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) -
      q • ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p]))‖ ≤ B := by
  rw [PowerSeries.smul_eq_C_mul, ← Polynomial.coe_C, ← Polynomial.coe_mul,
    ← Polynomial.coe_sub, Polynomial.coeff_coe]
  exact he n

end
end Li2

end
