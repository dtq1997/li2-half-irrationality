module
public import Li2Unified.Modular.Base.RationalPoleClearing
public import Li2Unified.Modular.Base.RationalBaseCongruence
public import Li2Unified.Modular.Base.PrimeNormReduction

set_option backward.privateInPublic true

@[expose] public section

/-! Actual integral base presentations have the rational leading values,
with an error divisible by p. The parameter remains (-1/2)^p. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem primeZeroShape_U_value_norm (hp4 : 3 < p) (k : Fin 5) :
    let g := integralPoleMulRegular (primePoleCenters p)
      ((X^k.val : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) 0 (primeZeroShapeResidue hp4)
    let s := integralPoleMulResidue (primePoleCenters p)
      ((X^k.val : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) (primeZeroShapeResidue hp4)
    ‖(((primePoleU hp4 g s).eval 0:ℤ_[p]):ℚ_[p]) -
      ((![-113/12,95/4,-253/4,2093/12,-17773/36] k:ℚ):ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  apply integralPolynomial_eval_zero_norm_of_rational
  · exact (primeZeroShape_monomial_rational hp4 k 0).1
  · exact zeroShape_U_prime_values hp4 k

theorem primeLowShape_V_value_norm (hp4 : 3 < p) (k : Fin 3) :
    let g := integralPoleMulRegular (primePoleCenters p)
      ((X^k.val : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) 0 (primeLowShapeResidue hp4)
    let s := integralPoleMulResidue (primePoleCenters p)
      ((X^k.val : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) (primeLowShapeResidue hp4)
    ‖(((primePoleV hp4 g s).eval 0:ℤ_[p]):ℚ_[p]) -
      ((![95/4,-253/4,2093/12] k:ℚ):ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  apply integralPolynomial_eval_zero_norm_of_rational
  · exact (primeLowShape_monomial_rational hp4 k 0).2
  · exact lowShape_V_prime_values hp4 k

theorem primeHighShape_V_value_norm (hp4 : 3 < p) (k : Fin 3) :
    let g := integralPoleMulRegular (primePoleCenters p)
      ((X^k.val : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) 1 primeHighShapeResidue
    let s := integralPoleMulResidue (primePoleCenters p)
      ((X^k.val : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) primeHighShapeResidue
    ‖(((primePoleV hp4 g s).eval 0:ℤ_[p]):ℚ_[p]) -
      ((![8,-46/3,266/9] k:ℚ):ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  apply integralPolynomial_eval_zero_norm_of_rational
  · exact (primeHighShape_monomial_rational hp4 k 0).2
  · exact highShape_V_prime_values hp4 k

end
end Li2

end
