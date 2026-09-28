module
public import Li2Unified.Modular.Base.PrimeMonomialLeading

set_option backward.privateInPublic true

@[expose] public section

/-! The low/high leading formulas retain the factor p needed to clear
U-a/p V. No matrix or unscaled numerator is identified here. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem primeDiscMonomial_low_scaled_leading (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (k : Fin 3) (eta : ℤ_[p]) (n : ℕ) :
    let U := (primePoleU hp4 (primeDiscMonomialRegular hp4 a k.val)
      (primeDiscMonomialResidue hp4 a k.val)).comp (C ((p:ℤ_[p])^2)*(X-C eta))
    let V := (primePoleV hp4 (primeDiscMonomialRegular hp4 a k.val)
      (primeDiscMonomialResidue hp4 a k.val)).comp (C ((p:ℤ_[p])^2)*(X-C eta))
    ‖(C (p:ℚ_[p])*U.map (algebraMap ℤ_[p] ℚ_[p]) -
      C (a.val:ℚ_[p])*V.map (algebraMap ℤ_[p] ℚ_[p]) -
      C (-(a.val:ℚ_[p])*((primeDiscUnitConstant a.val a.isLt:ℚ_[p]) *
        ((![95/4,-253/4,2093/12] k:ℚ):ℚ_[p])))).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  dsimp only
  apply integralPolynomial_prime_UV_leading _ _ (a.val:ℤ_[p])
  exact primeDiscMonomial_low_V_leading hp4 a ha0 ha k eta

theorem primeDiscMonomial_high_scaled_leading (hp4 : 3 < p) (a : Fin p)
    (ha : p-4 < a.val) (k : Fin 3) (eta : ℤ_[p]) (n : ℕ) :
    let U := (primePoleU hp4 (primeDiscMonomialRegular hp4 a k.val)
      (primeDiscMonomialResidue hp4 a k.val)).comp (C ((p:ℤ_[p])^2)*(X-C eta))
    let V := (primePoleV hp4 (primeDiscMonomialRegular hp4 a k.val)
      (primeDiscMonomialResidue hp4 a k.val)).comp (C ((p:ℤ_[p])^2)*(X-C eta))
    ‖(C (p:ℚ_[p])*U.map (algebraMap ℤ_[p] ℚ_[p]) -
      C (a.val:ℚ_[p])*V.map (algebraMap ℤ_[p] ℚ_[p]) -
      C (-(a.val:ℚ_[p])*((primeDiscUnitConstant a.val a.isLt:ℚ_[p]) *
        ((![8,-46/3,266/9] k:ℚ):ℚ_[p])))).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  dsimp only
  apply integralPolynomial_prime_UV_leading _ _ (a.val:ℤ_[p])
  exact primeDiscMonomial_high_V_leading hp4 a ha k eta

end
end Li2

end
