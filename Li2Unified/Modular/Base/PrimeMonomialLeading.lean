module
public import Li2Unified.Modular.Base.PolynomialUVLeading
public import Li2Unified.Modular.Base.PrimeBaseValueBounds
public import Li2Unified.Modular.Base.PrimeLocalLeadingBounds
public import Li2Unified.Modular.Base.PrimeOriginalLocalBasis
public import Li2Unified.Modular.Base.RestrictedPoleMultiplierAlgebra

set_option backward.privateInPublic true

@[expose] public section

/-! Leading values of the actual disc unit times each needed base monomial,
after Y=p^2(X-eta). These are local formulas before basis-jet assembly. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def primeDiscMonomialRegular (hp4 : 3 < p) (a : Fin p) (k : ℕ) : PowerSeries ℤ_[p] :=
  integralPoleMulRegular (primePoleCenters p)
    (primeDiscUnit a.val a.isLt*((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p]))
    (primeDiscBaseRegular a) (primeDiscBaseResidue hp4 a)

def primeDiscMonomialResidue (hp4 : 3 < p) (a : Fin p) (k : ℕ) : Fin 4 → ℤ_[p] :=
  integralPoleMulResidue (primePoleCenters p)
    (primeDiscUnit a.val a.isLt*((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p]))
    (primeDiscBaseResidue hp4 a)

lemma primeDiscBaseRegular_isRestricted (a : Fin p) :
    PowerSeries.IsRestricted 1 (primeDiscBaseRegular a) := by
  unfold primeDiscBaseRegular
  split_ifs
  · exact PowerSeries.isRestricted_zero 1
  · exact PowerSeries.isRestricted_zero 1
  · exact PowerSeries.isRestricted_one 1

lemma primeDiscMonomial_nested (hp4 : 3 < p) (a : Fin p) (k : ℕ) :
    primeDiscMonomialRegular hp4 a k =
      integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a.val a.isLt)
        (integralPoleMulRegular (primePoleCenters p)
          ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p])
          (primeDiscBaseRegular a) (primeDiscBaseResidue hp4 a))
        (integralPoleMulResidue (primePoleCenters p)
          ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) (primeDiscBaseResidue hp4 a)) ∧
    primeDiscMonomialResidue hp4 a k =
      integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a.val a.isLt)
        (integralPoleMulResidue (primePoleCenters p)
          ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) (primeDiscBaseResidue hp4 a)) := by
  have h := integralPoleMultiplier_assoc (primePoleCenters p) primePoleCenters_injective
    (primeDiscUnit a.val a.isLt) ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p])
    (primeDiscBaseRegular a) (primeDiscUnit_isRestricted a.val a.isLt)
    (polynomial_isRestricted _) (primeDiscBaseRegular_isRestricted a) (primeDiscBaseResidue hp4 a)
  exact ⟨h.1.symm,h.2.symm⟩

theorem primeDiscMonomial_zero_U_leading (hp4 : 3 < p) (k : Fin 5)
    (eta : ℤ_[p]) (n : ℕ) :
    let a : Fin p := ⟨0,by omega⟩
    ‖(((primePoleU hp4 (primeDiscMonomialRegular hp4 a k.val)
        (primeDiscMonomialResidue hp4 a k.val)).comp
        (C ((p:ℤ_[p])^2)*(X-C eta))).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((primeDiscUnitConstant (p := p) 0 (by omega):ℚ_[p]) *
        ((![-113/12,95/4,-253/4,2093/12,-17773/36] k:ℚ):ℚ_[p]))).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  dsimp only
  rw [(primeDiscMonomial_nested hp4 ⟨0,by omega⟩ k.val).1,
    (primeDiscMonomial_nested hp4 ⟨0,by omega⟩ k.val).2]
  simp only [primeDiscBaseRegular, primeDiscBaseResidue, if_pos rfl]
  apply primeDiscPole_U_substituted_rational
  · exact integralPoleMulRegular_isRestricted _ _ _ (polynomial_isRestricted _)
      (PowerSeries.isRestricted_zero 1) _
  · exact primeZeroShape_U_value_norm hp4 k

theorem primeDiscMonomial_low_V_leading (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (k : Fin 3) (eta : ℤ_[p]) (n : ℕ) :
    ‖(((primePoleV hp4 (primeDiscMonomialRegular hp4 a k.val)
        (primeDiscMonomialResidue hp4 a k.val)).comp
        (C ((p:ℤ_[p])^2)*(X-C eta))).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((primeDiscUnitConstant a.val a.isLt:ℚ_[p]) *
        ((![95/4,-253/4,2093/12] k:ℚ):ℚ_[p]))).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  rw [(primeDiscMonomial_nested hp4 a k.val).1, (primeDiscMonomial_nested hp4 a k.val).2]
  simp only [primeDiscBaseRegular, primeDiscBaseResidue, if_neg (by omega : a.val ≠ 0), if_pos ha]
  apply primeDiscPole_V_substituted_rational
  · exact integralPoleMulRegular_isRestricted _ _ _ (polynomial_isRestricted _)
      (PowerSeries.isRestricted_zero 1) _
  · exact primeLowShape_V_value_norm hp4 k

theorem primeDiscMonomial_high_V_leading (hp4 : 3 < p) (a : Fin p)
    (ha : p-4 < a.val) (k : Fin 3) (eta : ℤ_[p]) (n : ℕ) :
    ‖(((primePoleV hp4 (primeDiscMonomialRegular hp4 a k.val)
        (primeDiscMonomialResidue hp4 a k.val)).comp
        (C ((p:ℤ_[p])^2)*(X-C eta))).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((primeDiscUnitConstant a.val a.isLt:ℚ_[p]) *
        ((![8,-46/3,266/9] k:ℚ):ℚ_[p]))).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  rw [(primeDiscMonomial_nested hp4 a k.val).1, (primeDiscMonomial_nested hp4 a k.val).2]
  simp only [primeDiscBaseRegular, primeDiscBaseResidue, if_neg (by omega : a.val ≠ 0),
    if_neg (by omega : ¬a.val ≤ p-4)]
  apply primeDiscPole_V_substituted_rational
  · exact integralPoleMulRegular_isRestricted _ _ _ (polynomial_isRestricted _)
      (PowerSeries.isRestricted_one 1) _
  · exact primeHighShape_V_value_norm hp4 k

end
end Li2

end
