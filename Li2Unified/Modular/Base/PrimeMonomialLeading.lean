module
public import Li2Unified.Modular.Base.PolynomialUVLeading
public import Li2Unified.Modular.Base.RationalPoleClearing
public import Li2Unified.Modular.Base.RationalBaseCongruence
public import Li2Unified.Modular.Base.PrimeNormReduction
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

end
end Li2

end
