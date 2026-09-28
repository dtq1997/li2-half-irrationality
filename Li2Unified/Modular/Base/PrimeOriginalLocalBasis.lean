module
public import Li2Unified.Modular.Base.OriginalIntegerTests

set_option backward.privateInPublic true

@[expose] public section

/-! Uniform local formula for every entry of the actual 2(p-1) product basis.
The three cases keep the original p^3, p and 1 factors. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def primeDiscScale (a : Fin p) : ℚ_[p] :=
  if a.val = 0 then (p:ℚ_[p])^3 else if a.val ≤ p-4 then p else 1

def primeDiscBaseRegular (a : Fin p) : PowerSeries ℤ_[p] :=
  if a.val = 0 then 0 else if a.val ≤ p-4 then 0 else 1

def primeDiscBaseResidue (hp4 : 3 < p) (a : Fin p) : Fin 4 → ℤ_[p] :=
  if a.val = 0 then primeZeroShapeResidue hp4
  else if a.val ≤ p-4 then primeLowShapeResidue hp4 else primeHighShapeResidue

def primeDiscRegular (hp4 : 3 < p) (a : Fin p) : PowerSeries ℤ_[p] :=
  integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a.val a.isLt)
    (primeDiscBaseRegular a) (primeDiscBaseResidue hp4 a)

def primeDiscResidue (hp4 : 3 < p) (a : Fin p) : Fin 4 → ℤ_[p] :=
  integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a.val a.isLt)
    (primeDiscBaseResidue hp4 a)

lemma primeDiscRegular_isRestricted (hp4 : 3 < p) (a : Fin p) :
    PowerSeries.IsRestricted 1 (primeDiscRegular hp4 a) := by
  apply integralPoleMulRegular_isRestricted _ _ _ (primeDiscUnit_isRestricted _ _)
  unfold primeDiscBaseRegular
  split_ifs
  · exact PowerSeries.isRestricted_zero 1
  · exact PowerSeries.isRestricted_zero 1
  · exact PowerSeries.isRestricted_one 1

theorem original_disc_integral_cleared (hp4 : 3 < p) (a : Fin p) :
    primeDiscPolynomialSeries a.val (4*(p-1)) *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
        (integralPoleNumerator (primePoleCenters p) (primeDiscRegular hp4 a) (primeDiscResidue hp4 a)) =
    PowerSeries.C (primeDiscScale a) * (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
      rationalPolynomialSeries (((D (p-1))^3).comp (C (p:ℚ)*X-C (a.val:ℚ))) := by
  by_cases hz : a.val = 0
  · have ha : a = ⟨0,hp.out.pos⟩ := Fin.ext hz
    subst a
    simpa only [primeDiscRegular, primeDiscResidue, primeDiscBaseRegular, primeDiscBaseResidue,
      primeDiscScale, if_pos rfl, ite_true, Nat.cast_zero] using! original_zero_integral_cleared hp4
  · by_cases hl : a.val ≤ p-4
    · simpa only [primeDiscRegular, primeDiscResidue, primeDiscBaseRegular, primeDiscBaseResidue,
        primeDiscScale, if_neg hz, if_pos hl] using original_low_integral_cleared hp4 a (by omega) hl
    · simpa only [primeDiscRegular, primeDiscResidue, primeDiscBaseRegular, primeDiscBaseResidue,
        primeDiscScale, if_neg hz, if_neg hl] using original_high_integral_cleared hp4 a (by omega)

def primeDiscTestRegular (hp4 : 3 < p) (a : Fin p) (T : ℤ[X]) : PowerSeries ℤ_[p] :=
  integralPoleMulRegular (primePoleCenters p) (integralDiscTestPolynomial T a : PowerSeries ℤ_[p])
    (primeDiscRegular hp4 a) (primeDiscResidue hp4 a)

def primeDiscTestResidue (hp4 : 3 < p) (a : Fin p) (T : ℤ[X]) : Fin 4 → ℤ_[p] :=
  integralPoleMulResidue (primePoleCenters p) (integralDiscTestPolynomial T a : PowerSeries ℤ_[p])
    (primeDiscResidue hp4 a)

end
end Li2

end
