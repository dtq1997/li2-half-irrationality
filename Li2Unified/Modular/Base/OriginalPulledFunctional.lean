module
public import Li2Unified.Modular.Base.OriginalPulledRepresentation
public import Li2Unified.Modular.Base.PrimeFieldPoleExtension

set_option backward.privateInPublic true

@[expose] public section

/-! Identify the actual pulled simple-pole contributions with the field-valued
four-pole extension. This uses the original residue construction, not the desired
local R shape. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem original_pulled_polynomial_UV (hp4 : 3 < p) (m : ℕ) (F : ℚ[X])
    (a : Fin p) (Y : ℚ_[p]) :
    (fieldPrimePoleU hp4
      (rationalPolynomialSeries ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ)))) 0).eval Y -
      (a.val:ℚ_[p])/(p:ℚ_[p])*(fieldPrimePoleV hp4
        (rationalPolynomialSeries ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ)))) 0).eval Y =
    (parameterU (primeParameter p) ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ))):ℚ_[p]) -
      (a.val:ℚ_[p])/(p:ℚ_[p])*
        (parameterV (primeParameter p) ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ))):ℚ_[p]) := by
  change (fieldPrimePoleU hp4
      (((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ))).map (Rat.castHom ℚ_[p]) :
        PowerSeries ℚ_[p]) 0).eval Y - (a.val:ℚ_[p])/(p:ℚ_[p])*
      (fieldPrimePoleV hp4
        (((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ))).map (Rat.castHom ℚ_[p]) :
          PowerSeries ℚ_[p]) 0).eval Y = _
  rw [fieldPrimePoleU_polynomial, fieldPrimePoleV_polynomial]

theorem original_pulled_simplePole_UV (hp4 : 3 < p) (Y : ℚ_[p])
    (j a : ℕ) (hj : j ≤ 4*p-4) (ha : a < p) :
    pulledSimplePoleContribution (by omega : p ≠ 2) (by omega : p ≠ 3) Y j a =
      (fieldPrimePoleU hp4 (pulledPoleRegular j a) (pulledPoleResidue j a hj ha)).eval Y -
        (a:ℚ_[p])/(p:ℚ_[p])*
          (fieldPrimePoleV hp4 (pulledPoleRegular j a) (pulledPoleResidue j a hj ha)).eval Y := by
  unfold pulledSimplePoleContribution pulledPoleRegular pulledPoleResidue
  dsimp only
  by_cases hm : p ∣ j+(p-1-a)+1
  · simp only [dif_pos hm]
    rw [fieldPrimePoleU_single, fieldPrimePoleV_single]
    simp only [eval_mul, eval_C, eval_map]
    rw [primeUPole_eval₂, primeVPole_eval₂]
    dsimp only [primeMatchingPoleIndex]
    ring
  · simp only [dif_neg hm]
    rw [fieldPrimePoleU_regular, fieldPrimePoleV_regular, eval_C, eval_C,
      fieldRestrictedU_integral _ _ (padicReciprocalSeries_isRestricted _ _ _ _),
      fieldRestrictedV_integral _ _ (padicReciprocalSeries_isRestricted _ _ _ _)]

end
end Li2

end
