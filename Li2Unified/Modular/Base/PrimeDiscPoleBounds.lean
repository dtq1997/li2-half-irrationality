module
public import Li2Unified.Modular.Base.PrimeDiscUnits
public import Li2Unified.Modular.Base.PrimeBaseShapes
public import Li2Unified.Modular.Base.RestrictedPoleFunctionalError

set_option backward.privateInPublic true

@[expose] public section

/-! Actual local disc units acting on the existing bounded four-pole space.
The three base shapes are constructed before applying the unit; U/V errors
are bounded coefficientwise, not inferred from finite sample evaluations. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem primeDiscLowPole_cleared (hp4 : 3 < p) (a : ℕ) (ha : a < p) :
    integralPoleNumerator (primePoleCenters p)
      (integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a ha) 0
        (primeLowShapeResidue hp4))
      (integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a ha)
        (primeLowShapeResidue hp4)) = primeDiscUnit a ha*PowerSeries.X^3 := by
  rw [integralPoleNumerator_mul _ _ _ (primeDiscUnit_isRestricted a ha), primeLowShape_cleared]

theorem primeDiscHighPole_cleared (hp4 : 3 < p) (a : ℕ) (ha : a < p) :
    integralPoleNumerator (primePoleCenters p)
      (integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a ha) 1 primeHighShapeResidue)
      (integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a ha) primeHighShapeResidue) =
        primeDiscUnit a ha*(PowerSeries.X^3*(PowerSeries.X+PowerSeries.C 3)) := by
  rw [integralPoleNumerator_mul _ _ _ (primeDiscUnit_isRestricted a ha), primeHighShape_cleared]

theorem primeDiscZeroPole_cleared (hp4 : 3 < p) :
    integralPoleNumerator (primePoleCenters p)
      (integralPoleMulRegular (primePoleCenters p) (primeDiscUnit 0 hp.out.pos) 0
        (primeZeroShapeResidue hp4))
      (integralPoleMulResidue (primePoleCenters p) (primeDiscUnit 0 hp.out.pos)
        (primeZeroShapeResidue hp4)) = primeDiscUnit 0 hp.out.pos*PowerSeries.X := by
  rw [integralPoleNumerator_mul _ _ _ (primeDiscUnit_isRestricted 0 hp.out.pos), primeZeroShape_cleared]

end
end Li2

end
