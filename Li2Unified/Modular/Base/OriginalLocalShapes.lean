module
public import Li2Unified.Modular.Base.OriginalIntegralComparison
public import Li2Unified.Modular.Base.PrimeDiscPoleBounds

set_option backward.privateInPublic true

@[expose] public section

/-! Unconditional compatibility for the actual R_(p-1) on all three residue
classes, with the exact factors p, 1 and p^3. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma fieldPrimePoleDenominator_explicit :
    (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) =
      PowerSeries.X*(PowerSeries.X+1)*(PowerSeries.X+PowerSeries.C 2)*
        (PowerSeries.X+PowerSeries.C 3) := by
  rw [← fieldPoleDenominator_map, primePoleDenominator_explicit]
  simp [PadicInt.algebraMap_apply,
    show ((2:ℤ_[p]):ℚ_[p]) = 2 from rfl,
    show ((3:ℤ_[p]):ℚ_[p]) = 3 from rfl]

theorem original_low_integral_cleared (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) :
    primeDiscPolynomialSeries a.val (4*(p-1)) *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
        (integralPoleNumerator (primePoleCenters p)
          (integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a.val a.isLt) 0
            (primeLowShapeResidue hp4))
          (integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a.val a.isLt)
            (primeLowShapeResidue hp4))) =
    PowerSeries.C (p:ℚ_[p]) * (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
      rationalPolynomialSeries (((D (p-1))^3).comp (C (p:ℚ)*X-C (a.val:ℚ))) := by
  rw [primeDiscLowPole_cleared, map_mul, map_pow, PowerSeries.map_X,
    fieldPrimePoleDenominator_explicit, pow_comp, map_pow]
  change _ = _ * _ * primeDiscPolynomialSeries a.val (p-1)^3
  have he := primeDiscShape_low_cleared hp4 a.val ha0 ha
  calc
    _ = PowerSeries.X * (primeDiscPolynomialSeries a.val (4*(p-1)) *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (primeDiscUnit a.val a.isLt) *
        PowerSeries.X^2) := by ring
    _ = _ := by rw [← he]; ring

theorem original_high_integral_cleared (hp4 : 3 < p) (a : Fin p)
    (ha : p-3 ≤ a.val) :
    primeDiscPolynomialSeries a.val (4*(p-1)) *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
        (integralPoleNumerator (primePoleCenters p)
          (integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a.val a.isLt) 1
            primeHighShapeResidue)
          (integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a.val a.isLt)
            primeHighShapeResidue)) =
    PowerSeries.C (1:ℚ_[p]) * (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
      rationalPolynomialSeries (((D (p-1))^3).comp (C (p:ℚ)*X-C (a.val:ℚ))) := by
  rw [primeDiscHighPole_cleared hp4 a.val a.isLt, map_mul, map_mul, map_pow, map_add,
    PowerSeries.map_X, PowerSeries.map_C,
    fieldPrimePoleDenominator_explicit, pow_comp, map_pow]
  simp only [map_one, one_mul, map_ofNat]
  change _ = _ * primeDiscPolynomialSeries a.val (p-1)^3
  have he := primeDiscShape_high_cleared hp4 a.val ha a.isLt
  calc
    _ = (PowerSeries.X*(PowerSeries.X+PowerSeries.C 3)) *
      (primeDiscPolynomialSeries a.val (4*(p-1)) *
        PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (primeDiscUnit a.val a.isLt) *
          PowerSeries.X^2) := by simp only [map_ofNat]; ring
    _ = _ := by rw [← he]; simp only [map_ofNat]; ring

theorem original_zero_integral_cleared (hp4 : 3 < p) :
    primeDiscPolynomialSeries 0 (4*(p-1)) *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
        (integralPoleNumerator (primePoleCenters p)
          (integralPoleMulRegular (primePoleCenters p) (primeDiscUnit 0 hp.out.pos) 0
            (primeZeroShapeResidue hp4))
          (integralPoleMulResidue (primePoleCenters p) (primeDiscUnit 0 hp.out.pos)
            (primeZeroShapeResidue hp4))) =
    PowerSeries.C ((p:ℚ_[p])^3) * (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
      rationalPolynomialSeries (((D (p-1))^3).comp (C (p:ℚ)*X-C (0:ℚ))) := by
  rw [primeDiscZeroPole_cleared hp4, map_mul, PowerSeries.map_X,
    fieldPrimePoleDenominator_explicit, pow_comp, map_pow]
  simp only [map_pow]
  change _ = _ * _ * primeDiscPolynomialSeries (p := p) 0 (p-1)^3
  have he := primeDiscShape_zero_cleared hp4
  simp only [map_pow] at he
  calc
    _ = PowerSeries.X * (primeDiscPolynomialSeries 0 (4*(p-1)) *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (primeDiscUnit 0 hp.out.pos)) := by ring
    _ = _ := by rw [← he]; ring

theorem numeratorPulledValue_low (hp4 : 3 < p) (Y : ℚ_[p]) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) :
    let g := integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a.val a.isLt) 0
      (primeLowShapeResidue hp4)
    let r := integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a.val a.isLt)
      (primeLowShapeResidue hp4)
    (p:ℚ_[p]) * numeratorPulledValue (by omega : p ≠ 2) (by omega : p ≠ 3)
      Y (4*(p-1)) ((D (p-1))^3) a =
      (primePoleU hp4 g r).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y - (a.val:ℚ_[p])/(p:ℚ_[p]) *
        (primePoleV hp4 g r).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y := by
  apply numeratorPulledValue_integral_of_cleared hp4 Y (4*(p-1)) (by omega)
  · exact integralPoleMulRegular_isRestricted _ _ _ (primeDiscUnit_isRestricted _ _)
      (PowerSeries.isRestricted_zero 1) _
  · exact original_low_integral_cleared hp4 a ha0 ha

theorem numeratorPulledValue_high (hp4 : 3 < p) (Y : ℚ_[p]) (a : Fin p)
    (ha : p-3 ≤ a.val) :
    let g := integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a.val a.isLt) 1
      primeHighShapeResidue
    let r := integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a.val a.isLt)
      primeHighShapeResidue
    numeratorPulledValue (by omega : p ≠ 2) (by omega : p ≠ 3)
      Y (4*(p-1)) ((D (p-1))^3) a =
      (primePoleU hp4 g r).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y - (a.val:ℚ_[p])/(p:ℚ_[p]) *
        (primePoleV hp4 g r).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y := by
  have h := numeratorPulledValue_integral_of_cleared hp4 Y (4*(p-1)) (by omega)
    ((D (p-1))^3) a 1 _
    (integralPoleMulRegular_isRestricted _ _ _ (primeDiscUnit_isRestricted _ _)
      (PowerSeries.isRestricted_one 1) _) _ (original_high_integral_cleared hp4 a ha)
  simpa only [one_mul] using h

theorem numeratorPulledValue_zero (hp4 : 3 < p) (Y : ℚ_[p]) :
    let g := integralPoleMulRegular (primePoleCenters p) (primeDiscUnit 0 hp.out.pos) 0
      (primeZeroShapeResidue hp4)
    let r := integralPoleMulResidue (primePoleCenters p) (primeDiscUnit 0 hp.out.pos)
      (primeZeroShapeResidue hp4)
    (p:ℚ_[p])^3 * numeratorPulledValue (by omega : p ≠ 2) (by omega : p ≠ 3)
      Y (4*(p-1)) ((D (p-1))^3) ⟨0,hp.out.pos⟩ =
      (primePoleU hp4 g r).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y := by
  have h := numeratorPulledValue_integral_of_cleared hp4 Y (4*(p-1)) (by omega)
    ((D (p-1))^3) ⟨0,hp.out.pos⟩ ((p:ℚ_[p])^3) _
    (integralPoleMulRegular_isRestricted _ _ _ (primeDiscUnit_isRestricted _ _)
      (PowerSeries.isRestricted_zero 1) _) _ (original_zero_integral_cleared hp4)
  simpa only [Nat.cast_zero, zero_div, zero_mul, sub_zero] using h

end
end Li2

end
