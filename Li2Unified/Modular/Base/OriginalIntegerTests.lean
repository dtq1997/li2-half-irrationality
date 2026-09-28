module
public import Li2Unified.Modular.Base.OriginalLocalShapes
public import Li2Unified.Modular.Base.PrimeOriginalBasis

set_option backward.privateInPublic true

@[expose] public section

/-! Integral test polynomials use their own coefficient map and affine pullback.
Multiplication is performed with the proved integral divided difference. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def integralDiscTestPolynomial (T : ℤ[X]) (a : Fin p) : (ℤ_[p])[X] :=
  (T.map (Int.castRingHom ℤ_[p])).comp (C (p:ℤ_[p])*X-C (a.val:ℤ_[p]))

lemma integralDiscTestPolynomial_map (T : ℤ[X]) (a : Fin p) :
    (integralDiscTestPolynomial T a).map (algebraMap ℤ_[p] ℚ_[p]) =
      ((T.map (Int.castRingHom ℚ)).comp (C (p:ℚ)*X-C (a.val:ℚ))).map (Rat.castHom ℚ_[p]) := by
  have h1 : (algebraMap ℤ_[p] ℚ_[p]).comp (Int.castRingHom ℤ_[p]) =
      Int.castRingHom ℚ_[p] := Subsingleton.elim _ _
  have h2 : (Rat.castHom ℚ_[p]).comp (Int.castRingHom ℚ) =
      Int.castRingHom ℚ_[p] := Subsingleton.elim _ _
  simp only [integralDiscTestPolynomial, Polynomial.map_comp, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, map_natCast,
    Polynomial.map_natCast, Rat.coe_castHom, Rat.cast_natCast, Polynomial.map_map, h1, h2]

lemma integralDiscTestSeries_map (T : ℤ[X]) (a : Fin p) :
    PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
      (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) =
      rationalPolynomialSeries ((T.map (Int.castRingHom ℚ)).comp (C (p:ℚ)*X-C (a.val:ℚ))) := by
  rw [← Polynomial.polynomial_map_coe, integralDiscTestPolynomial_map]
  rfl

theorem original_test_integral_cleared
    (m : ℕ) (F : ℚ[X]) (a : Fin p) (c : ℚ_[p])
    (g : PowerSeries ℤ_[p]) (r : Fin 4 → ℤ_[p])
    (he : primeDiscPolynomialSeries a.val m *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (integralPoleNumerator (primePoleCenters p) g r) =
      PowerSeries.C c * (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
        rationalPolynomialSeries (F.comp (C (p:ℚ)*X-C (a.val:ℚ)))) (T : ℤ[X]) :
    primeDiscPolynomialSeries a.val m *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
        (integralPoleNumerator (primePoleCenters p)
          (integralPoleMulRegular (primePoleCenters p)
            (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) g r)
          (integralPoleMulResidue (primePoleCenters p)
            (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) r)) =
    PowerSeries.C c * (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
      rationalPolynomialSeries ((F*T.map (Int.castRingHom ℚ)).comp
        (C (p:ℚ)*X-C (a.val:ℚ))) := by
  rw [integralPoleNumerator_mul _ _ _ (polynomial_isRestricted _), map_mul,
    integralDiscTestSeries_map, mul_comp, map_mul]
  calc
    _ = rationalPolynomialSeries ((T.map (Int.castRingHom ℚ)).comp (C (p:ℚ)*X-C (a.val:ℚ))) *
      (primeDiscPolynomialSeries a.val m * PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
        (integralPoleNumerator (primePoleCenters p) g r)) := by ring
    _ = _ := by rw [he]; ring

theorem numeratorPulledValue_integer_test (hp4 : 3 < p) (Y : ℚ_[p])
    (m : ℕ) (hm : m ≤ 4*p-4) (F : ℚ[X]) (a : Fin p) (c : ℚ_[p])
    (g : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g) (r : Fin 4 → ℤ_[p])
    (he : primeDiscPolynomialSeries a.val m *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (integralPoleNumerator (primePoleCenters p) g r) =
      PowerSeries.C c * (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
        rationalPolynomialSeries (F.comp (C (p:ℚ)*X-C (a.val:ℚ)))) (T : ℤ[X]) :
    let gT := integralPoleMulRegular (primePoleCenters p)
      (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) g r
    let rT := integralPoleMulResidue (primePoleCenters p)
      (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) r
    c * numeratorPulledValue (by omega : p ≠ 2) (by omega : p ≠ 3)
      Y m (F*T.map (Int.castRingHom ℚ)) a =
      (primePoleU hp4 gT rT).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y - (a.val:ℚ_[p])/(p:ℚ_[p]) *
        (primePoleV hp4 gT rT).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y := by
  apply numeratorPulledValue_integral_of_cleared hp4 Y m hm
  · exact integralPoleMulRegular_isRestricted _ _ _ (polynomial_isRestricted _) hg _
  · exact original_test_integral_cleared m F a c g r he T

end
end Li2

end
