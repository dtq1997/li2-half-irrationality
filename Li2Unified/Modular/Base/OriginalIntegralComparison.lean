module
public import Li2Unified.Modular.Base.RestrictedSeriesCompat
public import Li2Unified.Modular.Base.OriginalNumeratorClearing

set_option backward.privateInPublic true

@[expose] public section

/-! Transfer a proved cleared identity to the original pulled functional.
The comparison representation must be independently constructed and restricted. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem originalPulled_eq_integral_of_cleared
    (m : ℕ) (hm : m ≤ 4*p-4) (F : ℚ[X]) (a : Fin p) (c : ℚ_[p])
    (g : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g) (r : Fin 4 → ℤ_[p])
    (he : primeDiscPolynomialSeries a.val m *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (integralPoleNumerator (primePoleCenters p) g r) =
      PowerSeries.C c * (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
        rationalPolynomialSeries (F.comp (C (p:ℚ)*X-C (a.val:ℚ)))) :
    c • originalPulledRegular m F a = PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) g ∧
    (fun i => c*originalPulledResidue m hm F a i) = (fun i => (r i : ℚ_[p])) := by
  apply fieldPoleNumerator_injective (primePoleCenters p) primePoleCenters_injective
    _ _ (Li2.restrictedSeries_smul 1 (originalPulledRegular_isRestricted m F a) c)
    (field_map_isRestricted g hg)
  rw [fieldPoleNumerator_smul, fieldPoleNumerator_integral]
  apply mul_left_cancel₀ (primeDiscPolynomialSeries_ne_zero (p := p) a.val m)
  rw [he]
  calc
    _ = PowerSeries.C c * (primeDiscPolynomialSeries a.val m *
      fieldPoleNumerator (primePoleCenters p) (originalPulledRegular m F a)
        (originalPulledResidue m hm F a)) := by ring
    _ = _ := by rw [originalPulled_cleared]; ring

theorem numeratorPulledValue_integral_of_cleared (hp4 : 3 < p) (Y : ℚ_[p])
    (m : ℕ) (hm : m ≤ 4*p-4) (F : ℚ[X]) (a : Fin p) (c : ℚ_[p])
    (g : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g) (r : Fin 4 → ℤ_[p])
    (he : primeDiscPolynomialSeries a.val m *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (integralPoleNumerator (primePoleCenters p) g r) =
      PowerSeries.C c * (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
        rationalPolynomialSeries (F.comp (C (p:ℚ)*X-C (a.val:ℚ)))) :
    c * numeratorPulledValue (by omega : p ≠ 2) (by omega : p ≠ 3) Y m F a =
      (primePoleU hp4 g r).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y - (a.val:ℚ_[p])/(p:ℚ_[p]) *
        (primePoleV hp4 g r).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y := by
  obtain ⟨hgEq,hrEq⟩ := originalPulled_eq_integral_of_cleared m hm F a c g hg r he
  have hu : C c * fieldPrimePoleU hp4 (originalPulledRegular m F a)
      (originalPulledResidue m hm F a) =
      (primePoleU hp4 g r).map (algebraMap ℤ_[p] ℚ_[p]) := by
    change C c * fieldPoleFunctional _ _ _ _ = _
    rw [← fieldPoleFunctional_smul _ _ _ (originalPulledRegular_isRestricted m F a) _ c,
      hgEq, hrEq]
    exact fieldPrimePoleU_integral hp4 g hg r
  have hv : C c * fieldPrimePoleV hp4 (originalPulledRegular m F a)
      (originalPulledResidue m hm F a) =
      (primePoleV hp4 g r).map (algebraMap ℤ_[p] ℚ_[p]) := by
    change C c * fieldPoleFunctional _ _ _ _ = _
    rw [← fieldPoleFunctional_smul _ _ _ (originalPulledRegular_isRestricted m F a) _ c,
      hgEq, hrEq]
    exact fieldPrimePoleV_integral hp4 g hg r
  have hu' := congrArg (fun P : (ℚ_[p])[X] => P.eval Y) hu
  have hv' := congrArg (fun P : (ℚ_[p])[X] => P.eval Y) hv
  simp only [eval_mul, eval_C, eval_map] at hu' hv'
  rw [numeratorPulledValue_field hp4 Y m hm F a, mul_sub, hu']
  rw [← hv']
  ring

end
end Li2

end
