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

end
end Li2

end
