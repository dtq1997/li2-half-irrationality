module
public import Li2Unified.Modular.Base.FieldRestrictedPoles
public import Li2Unified.Modular.Base.RestrictedPoleBounds

set_option backward.privateInPublic true

@[expose] public section

/-! The Q_p pole representation and functional preserve the original integral
representation under the canonical inclusion. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fieldPoleDenominator_map (c : ι → ℤ_[p]) :
    (integralPoleDenominator c).map (algebraMap ℤ_[p] ℚ_[p]) = fieldPoleDenominator c := by
  simp [integralPoleDenominator, fieldPoleDenominator, Polynomial.map_prod, PadicInt.algebraMap_apply]

lemma fieldPoleCofactor_map (c : ι → ℤ_[p]) (i : ι) :
    (integralPoleCofactor c i).map (algebraMap ℤ_[p] ℚ_[p]) = fieldPoleCofactor c i := by
  simp [integralPoleCofactor, fieldPoleCofactor, Polynomial.map_prod, PadicInt.algebraMap_apply]

theorem fieldPoleNumerator_integral (c : ι → ℤ_[p])
    (f : PowerSeries ℤ_[p]) (r : ι → ℤ_[p]) :
    fieldPoleNumerator c (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) f)
      (fun i => (r i:ℚ_[p])) =
    PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (integralPoleNumerator c f r) := by
  unfold fieldPoleNumerator integralPoleNumerator
  simp only [map_add, map_mul, ← Polynomial.polynomial_map_coe, Polynomial.map_sum,
    Polynomial.map_mul, map_C, fieldPoleDenominator_map, fieldPoleCofactor_map, PadicInt.algebraMap_apply]

theorem fieldPoleNumerator_add (c : ι → ℤ_[p]) (f g : PowerSeries ℚ_[p])
    (r s : ι → ℚ_[p]) :
    fieldPoleNumerator c (f+g) (r+s) = fieldPoleNumerator c f r + fieldPoleNumerator c g s := by
  simp only [fieldPoleNumerator, Pi.add_apply, map_add, add_mul,
    Finset.sum_add_distrib, Polynomial.coe_add]
  ring

theorem fieldPoleNumerator_smul (c : ι → ℤ_[p]) (f : PowerSeries ℚ_[p])
    (r : ι → ℚ_[p]) (a : ℚ_[p]) :
    fieldPoleNumerator c (a • f) (fun i => a*r i) =
      PowerSeries.C a * fieldPoleNumerator c f r := by
  simp only [fieldPoleNumerator, map_mul, mul_assoc, ← Finset.mul_sum,
    Polynomial.coe_mul, Polynomial.coe_C]
  rw [Algebra.smul_def]
  change _ * (PowerSeries.C a * f) + _ = _
  ring

def fieldPoleFunctional (μ : ℕ → ℤ_[p]) (w : ι → (ℚ_[p])[X])
    (f : PowerSeries ℚ_[p]) (r : ι → ℚ_[p]) : (ℚ_[p])[X] :=
  C (fieldRestrictedMoment μ f) + ∑ i, C (r i)*w i

theorem fieldPoleFunctional_integral (μ : ℕ → ℤ_[p]) (w : ι → (ℤ_[p])[X])
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f) (r : ι → ℤ_[p]) :
    fieldPoleFunctional μ (fun i => (w i).map (algebraMap ℤ_[p] ℚ_[p]))
      (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) f) (fun i => (r i:ℚ_[p])) =
      (restrictedPoleFunctional μ w f r).map (algebraMap ℤ_[p] ℚ_[p]) := by
  simp [fieldPoleFunctional, restrictedPoleFunctional, fieldRestrictedMoment_integral μ f hf, Polynomial.map_sum, PadicInt.algebraMap_apply]

theorem fieldPoleFunctional_add (μ : ℕ → ℤ_[p]) (w : ι → (ℚ_[p])[X])
    (f g : PowerSeries ℚ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (hg : PowerSeries.IsRestricted 1 g) (r s : ι → ℚ_[p]) :
    fieldPoleFunctional μ w (f+g) (r+s) =
      fieldPoleFunctional μ w f r + fieldPoleFunctional μ w g s := by
  simp only [fieldPoleFunctional, fieldRestrictedMoment_add μ f g hf hg, map_add,
    Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem fieldPoleFunctional_smul (μ : ℕ → ℤ_[p]) (w : ι → (ℚ_[p])[X])
    (f : PowerSeries ℚ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (r : ι → ℚ_[p]) (a : ℚ_[p]) :
    fieldPoleFunctional μ w (a • f) (fun i => a*r i) = C a*fieldPoleFunctional μ w f r := by
  simp only [fieldPoleFunctional, fieldRestrictedMoment_smul μ f hf a, map_mul,
    mul_add, Finset.mul_sum, mul_assoc]

end
end Li2

end
