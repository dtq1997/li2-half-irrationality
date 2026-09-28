module
public import Li2Unified.Modular.Base.RestrictedPoleMultiplication
public import Li2Unified.Modular.Base.RestrictedDifferential

set_option backward.privateInPublic true

@[expose] public section

/-! Coefficient bounds for multiplication and for the finite-pole extension.
The parameter in a pole value may be any integral polynomial. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem restricted_mul_coeff_bound (g f : PowerSeries ℤ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B) (n : ℕ) :
    ‖PowerSeries.coeff n (g*f)‖ ≤ B := by
  rw [PowerSeries.coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB
  intro ij _
  rw [mul_comm]
  exact (integral_coeff_mul_norm_le _ _).trans (hf ij.2)

theorem integralPoleMulRegular_coeff_bound (c : ι → ℤ_[p])
    (g f : PowerSeries ℤ_[p]) (r : ι → ℤ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B) (hr : ∀ i, ‖r i‖ ≤ B) (n : ℕ) :
    ‖PowerSeries.coeff n (integralPoleMulRegular c g f r)‖ ≤ B := by
  unfold integralPoleMulRegular
  rw [map_add, map_sum]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · exact restricted_mul_coeff_bound g f B hB hf n
  · apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB
    intro i _
    rw [PowerSeries.coeff_C_mul]
    exact (integral_coeff_mul_norm_le _ _).trans (hr i)

theorem integralPoleMulResidue_bound (c : ι → ℤ_[p])
    (g : PowerSeries ℤ_[p]) (r : ι → ℤ_[p]) (B : ℝ)
    (hr : ∀ i, ‖r i‖ ≤ B) (i : ι) :
    ‖integralPoleMulResidue c g r i‖ ≤ B :=
  (integral_coeff_mul_norm_le _ _).trans (hr i)

def restrictedPoleFunctional (μ : ℕ → ℤ_[p]) (w : ι → (ℤ_[p])[X])
    (f : PowerSeries ℤ_[p]) (r : ι → ℤ_[p]) : (ℤ_[p])[X] :=
  C (restrictedMoment μ f) + ∑ i, C (r i)*w i

theorem restrictedPoleFunctional_coeff_bound (μ : ℕ → ℤ_[p]) (w : ι → (ℤ_[p])[X])
    (f : PowerSeries ℤ_[p]) (r : ι → ℤ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B) (hr : ∀ i, ‖r i‖ ≤ B) (n : ℕ) :
    ‖(restrictedPoleFunctional μ w f r).coeff n‖ ≤ B := by
  unfold restrictedPoleFunctional
  rw [coeff_add, finset_sum_coeff]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · by_cases hn : n = 0
    · subst n
      rw [coeff_C_zero]
      exact restrictedMoment_norm_le μ f B hf
    · simpa [coeff_C, hn] using hB
  · apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB
    intro i _
    rw [coeff_C_mul]
    exact (integral_coeff_mul_norm_le _ _).trans (hr i)

theorem restrictedPoleFunctional_add (μ : ℕ → ℤ_[p]) (w : ι → (ℤ_[p])[X])
    (f g : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (hg : PowerSeries.IsRestricted 1 g) (r s : ι → ℤ_[p]) :
    restrictedPoleFunctional μ w (f+g) (r+s) =
      restrictedPoleFunctional μ w f r + restrictedPoleFunctional μ w g s := by
  unfold restrictedPoleFunctional
  rw [restrictedMoment_add μ f g hf hg, map_add]
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  ring

theorem restrictedPoleFunctional_smul (μ : ℕ → ℤ_[p]) (w : ι → (ℤ_[p])[X])
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f) (r : ι → ℤ_[p]) (a : ℤ_[p]) :
    restrictedPoleFunctional μ w (a • f) (a • r) = C a*restrictedPoleFunctional μ w f r := by
  unfold restrictedPoleFunctional
  rw [restrictedMoment_smul μ f hf a, map_mul, mul_add, Finset.mul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

end
end Li2

end
