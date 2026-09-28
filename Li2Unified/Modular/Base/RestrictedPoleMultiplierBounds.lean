module
public import Li2Unified.Modular.Base.RestrictedPoleBounds

set_option backward.privateInPublic true

@[expose] public section

/-! A small restricted multiplier gives a small regular correction and small
residues. This is the bound needed for the local unit minus its constant. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integralPoleMulRegular_bound_left (c : ι → ℤ_[p])
    (g f : PowerSeries ℤ_[p]) (r : ι → ℤ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) :
    ‖PowerSeries.coeff n (integralPoleMulRegular c g f r)‖ ≤ B := by
  unfold integralPoleMulRegular
  rw [map_add, map_sum]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · rw [mul_comm g f]
    exact restricted_mul_coeff_bound f g B hB hg n
  · apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB
    intro i _
    rw [PowerSeries.coeff_C_mul, mul_comm]
    exact (integral_coeff_mul_norm_le _ _).trans
      (restrictedDivDiff_coeff_bound (c i) g n B (fun k => hg _))

theorem integralPoleMulResidue_bound_left (c : ι → ℤ_[p])
    (g : PowerSeries ℤ_[p]) (r : ι → ℤ_[p]) (B : ℝ)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (i : ι) :
    ‖integralPoleMulResidue c g r i‖ ≤ B := by
  unfold integralPoleMulResidue
  rw [mul_comm]
  exact (integral_coeff_mul_norm_le _ _).trans (restrictedMoment_norm_le _ g B hg)

theorem integralPoleNumerator_add (c : ι → ℤ_[p])
    (f g : PowerSeries ℤ_[p]) (r s : ι → ℤ_[p]) :
    integralPoleNumerator c (f+g) (r+s) =
      integralPoleNumerator c f r + integralPoleNumerator c g s := by
  unfold integralPoleNumerator
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib,
    Polynomial.coe_add, mul_add]
  ring

theorem integralPoleNumerator_smul (c : ι → ℤ_[p])
    (f : PowerSeries ℤ_[p]) (r : ι → ℤ_[p]) (a : ℤ_[p]) :
    integralPoleNumerator c (a • f) (a • r) =
      PowerSeries.C a * integralPoleNumerator c f r := by
  unfold integralPoleNumerator
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc,
    polynomial_coe_finset_sum, Polynomial.coe_mul, Polynomial.coe_C,
    Finset.mul_sum, mul_add, PowerSeries.smul_eq_C_mul]
  ring

end
end Li2

end
