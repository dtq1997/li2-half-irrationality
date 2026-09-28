module
public import Li2Unified.Modular.Base.RestrictedSeriesCompat
public import Li2Unified.Modular.Base.RestrictedPoleMultiplierError

set_option backward.privateInPublic true

@[expose] public section

/-! A coefficient error in a restricted multiplier survives the entire
finite-pole functional, including its divided-difference regular correction. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem restrictedPoleFunctional_multiplier_error (c : ι → ℤ_[p])
    (hc : Function.Injective c) (μ : ℕ → ℤ_[p]) (w : ι → (ℤ_[p])[X])
    (g f : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g)
    (hf : PowerSeries.IsRestricted 1 f) (r : ι → ℤ_[p]) (k : ℤ_[p])
    (B : ℝ) (hB : 0 ≤ B)
    (he : ∀ n, ‖PowerSeries.coeff n (g-PowerSeries.C k)‖ ≤ B) (n : ℕ) :
    ‖(restrictedPoleFunctional μ w
        (integralPoleMulRegular c g f r) (integralPoleMulResidue c g r) -
      C k*restrictedPoleFunctional μ w f r).coeff n‖ ≤ B := by
  have hsmall : PowerSeries.IsRestricted 1 (g-PowerSeries.C k) := by
    rw [sub_eq_add_neg]
    exact PowerSeries.isRestricted.add 1 hg
      (PowerSeries.isRestricted.neg 1 (PowerSeries.isRestricted_C 1 k))
  obtain ⟨hreg,hres⟩ := integralPoleMultiplier_decomposition c hc g f hg hf r k
  rw [hreg, hres, restrictedPoleFunctional_add μ w _ _
    (Li2.restrictedSeries_smul 1 hf k)
    (integralPoleMulRegular_isRestricted c _ f hsmall hf r),
    restrictedPoleFunctional_smul μ w f hf r k, add_sub_cancel_left]
  exact restrictedPoleFunctional_coeff_bound μ w _ _ B hB
    (integralPoleMulRegular_bound_left c _ f r B hB he)
    (integralPoleMulResidue_bound_left c _ r B he) n

end
end Li2

end
