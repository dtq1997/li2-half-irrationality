module
public import Li2Unified.Modular.Base.RestrictedSeriesCompat
public import Li2Unified.Modular.Base.RestrictedPoleMultiplierBounds

set_option backward.privateInPublic true

@[expose] public section

/-! Exact decomposition of multiplication by g into its chosen constant and
a coefficientwise small error, in the existing simple-pole representation. -/
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integralPoleMultiplier_decomposition (c : ι → ℤ_[p])
    (hc : Function.Injective c) (g f : PowerSeries ℤ_[p])
    (hg : PowerSeries.IsRestricted 1 g) (hf : PowerSeries.IsRestricted 1 f)
    (r : ι → ℤ_[p]) (k : ℤ_[p]) :
    integralPoleMulRegular c g f r = k • f +
      integralPoleMulRegular c (g-PowerSeries.C k) f r ∧
    integralPoleMulResidue c g r = k • r +
      integralPoleMulResidue c (g-PowerSeries.C k) r := by
  have he : PowerSeries.IsRestricted 1 (g-PowerSeries.C k) := by
    rw [sub_eq_add_neg]
    exact PowerSeries.isRestricted.add 1 hg
      (PowerSeries.isRestricted.neg 1 (PowerSeries.isRestricted_C 1 k))
  apply integralPoleNumerator_injective c hc _ _
    (integralPoleMulRegular_isRestricted c g f hg hf r)
    (PowerSeries.isRestricted.add 1 (Li2.restrictedSeries_smul 1 hf k)
      (integralPoleMulRegular_isRestricted c _ f he hf r))
  rw [integralPoleNumerator_mul c g f hg r, integralPoleNumerator_add,
    integralPoleNumerator_smul, integralPoleNumerator_mul c _ f he r]
  ring

end
end Li2

end
