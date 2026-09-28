module
public import Li2Unified.Modular.Base.RestrictedPoleFunctionalError

set_option backward.privateInPublic true

@[expose] public section

/-! Associativity and additivity of multiplication in the independently
constructed restricted simple-pole presentation. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integralPoleMultiplier_assoc (c : ι → ℤ_[p]) (hc : Function.Injective c)
    (g h f : PowerSeries ℤ_[p])
    (hg : PowerSeries.IsRestricted 1 g) (hh : PowerSeries.IsRestricted 1 h)
    (hf : PowerSeries.IsRestricted 1 f) (r : ι → ℤ_[p]) :
    integralPoleMulRegular c g (integralPoleMulRegular c h f r)
      (integralPoleMulResidue c h r) = integralPoleMulRegular c (g*h) f r ∧
    integralPoleMulResidue c g (integralPoleMulResidue c h r) =
      integralPoleMulResidue c (g*h) r := by
  apply integralPoleNumerator_injective c hc _ _
    (integralPoleMulRegular_isRestricted c g _ hg
      (integralPoleMulRegular_isRestricted c h f hh hf r) _)
    (integralPoleMulRegular_isRestricted c (g*h) f
      (PowerSeries.IsRestricted.mul 1 hg hh) hf r)
  rw [integralPoleNumerator_mul c g _ hg,
    integralPoleNumerator_mul c h f hh,
    integralPoleNumerator_mul c (g*h) f (PowerSeries.IsRestricted.mul 1 hg hh)]
  exact (mul_assoc _ _ _).symm

theorem integralPoleMultiplier_add (c : ι → ℤ_[p]) (hc : Function.Injective c)
    (g h f : PowerSeries ℤ_[p])
    (hg : PowerSeries.IsRestricted 1 g) (hh : PowerSeries.IsRestricted 1 h)
    (hf : PowerSeries.IsRestricted 1 f) (r : ι → ℤ_[p]) :
    integralPoleMulRegular c (g+h) f r =
      integralPoleMulRegular c g f r + integralPoleMulRegular c h f r ∧
    integralPoleMulResidue c (g+h) r =
      integralPoleMulResidue c g r + integralPoleMulResidue c h r := by
  apply integralPoleNumerator_injective c hc _ _
    (integralPoleMulRegular_isRestricted c (g+h) f
      (PowerSeries.IsRestricted.add 1 hg hh) hf r)
    (PowerSeries.IsRestricted.add 1
      (integralPoleMulRegular_isRestricted c g f hg hf r)
      (integralPoleMulRegular_isRestricted c h f hh hf r))
  rw [integralPoleNumerator_mul c (g+h) f (PowerSeries.IsRestricted.add 1 hg hh),
    integralPoleNumerator_add, integralPoleNumerator_mul c g f hg,
    integralPoleNumerator_mul c h f hh, add_mul]

theorem integralPoleMultiplier_smul (c : ι → ℤ_[p]) (hc : Function.Injective c)
    (g f : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g)
    (hf : PowerSeries.IsRestricted 1 f) (r : ι → ℤ_[p]) (k : ℤ_[p]) :
    integralPoleMulRegular c (k • g) f r = k • integralPoleMulRegular c g f r ∧
    integralPoleMulResidue c (k • g) r = k • integralPoleMulResidue c g r := by
  apply integralPoleNumerator_injective c hc _ _
    (integralPoleMulRegular_isRestricted c (k • g) f
      (PowerSeries.IsRestricted.smul 1 hg k) hf r)
    (PowerSeries.IsRestricted.smul 1
      (integralPoleMulRegular_isRestricted c g f hg hf r) k)
  rw [integralPoleNumerator_mul c (k • g) f (PowerSeries.IsRestricted.smul 1 hg k),
    integralPoleNumerator_smul, integralPoleNumerator_mul c g f hg,
    PowerSeries.smul_eq_C_mul, mul_assoc]

theorem restrictedPoleFunctional_multiplier_difference (c : ι → ℤ_[p])
    (hc : Function.Injective c) (μ : ℕ → ℤ_[p]) (w : ι → (ℤ_[p])[X])
    (g h f : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g)
    (hh : PowerSeries.IsRestricted 1 h) (hf : PowerSeries.IsRestricted 1 f)
    (r : ι → ℤ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (he : ∀ n, ‖PowerSeries.coeff n (g-h)‖ ≤ B) (n : ℕ) :
    ‖(restrictedPoleFunctional μ w
        (integralPoleMulRegular c g f r) (integralPoleMulResidue c g r) -
      restrictedPoleFunctional μ w
        (integralPoleMulRegular c h f r) (integralPoleMulResidue c h r)).coeff n‖ ≤ B := by
  have hd : PowerSeries.IsRestricted 1 (g-h) := by
    rw [sub_eq_add_neg]
    exact PowerSeries.IsRestricted.add 1 hg (PowerSeries.IsRestricted.neg 1 hh)
  have hdec := integralPoleMultiplier_add c hc h (g-h) f hh hd hf r
  rw [add_sub_cancel] at hdec
  rw [hdec.1, hdec.2, restrictedPoleFunctional_add μ w _ _
    (integralPoleMulRegular_isRestricted c h f hh hf r)
    (integralPoleMulRegular_isRestricted c (g-h) f hd hf r), add_sub_cancel_left]
  exact restrictedPoleFunctional_coeff_bound μ w _ _ B hB
    (integralPoleMulRegular_bound_left c (g-h) f r B hB he)
    (integralPoleMulResidue_bound_left c (g-h) r B he) n

end
end Li2

end
