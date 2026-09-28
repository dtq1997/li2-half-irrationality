module
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

set_option backward.privateInPublic true

@[expose] public section
/-
SPDX-License-Identifier: Apache-2.0
Adapted from Apery/CircleAtoms.lean in https://github.com/mo271/Zeta5,
commit f19a1960609f7d38e7b63fd2acb05e6f60a7b741.
See ../LICENSE-Zeta5 for the upstream Apache 2.0 license.
Narrow imports and Li2 namespace; retain only the stated logarithmic
integral tools; replace old circle fibers by fixed Mathlib countable preimages.
-/


open MeasureTheory Real intervalIntegral
namespace Li2

lemma circle_log_integrable (c a : ℂ) (R : ℝ) :
    IntervalIntegrable (fun θ => Real.log ‖circleMap c R θ - a‖) volume 0 (2 * π) :=
  circleIntegrable_log_norm_sub_const R

lemma circle_log_integral_zero_one (a : ℂ) :
    (∫ θ in (0 : ℝ)..2 * π, Real.log ‖circleMap 0 1 θ - a‖) =
      2 * π * log⁺ ‖a‖ := by
  have h := circleAverage_log_norm_sub_const_eq_posLog (a := a)
  rw [circleAverage_def, smul_eq_mul] at h
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  calc
    _ = (2 * π) * ((2 * π)⁻¹ *
        (∫ θ in (0 : ℝ)..2 * π, Real.log ‖circleMap 0 1 θ - a‖)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
    _ = _ := congrArg (fun t : ℝ => (2 * π) * t) h

lemma cos_eq_half_add_inv (θ : ℝ) :
    ((Real.cos θ : ℝ) : ℂ) = (circleMap 0 1 θ + (circleMap 0 1 θ)⁻¹) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, circleMap_zero]
  simp only [Complex.ofReal_one, one_mul]
  rw [← Complex.exp_neg]
  ring_nf

end Li2

end
