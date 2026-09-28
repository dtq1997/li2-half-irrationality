module
public import Li2Unified.Modular.Base.LogNormIntegral
public import Li2Unified.Modular.Base.OriginalExternalField

set_option backward.privateInPublic true

@[expose] public section

open MeasureTheory
namespace Li2
noncomputable section

lemma log_sixteen_add_sq (x : ℝ) :
    Real.log (16 + x ^ 2) =
      2 * Real.log 4 + Real.log (1 + x ^ 2 / 16) := by
  have hpos : 0 < 1 + x ^ 2 / 16 := by positivity
  calc
    Real.log (16 + x ^ 2) =
        Real.log ((4 : ℝ) ^ 2 * (1 + x ^ 2 / 16)) := by
      congr 1
      ring
    _ = Real.log ((4 : ℝ) ^ 2) + Real.log (1 + x ^ 2 / 16) :=
      Real.log_mul (by norm_num) (ne_of_gt hpos)
    _ = _ := by rw [Real.log_pow]; norm_num

/-- The literal identity (4) of GLOBAL-INTEGRAL-v1 on the nonnegative axis. -/
theorem originalExternalV_eq_log_integrals_of_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    originalExternalV x =
      4 * Real.log 4 - 1 +
        3 * (∫ t : ℝ in (0 : ℝ)..1,
          Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) -
        (∫ t : ℝ in (0 : ℝ)..4,
          Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) -
        Real.pi * x := by
  by_cases hx0 : x = 0
  · subst x
    simp only [Complex.ofReal_zero, log_norm_real_add_imag_zero,
      originalExternalV_zero, mul_zero, sub_zero]
    rw [integral_log_from_zero, integral_log_from_zero, Real.log_one]
    ring
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hA1 : Real.arctan (1 / x) = Real.pi / 2 - Real.arctan x := by
    simpa only [one_div] using Real.arctan_inv_of_pos hxp
  have hA4 : Real.arctan (4 / x) =
      Real.pi / 2 - Real.arctan (x / 4) := by
    simpa only [inv_div] using
      Real.arctan_inv_of_pos (div_pos hxp (by norm_num : (0 : ℝ) < 4))
  rw [integral_log_norm_real_add_imag (x := x) (b := 1) hx (by norm_num),
    integral_log_norm_real_add_imag (x := x) (b := 4) hx (by norm_num),
    hA1, hA4]
  norm_num only [one_pow]
  rw [log_sixteen_add_sq, originalExternalV, originalExternalW_eq_formula]
  ring

/-- The same original external field on the whole real axis. -/
theorem originalExternalV_eq_log_integrals (x : ℝ) :
    originalExternalV x =
      4 * Real.log 4 - 1 +
        3 * (∫ t : ℝ in (0 : ℝ)..1,
          Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) -
        (∫ t : ℝ in (0 : ℝ)..4,
          Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) -
        Real.pi * |x| := by
  have hV : originalExternalV |x| = originalExternalV x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, even_originalExternalV x]
  have h := originalExternalV_eq_log_integrals_of_nonneg (abs_nonneg x)
  rw [hV] at h
  simpa only [log_norm_real_add_imag, sq_abs] using h

end
end Li2

end
