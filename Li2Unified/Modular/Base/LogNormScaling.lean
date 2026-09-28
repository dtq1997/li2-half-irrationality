module
public import Li2Unified.Modular.Base.LogNormMonotone

set_option backward.privateInPublic true

@[expose] public section

open MeasureTheory
namespace Li2
noncomputable section

theorem integral_log_norm_scale {c : ℝ} (hc : 0 < c) (b x : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..c * b,
      Real.log ‖(t : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I‖) =
      c * b * Real.log c + c *
        (∫ t : ℝ in (0 : ℝ)..b,
          Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) := by
  have heq :
      (∫ t : ℝ in (0 : ℝ)..b,
        Real.log ‖((c * t : ℝ) : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I‖) =
      ∫ t : ℝ in (0 : ℝ)..b,
        (Real.log c + Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(volume : Measure ℝ).ae_ne (0 : ℝ)] with t ht
    intro _
    have hn : (t : ℂ) + (x : ℂ) * Complex.I ≠ 0 := by
      intro h
      apply ht
      simpa using congrArg Complex.re h
    have hz : ((c * t : ℝ) : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I =
        (c : ℂ) * ((t : ℂ) + (x : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hz, norm_mul, Complex.norm_of_nonneg hc.le,
      Real.log_mul hc.ne' (norm_ne_zero_iff.mpr hn)]
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => Real.log ‖(t : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I‖)
    (a := 0) (b := b) c
  simp only [mul_zero, smul_eq_mul, heq] at hs
  rw [← hs, intervalIntegral.integral_add
    (by simp) (intervalIntegrable_log_norm_real_add_imag_all x 0 b),
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

end
end Li2

end
