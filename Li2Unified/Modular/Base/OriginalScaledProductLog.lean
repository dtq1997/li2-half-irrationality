module
public import Li2Unified.Modular.Base.OriginalProductLog
public import Li2Unified.Modular.Base.OriginalSnLogBounds
public import Li2Unified.Modular.Base.LogNormScaling
public import Li2Unified.Modular.Base.OriginalExternalFieldIntegral

set_option backward.privateInPublic true

@[expose] public section

open Polynomial MeasureTheory
namespace Li2
noncomputable section

/-- The scaled original quotient, including its normalization and exponential weight. -/
theorem original_scaled_product_log_upper (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    Real.log (Sn n : ℝ) +
        3 * Real.log ‖(D n).eval₂ (Rat.castHom ℂ)
          (originalContourPoint ((n : ℝ) * x))‖ -
        Real.log ‖(D (4 * n)).eval₂ (Rat.castHom ℂ)
          (originalContourPoint ((n : ℝ) * x))‖ -
        Real.pi * |(n : ℝ) * x| ≤
      (n : ℝ) * originalExternalV x + Real.log 2 - Real.log (n : ℝ) +
        (9 / 2 : ℝ) * Real.log ((n : ℝ) + 3 / 2 + |(n : ℝ) * x|) +
        11 / 4 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnum := (originalD_log_norm_bounds n ((n : ℝ) * x)).2
  have hden := (originalD_log_norm_bounds (4 * n) ((n : ℝ) * x)).1
  have hs := (originalSn_log_error_bounds n hn).2
  have hi1 := integral_log_norm_scale hnR 1 x
  have hi4 := integral_log_norm_scale hnR 4 x
  simp only [mul_one] at hi1
  have hcast : ((4 * n : ℕ) : ℝ) = (n : ℝ) * 4 := by push_cast; ring
  rw [hcast] at hden
  rw [hi1] at hnum
  rw [hi4] at hden
  have hv := originalExternalV_eq_log_integrals x
  have hvn := congrArg (fun t : ℝ => (n : ℝ) * t) hv
  dsimp only at hvn
  simp only [abs_mul, abs_of_pos hnR] at hnum ⊢
  nlinarith only [hnum, hden, hs, hvn]

end
end Li2

end
