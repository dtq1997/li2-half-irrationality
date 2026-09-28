module
public import Li2Unified.Modular.Positive.Packed.P090
public import Li2Unified.Modular.Positive.Packed.P073
public import Li2Unified.Modular.Base.OriginalContourRational
public import Li2Unified.Modular.Base.OriginalContourCompensated

set_option backward.privateInPublic true

@[expose] public section

section
/-! The actual quotient `G=z*F/D_m` causes no endpoint contribution on the
vertical arms. This uses its independently proved polynomial growth bound. -/

open Filter Polynomial
open scoped Topology
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

private lemma shifted_poly_exp_decay (k : ℕ) :
    Tendsto (fun T : ℝ => (1 + T) ^ k * Real.exp (-2 * Real.pi * T))
      atTop (𝓝 0) := by
  have hbase : Tendsto (fun T : ℝ => T ^ k * Real.exp (-(2 * Real.pi) * T))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (k : ℝ) (2 * Real.pi) (by positivity)
  have hbound : Tendsto
      (fun T : ℝ => (2 : ℝ) ^ k * (T ^ k * Real.exp (-(2 * Real.pi) * T)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hbase.const_mul ((2 : ℝ) ^ k)
  apply squeeze_zero_norm' _ hbound
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : 0 ≤ T := by linarith
  have hpow : (1 + T) ^ k ≤ (2 * T) ^ k :=
    pow_le_pow_left₀ (by linarith) (by linarith) k
  calc
    ‖(1 + T) ^ k * Real.exp (-2 * Real.pi * T)‖ =
        (1 + T) ^ k * Real.exp (-2 * Real.pi * T) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ (2 * T) ^ k * Real.exp (-2 * Real.pi * T) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = (2 : ℝ) ^ k * (T ^ k * Real.exp (-(2 * Real.pi) * T)) := by
      rw [mul_pow]
      ring

lemma upper_actual_G_endpoint (m : ℕ) (F : ℚ[X]) :
    Tendsto (fun T : ℝ =>
      power (point ⟨1, by decide⟩ T) *
        kappaPlus (point ⟨1, by decide⟩ T) *
        Li2.originalContourG m F (point ⟨1, by decide⟩ T))
      atTop (𝓝 0) := by
  let C : ℝ := Li2.originalCoefficientNormSum F
  have hlim : Tendsto (fun T : ℝ =>
      C * ((1 + T) ^ (F.natDegree + 1) * Real.exp (-2 * Real.pi * T)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (shifted_poly_exp_decay (F.natDegree + 1)).const_mul C
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  let z : ℂ := point ⟨1, by decide⟩ T
  have hT0 : 0 ≤ T := by linarith
  have hp : ‖power z‖ ≤ 1 := by
    change ‖power (point ⟨1, by decide⟩ T)‖ ≤ 1
    rw [power_eq_original, point_up]
    exact Li2.originalContourPower_norm_le_one T
  have hk : ‖kappaPlus z‖ ≤ Real.exp (-2 * Real.pi * T) := by
    dsimp [z]
    exact kappaPlus_upper_norm_le T
  have hz : ‖z‖ ≤ 1 + T := by
    change ‖point ⟨1, by decide⟩ T‖ ≤ 1 + T
    rw [point_up]
    have h := Li2.originalContourPoint_norm_le T
    rw [abs_of_nonneg hT0] at h
    linarith
  have hq : ‖Li2.originalComplexQuotient m F z‖ ≤
      C * (1 + T) ^ F.natDegree := by
    change ‖Li2.originalComplexQuotient m F (point ⟨1, by decide⟩ T)‖ ≤
      Li2.originalCoefficientNormSum F * (1 + T) ^ F.natDegree
    rw [point_up]
    simpa only [abs_of_nonneg hT0] using
      Li2.originalComplexQuotient_vertical_polynomial_growth m F T
  calc
    ‖power z * kappaPlus z * Li2.originalContourG m F z‖ =
        ‖power z‖ * ‖kappaPlus z‖ * ‖z‖ *
          ‖Li2.originalComplexQuotient m F z‖ := by
      simp only [Li2.originalContourG, norm_mul]
      ring
    _ ≤ 1 * Real.exp (-2 * Real.pi * T) * (1 + T) *
          (C * (1 + T) ^ F.natDegree) := by
      gcongr
    _ = C * ((1 + T) ^ (F.natDegree + 1) *
          Real.exp (-2 * Real.pi * T)) := by
      rw [pow_succ]
      ring

lemma lower_actual_G_endpoint (m : ℕ) (F : ℚ[X]) :
    Tendsto (fun T : ℝ =>
      power (point ⟨2, by decide⟩ T) *
        kappaMinus (point ⟨2, by decide⟩ T) *
        Li2.originalContourG m F (point ⟨2, by decide⟩ T))
      atTop (𝓝 0) := by
  let C : ℝ := Li2.originalCoefficientNormSum F
  have hlim : Tendsto (fun T : ℝ =>
      C * ((1 + T) ^ (F.natDegree + 1) * Real.exp (-2 * Real.pi * T)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (shifted_poly_exp_decay (F.natDegree + 1)).const_mul C
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  let z : ℂ := point ⟨2, by decide⟩ T
  have hT0 : 0 ≤ T := by linarith
  have hp : ‖power z‖ ≤ 1 := by
    change ‖power (point ⟨2, by decide⟩ T)‖ ≤ 1
    rw [power_eq_original, point_down]
    exact Li2.originalContourPower_norm_le_one (-T)
  have hk : ‖kappaMinus z‖ ≤ Real.exp (-2 * Real.pi * T) := by
    dsimp [z]
    exact kappaMinus_lower_norm_le T
  have hz : ‖z‖ ≤ 1 + T := by
    change ‖point ⟨2, by decide⟩ T‖ ≤ 1 + T
    rw [point_down]
    have h := Li2.originalContourPoint_norm_le (-T)
    rw [abs_neg, abs_of_nonneg hT0] at h
    linarith
  have hq : ‖Li2.originalComplexQuotient m F z‖ ≤
      C * (1 + T) ^ F.natDegree := by
    change ‖Li2.originalComplexQuotient m F (point ⟨2, by decide⟩ T)‖ ≤
      Li2.originalCoefficientNormSum F * (1 + T) ^ F.natDegree
    rw [point_down]
    simpa only [abs_neg, abs_of_nonneg hT0] using
      Li2.originalComplexQuotient_vertical_polynomial_growth m F (-T)
  calc
    ‖power z * kappaMinus z * Li2.originalContourG m F z‖ =
        ‖power z‖ * ‖kappaMinus z‖ * ‖z‖ *
          ‖Li2.originalComplexQuotient m F z‖ := by
      simp only [Li2.originalContourG, norm_mul]
      ring
    _ ≤ 1 * Real.exp (-2 * Real.pi * T) * (1 + T) *
          (C * (1 + T) ^ F.natDegree) := by
      gcongr
    _ = C * ((1 + T) ^ (F.natDegree + 1) *
          Real.exp (-2 * Real.pi * T)) := by
      rw [pow_succ]
      ring

end
end Li2Unified.Proofs.Contour

end


end
