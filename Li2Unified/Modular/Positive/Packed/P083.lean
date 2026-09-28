module
public import Li2Unified.Modular.Positive.Packed.P082
public import Li2Unified.Modular.Base.OriginalContourHorizontalTails
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.privateInPublic true

@[expose] public section

section
/-! The real-ray endpoint from the actual quotient vanishes exponentially. -/

open Filter Polynomial
open scoped Topology BigOperators
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

private lemma shifted_log_two_decay (k : ℕ) :
    Tendsto (fun x : ℝ => (1 + x) ^ k * Real.exp (-Real.log 2 * x))
      atTop (𝓝 0) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : Tendsto
      (fun x : ℝ => x ^ k * Real.exp (-(Real.log 2) * x))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) (Real.log 2) hlog
  have hscale : Tendsto
      (fun x : ℝ => (2 : ℝ) ^ k * (x ^ k * Real.exp (-(Real.log 2) * x)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hbase.const_mul ((2 : ℝ) ^ k)
  apply squeeze_zero_norm' _ hscale
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 ≤ x := by linarith
  have hpow : (1 + x) ^ k ≤ (2 * x) ^ k :=
    pow_le_pow_left₀ (by linarith) (by linarith) k
  calc
    ‖(1 + x) ^ k * Real.exp (-Real.log 2 * x)‖ =
        (1 + x) ^ k * Real.exp (-Real.log 2 * x) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ (2 * x) ^ k * Real.exp (-Real.log 2 * x) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = (2 : ℝ) ^ k * (x ^ k * Real.exp (-(Real.log 2) * x)) := by
      rw [mul_pow]
      ring

private lemma ray_endpoint_norm_bound (d : ℕ) (F : ℚ[X])
    (x : ℝ) (hx : 1 ≤ x) :
    ‖power (x : ℂ) * Li2.originalContourG d F (x : ℂ)‖ ≤
      Li2.originalCoefficientNormSum F *
        ((1 + x) ^ (F.natDegree + 1) * Real.exp (-Real.log 2 * x)) := by
  let C : ℝ := Li2.originalCoefficientNormSum F
  let z : ℂ := (x : ℂ)
  have hx0 : 0 ≤ x := by linarith
  have hR : 1 ≤ 1 + x := by linarith
  have hz : ‖z‖ ≤ 1 + x := by
    dsimp [z]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    linarith
  have hF : ‖F.eval₂ (Rat.castHom ℂ) z‖ ≤ C * (1 + x) ^ F.natDegree :=
    Li2.originalComplexEval_norm_le_of_norm_le F z (1 + x) hR hz
  have hD : 1 ≤ ‖(Li2.D d).eval₂ (Rat.castHom ℂ) z‖ := by
    apply Li2.D_eval₂_complex_norm_ge_one_of_re_nonneg d
    simpa [z] using hx0
  have hq : ‖Li2.originalComplexQuotient d F z‖ ≤
      C * (1 + x) ^ F.natDegree := by
    rw [Li2.originalComplexQuotient, norm_div]
    exact (div_le_self (norm_nonneg _) hD).trans hF
  have hp : ‖power z‖ = Real.exp (-Real.log 2 * x) := by
    have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      simp [one_div, Real.log_inv]
    dsimp [z, power]
    rw [Complex.norm_exp]
    rw [hlog]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  calc
    ‖power z * Li2.originalContourG d F z‖ =
        ‖power z‖ * ‖z‖ * ‖Li2.originalComplexQuotient d F z‖ := by
      simp only [Li2.originalContourG, norm_mul]
      ring
    _ ≤ Real.exp (-Real.log 2 * x) * (1 + x) *
          (C * (1 + x) ^ F.natDegree) := by
      rw [hp]
      gcongr
    _ = C * ((1 + x) ^ (F.natDegree + 1) *
          Real.exp (-Real.log 2 * x)) := by
      rw [pow_succ]
      ring

lemma ray_actual_G_endpoint (d : ℕ) (F : ℚ[X]) :
    Tendsto (fun x : ℝ => power (x : ℂ) * Li2.originalContourG d F (x : ℂ))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun x : ℝ => Li2.originalCoefficientNormSum F *
      ((1 + x) ^ (F.natDegree + 1) * Real.exp (-Real.log 2 * x)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (shifted_log_two_decay (F.natDegree + 1)).const_mul
        (Li2.originalCoefficientNormSum F)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact ray_endpoint_norm_bound d F x hx

lemma ray_actual_G_endpoint_nat (d : ℕ) (F : ℚ[X]) :
    Tendsto (fun N : ℕ =>
      power ((((N : ℝ) + 1 / 2 : ℝ) : ℂ)) *
        Li2.originalContourG d F ((((N : ℝ) + 1 / 2 : ℝ) : ℂ)))
      atTop (𝓝 0) := by
  have hx : Tendsto (fun N : ℕ => (N : ℝ) + 1 / 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro B
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop B)]
      with N hN
    linarith
  exact (ray_actual_G_endpoint d F).comp hx

end
end Li2Unified.Proofs.Contour

end


end
