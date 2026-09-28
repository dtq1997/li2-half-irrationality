module
public import Li2Unified.Modular.Positive.Packed.P074
public import Li2Unified.Modular.Base.OriginalContourHorizontalTails
public import Li2Unified.Modular.Base.OriginalContourRightActual
public import Li2Unified.Modular.Positive.Packed.P073
public import Li2Unified.Modular.Base.OriginalContourRightTails

set_option backward.privateInPublic true

@[expose] public section

section
/-! The top side of the diagonal positive-half rectangle has an additional
exponential factor from its upper-kernel multiplier. -/

open Polynomial MeasureTheory Filter Set
open scoped Topology BigOperators Interval
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

lemma upperMultiplier_norm_horizontal (x T : ℝ) :
    ‖upperMultiplier ((x : ℂ) + (T : ℂ) * Complex.I)‖ =
      Real.exp (-Real.pi * T) / (2 * Real.pi) := by
  unfold upperMultiplier
  rw [norm_div, Complex.norm_exp]
  have hnum : (((Real.pi : ℂ) * Complex.I) *
      ((x : ℂ) + (T : ℂ) * Complex.I)).re = -Real.pi * T := by
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  have hden : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), Complex.norm_I]
    norm_num
  rw [hnum, hden]

lemma upper_top_integrand_norm_le (d : ℕ) (F : ℚ[X]) (N : ℕ)
    (hN : 1 ≤ N) {x T : ℝ}
    (hx : x ∈ Set.Icc (1 / 2) ((N : ℝ) + 1 / 2)) (hT : 1 ≤ T) :
    ‖(power ((x : ℂ) + (T : ℂ) * Complex.I) *
        kappaPlus ((x : ℂ) + (T : ℂ) * Complex.I)) *
        deriv (Li2.originalContourG d F) ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      (Real.exp (-Real.pi * T) / (2 * Real.pi)) *
        (Li2.originalContourHorizontalConstant d F N *
          T ^ (Li2.originalContourGDerivativeNumerator d F).natDegree *
          Real.exp (-Real.pi * T)) := by
  let z : ℂ := (x : ℂ) + (T : ℂ) * Complex.I
  have hzim : z.im = T := by simp [z, Complex.add_im, Complex.mul_im]
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
    Li2.originalContour_sin_ne_zero_of_im_ne_zero (by rw [hzim]; linarith)
  have hk : power z * kappaPlus z = upperMultiplier z * Li2.originalContourKernel z :=
    kappaPlus_eq_kernel z hsin
  have hTabs : |T| = T := abs_of_nonneg (by linarith)
  have hold := Li2.originalContour_horizontal_integrand_norm_le d F N hN hx
    (t := T) (by rw [hTabs]; exact hT)
  rw [hTabs] at hold
  calc
    ‖(power z * kappaPlus z) * deriv (Li2.originalContourG d F) z‖ =
        ‖upperMultiplier z‖ *
          ‖Li2.originalContourKernel z * deriv (Li2.originalContourG d F) z‖ := by
      rw [hk]
      simp only [norm_mul]
      ring
    _ ≤ ‖upperMultiplier z‖ *
        (Li2.originalContourHorizontalConstant d F N *
          T ^ (Li2.originalContourGDerivativeNumerator d F).natDegree *
          Real.exp (-Real.pi * T)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [z] using hold
    _ = _ := by rw [upperMultiplier_norm_horizontal]

def upperTopIntegral (d : ℕ) (F : ℚ[X]) (N : ℕ) (T : ℝ) : ℂ :=
  ∫ x : ℝ in (1 / 2)..((N : ℝ) + 1 / 2),
    (power ((x : ℂ) + (T : ℂ) * Complex.I) *
      kappaPlus ((x : ℂ) + (T : ℂ) * Complex.I)) *
      deriv (Li2.originalContourG d F) ((x : ℂ) + (T : ℂ) * Complex.I)

lemma upperTopIntegral_norm_le (d : ℕ) (F : ℚ[X]) (N : ℕ)
    (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T) :
    ‖upperTopIntegral d F N T‖ ≤
      (N : ℝ) * ((Real.exp (-Real.pi * T) / (2 * Real.pi)) *
        (Li2.originalContourHorizontalConstant d F N *
          T ^ (Li2.originalContourGDerivativeNumerator d F).natDegree *
          Real.exp (-Real.pi * T))) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hab : (1 / 2 : ℝ) ≤ (N : ℝ) + 1 / 2 := by linarith
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 : ℝ)) (b := (N : ℝ) + 1 / 2)
    (f := fun x : ℝ =>
      (power ((x : ℂ) + (T : ℂ) * Complex.I) *
        kappaPlus ((x : ℂ) + (T : ℂ) * Complex.I)) *
        deriv (Li2.originalContourG d F) ((x : ℂ) + (T : ℂ) * Complex.I))
    (C := (Real.exp (-Real.pi * T) / (2 * Real.pi)) *
      (Li2.originalContourHorizontalConstant d F N *
        T ^ (Li2.originalContourGDerivativeNumerator d F).natDegree *
        Real.exp (-Real.pi * T)))
    (fun x hx => upper_top_integrand_norm_le d F N hN
      (by rw [Set.uIoc_of_le hab] at hx; exact ⟨hx.1.le, hx.2⟩) hT)
  have hlen : |((N : ℝ) + 1 / 2) - 1 / 2| = (N : ℝ) := by
    rw [add_sub_cancel_right, abs_of_nonneg (Nat.cast_nonneg N)]
  change ‖upperTopIntegral d F N T‖ ≤
    ((Real.exp (-Real.pi * T) / (2 * Real.pi)) *
      (Li2.originalContourHorizontalConstant d F N *
        T ^ (Li2.originalContourGDerivativeNumerator d F).natDegree *
        Real.exp (-Real.pi * T))) *
      |((N : ℝ) + 1 / 2) - 1 / 2| at hbound
  rw [hlen] at hbound
  convert hbound using 1; ring

theorem upperTopIntegral_diagonal_tendsto_zero (d : ℕ) (F : ℚ[X]) :
    Tendsto (fun N : ℕ => upperTopIntegral d F N (N : ℝ)) atTop (𝓝 0) := by
  let C : ℝ := Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F)
  let k : ℕ := (Li2.originalContourGDerivativeNumerator d F).natDegree
  have hC : 0 ≤ C := Li2.originalRightCoefficientNormSum_nonneg _
  have hr : Tendsto (fun t : ℝ =>
      t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi) * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        ((2 * k + 1 : ℕ) : ℝ) (2 * Real.pi) (by positivity)
  have hn : Tendsto (fun N : ℕ =>
      (N : ℝ) ^ (2 * k + 1) * Real.exp (-(2 * Real.pi) * (N : ℝ)))
      atTop (𝓝 0) := hr.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ =>
      (2 * C * 3 ^ k) *
        ((N : ℝ) ^ (2 * k + 1) * Real.exp (-(2 * Real.pi) * (N : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hn.const_mul (2 * C * 3 ^ k)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow : ((N : ℝ) + 2) ^ k ≤ (3 * (N : ℝ)) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc
    ‖upperTopIntegral d F N (N : ℝ)‖ ≤
        (N : ℝ) * ((Real.exp (-Real.pi * (N : ℝ)) / (2 * Real.pi)) *
          (Li2.originalContourHorizontalConstant d F N *
            (N : ℝ) ^ k * Real.exp (-Real.pi * (N : ℝ)))) :=
      upperTopIntegral_norm_le d F N hN hNR
    _ = 2 * C * ((N : ℝ) * ((N : ℝ) + 2) ^ k *
        (N : ℝ) ^ k *
        (Real.exp (-Real.pi * (N : ℝ)) * Real.exp (-Real.pi * (N : ℝ)))) := by
      unfold Li2.originalContourHorizontalConstant
      dsimp only [C, k]
      field_simp [hpi]
      ring
    _ = 2 * C * ((N : ℝ) * ((N : ℝ) + 2) ^ k *
        (N : ℝ) ^ k * Real.exp (-(2 * Real.pi) * (N : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ 2 * C * ((N : ℝ) * (3 * (N : ℝ)) ^ k *
        (N : ℝ) ^ k * Real.exp (-(2 * Real.pi) * (N : ℝ))) := by
      gcongr
    _ = (2 * C * 3 ^ k) *
        ((N : ℝ) ^ (2 * k + 1) * Real.exp (-(2 * Real.pi) * (N : ℝ))) := by
      rw [mul_pow, pow_add, pow_mul, pow_succ]
      ring

end
end Li2Unified.Proofs.Contour

end

section
/-! Integer translation of the positive-half star kernels, for right-edge
tail estimates. -/

namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

private lemma exp_neg_period (N : ℕ) :
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (N : ℂ)) = 1 := by
  rw [show -(2 * (Real.pi : ℂ) * Complex.I) * (N : ℂ) =
      -((N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) by ring]
  rw [Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I]
  norm_num

private lemma exp_pos_period (N : ℕ) :
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (N : ℂ)) = 1 := by
  rw [show (2 * (Real.pi : ℂ) * Complex.I) * (N : ℂ) =
      (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
  exact Complex.exp_nat_mul_two_pi_mul_I N

lemma kappaPlus_nat_add (N : ℕ) (z : ℂ) :
    kappaPlus ((N : ℂ) + z) = kappaPlus z := by
  unfold kappaPlus
  rw [mul_add, Complex.exp_add, exp_neg_period]
  ring

lemma kappaMinus_nat_add (N : ℕ) (z : ℂ) :
    kappaMinus ((N : ℂ) + z) = kappaMinus z := by
  unfold kappaMinus
  rw [mul_add, Complex.exp_add, exp_pos_period]
  ring

lemma upper_kernel_nat_add (N : ℕ) (z : ℂ) :
    power ((N : ℂ) + z) * kappaPlus ((N : ℂ) + z) =
      (1 / 2 : ℂ) ^ N * (power z * kappaPlus z) := by
  rw [kappaPlus_nat_add, power_eq_original,
    Li2.originalContourPower_nat_add, ← power_eq_original]
  ring

lemma lower_kernel_nat_add (N : ℕ) (z : ℂ) :
    power ((N : ℂ) + z) * kappaMinus ((N : ℂ) + z) =
      (1 / 2 : ℂ) ^ N * (power z * kappaMinus z) := by
  rw [kappaMinus_nat_add, power_eq_original,
    Li2.originalContourPower_nat_add, ← power_eq_original]
  ring

end
end Li2Unified.Proofs.Contour

end


end
