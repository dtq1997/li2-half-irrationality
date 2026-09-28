module
public import Li2Unified.Modular.Positive.Packed.P073
public import Li2Unified.Modular.Positive.Packed.P077
public import Li2Unified.Modular.Base.OriginalContourRightActual

set_option backward.privateInPublic true

@[expose] public section

section
/-! The positive-half star kernels on their respective vertical arms. -/

namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

lemma exp_upper_arm (y : ℝ) :
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * point ⟨1, by decide⟩ y) =
      -((Real.exp (2 * Real.pi * y) : ℝ) : ℂ) := by
  have harg : -(2 * (Real.pi : ℂ) * Complex.I) * point ⟨1, by decide⟩ y =
      -((Real.pi : ℂ) * Complex.I) + ((2 * Real.pi * y : ℝ) : ℂ) := by
    simp only [point, reduceIte]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [harg, Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
  rw [← Complex.ofReal_exp]
  ring

lemma exp_lower_arm (y : ℝ) :
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * point ⟨2, by decide⟩ y) =
      -((Real.exp (2 * Real.pi * y) : ℝ) : ℂ) := by
  have harg : (2 * (Real.pi : ℂ) * Complex.I) * point ⟨2, by decide⟩ y =
      ((Real.pi : ℂ) * Complex.I) + ((2 * Real.pi * y : ℝ) : ℂ) := by
    simp only [point]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [harg, Complex.exp_add, Complex.exp_pi_mul_I]
  rw [← Complex.ofReal_exp]
  ring

lemma kappaPlus_upper (y : ℝ) :
    kappaPlus (point ⟨1, by decide⟩ y) =
      ((1 / (1 + Real.exp (2 * Real.pi * y)) : ℝ) : ℂ) := by
  unfold kappaPlus
  rw [exp_upper_arm]
  push_cast
  ring

lemma kappaMinus_lower (y : ℝ) :
    kappaMinus (point ⟨2, by decide⟩ y) =
      ((1 / (1 + Real.exp (2 * Real.pi * y)) : ℝ) : ℂ) := by
  unfold kappaMinus
  rw [exp_lower_arm]
  push_cast
  ring

lemma kappaPlus_upper_norm_le (y : ℝ) :
    ‖kappaPlus (point ⟨1, by decide⟩ y)‖ ≤ Real.exp (-2 * Real.pi * y) := by
  rw [kappaPlus_upper, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  calc
    1 / (1 + Real.exp (2 * Real.pi * y)) ≤
        1 / Real.exp (2 * Real.pi * y) :=
      one_div_le_one_div_of_le (Real.exp_pos _) (by linarith)
    _ = Real.exp (-2 * Real.pi * y) := by
      rw [show -2 * Real.pi * y = -(2 * Real.pi * y) by ring, Real.exp_neg]
      simp only [one_div]

lemma kappaMinus_lower_norm_le (y : ℝ) :
    ‖kappaMinus (point ⟨2, by decide⟩ y)‖ ≤ Real.exp (-2 * Real.pi * y) := by
  rw [kappaMinus_lower, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  calc
    1 / (1 + Real.exp (2 * Real.pi * y)) ≤
        1 / Real.exp (2 * Real.pi * y) :=
      one_div_le_one_div_of_le (Real.exp_pos _) (by linarith)
    _ = Real.exp (-2 * Real.pi * y) := by
      rw [show -2 * Real.pi * y = -(2 * Real.pi * y) by ring, Real.exp_neg]
      simp only [one_div]

end
end Li2Unified.Proofs.Contour

end

section
/-! The right side of a fixed-height positive-half upper rectangle vanishes
as its width tends to infinity. -/

open Polynomial MeasureTheory Filter Set
open scoped Topology BigOperators Interval
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

lemma kappaPlus_upper_norm_le_one (y : ℝ) :
    ‖kappaPlus (point ⟨1, by decide⟩ y)‖ ≤ 1 := by
  rw [kappaPlus_upper, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [Real.exp_pos (2 * Real.pi * y)]

lemma upper_right_integrand_norm_le (d : ℕ) (F : ℚ[X]) (N : ℕ) (y : ℝ) :
    ‖(power ((N : ℂ) + point ⟨1, by decide⟩ y) *
        kappaPlus ((N : ℂ) + point ⟨1, by decide⟩ y)) *
        deriv (Li2.originalContourG d F) ((N : ℂ) + point ⟨1, by decide⟩ y)‖ ≤
      (1 / 2 : ℝ) ^ N *
        Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F) *
          (1 + (N : ℝ) + |y|) ^
            (Li2.originalContourGDerivativeNumerator d F).natDegree := by
  have hp : ‖power (point ⟨1, by decide⟩ y)‖ ≤ 1 := by
    rw [power_eq_original, point_up]
    exact Li2.originalContourPower_norm_le_one y
  have hk := kappaPlus_upper_norm_le_one y
  have hg : ‖deriv (Li2.originalContourG d F)
      ((N : ℂ) + point ⟨1, by decide⟩ y)‖ ≤
      Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F) *
        (1 + (N : ℝ) + |y|) ^
          (Li2.originalContourGDerivativeNumerator d F).natDegree := by
    rw [point_up]
    exact Li2.originalContourG_deriv_right_norm_le d F N y
  have hp0 : ‖((1 / 2 : ℂ) ^ N)‖ = (1 / 2 : ℝ) ^ N := by norm_num
  have hpk : ‖power (point ⟨1, by decide⟩ y)‖ *
      ‖kappaPlus (point ⟨1, by decide⟩ y)‖ ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hp hk (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  calc
    _ = (1 / 2 : ℝ) ^ N *
        (‖power (point ⟨1, by decide⟩ y)‖ *
          ‖kappaPlus (point ⟨1, by decide⟩ y)‖) *
        ‖deriv (Li2.originalContourG d F)
          ((N : ℂ) + point ⟨1, by decide⟩ y)‖ := by
      rw [upper_kernel_nat_add, norm_mul, norm_mul, norm_mul, hp0]
    _ ≤ (1 / 2 : ℝ) ^ N * 1 *
        ‖deriv (Li2.originalContourG d F)
          ((N : ℂ) + point ⟨1, by decide⟩ y)‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpk (by positivity)) (norm_nonneg _)
    _ ≤ (1 / 2 : ℝ) ^ N * 1 *
        (Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F) *
          (1 + (N : ℝ) + |y|) ^
            (Li2.originalContourGDerivativeNumerator d F).natDegree) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by ring

def upperRightIntegral (d : ℕ) (F : ℚ[X]) (N : ℕ) (T : ℝ) : ℂ :=
  ∫ y : ℝ in (-T)..T,
    (power ((N : ℂ) + point ⟨1, by decide⟩ y) *
      kappaPlus ((N : ℂ) + point ⟨1, by decide⟩ y)) *
      deriv (Li2.originalContourG d F) ((N : ℂ) + point ⟨1, by decide⟩ y)

lemma upperRightIntegral_norm_le (d : ℕ) (F : ℚ[X]) (N : ℕ) (T : ℝ)
    (hT : 0 ≤ T) :
    ‖upperRightIntegral d F N T‖ ≤
      (2 * T) * ((1 / 2 : ℝ) ^ N *
        Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F) *
          (1 + (N : ℝ) + T) ^
            (Li2.originalContourGDerivativeNumerator d F).natDegree) := by
  let C : ℝ := Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F)
  let k : ℕ := (Li2.originalContourGDerivativeNumerator d F).natDegree
  have hC : 0 ≤ C := Li2.originalRightCoefficientNormSum_nonneg _
  have hbound (y : ℝ) (hy : y ∈ Set.uIoc (-T) T) :
      ‖(power ((N : ℂ) + point ⟨1, by decide⟩ y) *
          kappaPlus ((N : ℂ) + point ⟨1, by decide⟩ y)) *
          deriv (Li2.originalContourG d F) ((N : ℂ) + point ⟨1, by decide⟩ y)‖ ≤
        (1 / 2 : ℝ) ^ N * C * (1 + (N : ℝ) + T) ^ k := by
    have hy' : -T < y ∧ y ≤ T := by
      have hInterval : -T ≤ T := by linarith
      rw [Set.uIoc_of_le hInterval] at hy
      exact hy
    have hyT : |y| ≤ T := abs_le.mpr ⟨by linarith [hy'.1], hy'.2⟩
    have hpow : (1 + (N : ℝ) + |y|) ^ k ≤ (1 + (N : ℝ) + T) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    calc
      _ ≤ (1 / 2 : ℝ) ^ N * C * (1 + (N : ℝ) + |y|) ^ k :=
        upper_right_integrand_norm_le d F N y
      _ ≤ (1 / 2 : ℝ) ^ N * C * (1 + (N : ℝ) + T) ^ k := by
        gcongr
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := T)
    (f := fun y : ℝ =>
      (power ((N : ℂ) + point ⟨1, by decide⟩ y) *
        kappaPlus ((N : ℂ) + point ⟨1, by decide⟩ y)) *
        deriv (Li2.originalContourG d F) ((N : ℂ) + point ⟨1, by decide⟩ y))
    (C := (1 / 2 : ℝ) ^ N * C * (1 + (N : ℝ) + T) ^ k) hbound
  have hlen : |T - -T| = 2 * T := by
    rw [show T - -T = 2 * T by ring, abs_of_nonneg (by positivity)]
  change ‖upperRightIntegral d F N T‖ ≤
    ((1 / 2 : ℝ) ^ N * C * (1 + (N : ℝ) + T) ^ k) * |T - -T| at h
  rw [hlen] at h
  convert h using 1; ring

theorem upperRightIntegral_tendsto_zero (d : ℕ) (F : ℚ[X]) (T : ℝ)
    (hT : 0 ≤ T) : Tendsto (fun N : ℕ => upperRightIntegral d F N T) atTop (𝓝 0) := by
  let C : ℝ := Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F)
  let k : ℕ := (Li2.originalContourGDerivativeNumerator d F).natDegree
  have hdecay := Li2.originalRightDecay_tendsto_zero k
  have hlim : Tendsto
      (fun N : ℕ => (2 * T * C * (1 + T) ^ k) *
        ((1 + (N : ℝ)) ^ k * (1 / 2 : ℝ) ^ N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hdecay.const_mul (2 * T * C * (1 + T) ^ k)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [] with N
  have hC : 0 ≤ C := Li2.originalRightCoefficientNormSum_nonneg _
  have hshift : 1 + (N : ℝ) + T ≤ (1 + T) * (1 + (N : ℝ)) := by
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith
  have hpow : (1 + (N : ℝ) + T) ^ k ≤
      (1 + T) ^ k * (1 + (N : ℝ)) ^ k := by
    calc
      _ ≤ ((1 + T) * (1 + (N : ℝ))) ^ k :=
        pow_le_pow_left₀ (by positivity) hshift k
      _ = _ := mul_pow _ _ _
  calc
    ‖upperRightIntegral d F N T‖ ≤
        (2 * T) * ((1 / 2 : ℝ) ^ N * C * (1 + (N : ℝ) + T) ^ k) :=
      upperRightIntegral_norm_le d F N T hT
    _ ≤ (2 * T) * ((1 / 2 : ℝ) ^ N * C *
        ((1 + T) ^ k * (1 + (N : ℝ)) ^ k)) := by gcongr
    _ = (2 * T * C * (1 + T) ^ k) *
        ((1 + (N : ℝ)) ^ k * (1 / 2 : ℝ) ^ N) := by ring

end
end Li2Unified.Proofs.Contour

end


end
