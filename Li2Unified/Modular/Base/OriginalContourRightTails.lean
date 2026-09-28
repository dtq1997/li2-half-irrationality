module
public import Li2Unified.Modular.Base.OriginalContourResidue
public import Li2Unified.Modular.Base.OriginalContourIBP
public import Mathlib.Analysis.SpecificLimits.Normed

set_option backward.privateInPublic true

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace Li2
noncomputable section

lemma originalContour_sin_nat_add (N : ℕ) (z : ℂ) :
    Complex.sin ((Real.pi : ℂ) * ((N : ℂ) + z)) =
      (-1 : ℂ) ^ N * Complex.sin ((Real.pi : ℂ) * z) := by
  simp only [mul_add, Complex.sin_add, originalContour_sin_nat,
    originalContour_cos_nat, zero_mul, zero_add]

lemma originalContourPower_nat_add (N : ℕ) (z : ℂ) :
    originalContourPower ((N : ℂ) + z) =
      (1 / 2 : ℂ) ^ N * originalContourPower z := by
  calc
    originalContourPower ((N : ℂ) + z) =
        originalContourPower (N : ℂ) * originalContourPower z := by
      simp only [originalContourPower, mul_add, Complex.exp_add]
    _ = (1 / 2 : ℂ) ^ N * originalContourPower z := by
      rw [originalContourPower_nat]

lemma originalContourKernel_nat_add (N : ℕ) (z : ℂ) :
    originalContourKernel ((N : ℂ) + z) =
      (-1 / 2 : ℂ) ^ N * originalContourKernel z := by
  unfold originalContourKernel
  rw [originalContourPower_nat_add, originalContour_sin_nat_add]
  calc
    (Real.pi : ℂ) * ((1 / 2 : ℂ) ^ N * originalContourPower z) /
        ((-1 : ℂ) ^ N * Complex.sin ((Real.pi : ℂ) * z)) =
      ((1 / 2 : ℂ) ^ N / (-1 : ℂ) ^ N) *
        ((Real.pi : ℂ) * originalContourPower z /
          Complex.sin ((Real.pi : ℂ) * z)) := by
      rw [div_mul_div_comm]
      congr 1 <;> ring
    _ = (-1 / 2 : ℂ) ^ N *
        ((Real.pi : ℂ) * originalContourPower z /
          Complex.sin ((Real.pi : ℂ) * z)) := by
      rw [← div_pow]
      norm_num

lemma originalContourKernel_nat_add_norm (N : ℕ) (z : ℂ) :
    ‖originalContourKernel ((N : ℂ) + z)‖ =
      (1 / 2 : ℝ) ^ N * ‖originalContourKernel z‖ := by
  rw [originalContourKernel_nat_add, norm_mul, norm_pow]
  have h : ‖(-1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    norm_num [norm_div]
  rw [h]

lemma originalRightContourKernel_norm_le (N : ℕ) (y : ℝ) :
    ‖originalContourKernel ((N : ℂ) + originalContourPoint y)‖ ≤
      (2 * Real.pi) * (1 / 2 : ℝ) ^ N *
        Real.exp (-Real.pi * |y|) := by
  rw [originalContourKernel_nat_add_norm]
  calc
    (1 / 2 : ℝ) ^ N *
        ‖originalContourKernel (originalContourPoint y)‖ ≤
      (1 / 2 : ℝ) ^ N *
        ((2 * Real.pi) * Real.exp (-Real.pi * |y|)) :=
      mul_le_mul_of_nonneg_left
        (originalContourKernel_norm_le_exp y) (by positivity)
    _ = (2 * Real.pi) * (1 / 2 : ℝ) ^ N *
        Real.exp (-Real.pi * |y|) := by ring

lemma continuous_originalRightContourKernel (N : ℕ) :
    Continuous (fun y : ℝ =>
      originalContourKernel ((N : ℂ) + originalContourPoint y)) := by
  simpa only [originalContourKernel_nat_add] using
    (continuous_const.mul continuous_originalContourKernel_vertical :
      Continuous (fun y : ℝ =>
        (-1 / 2 : ℂ) ^ N *
          originalContourKernel (originalContourPoint y)))

lemma originalRightKernel_mul_norm_le
    {C : ℝ} (hC : 0 ≤ C) (d N : ℕ) (f : ℝ → ℂ)
    (hf : ∀ y, ‖f y‖ ≤ C * (1 + (N : ℝ) + |y|) ^ d)
    (y : ℝ) :
    ‖originalContourKernel ((N : ℂ) + originalContourPoint y) * f y‖ ≤
      (2 * Real.pi * C) *
        ((1 + (N : ℝ)) ^ d * (1 / 2 : ℝ) ^ N) *
        ((1 + |y|) ^ d * Real.exp (-Real.pi * |y|)) := by
  have hsep :
      1 + (N : ℝ) + |y| ≤ (1 + (N : ℝ)) * (1 + |y|) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg N) (abs_nonneg y)]
  have hfp :
      ‖f y‖ ≤ C * (1 + (N : ℝ)) ^ d * (1 + |y|) ^ d := by
    calc
      ‖f y‖ ≤ C * (1 + (N : ℝ) + |y|) ^ d := hf y
      _ ≤ C * ((1 + (N : ℝ)) * (1 + |y|)) ^ d :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hsep d) hC
      _ = C * (1 + (N : ℝ)) ^ d * (1 + |y|) ^ d := by
        rw [mul_pow]
        ring
  rw [norm_mul]
  calc
    ‖originalContourKernel ((N : ℂ) + originalContourPoint y)‖ *
        ‖f y‖ ≤
      ((2 * Real.pi) * (1 / 2 : ℝ) ^ N *
        Real.exp (-Real.pi * |y|)) *
      (C * (1 + (N : ℝ)) ^ d * (1 + |y|) ^ d) :=
      mul_le_mul (originalRightContourKernel_norm_le N y) hfp
        (norm_nonneg _) (by positivity)
    _ = (2 * Real.pi * C) *
        ((1 + (N : ℝ)) ^ d * (1 / 2 : ℝ) ^ N) *
        ((1 + |y|) ^ d * Real.exp (-Real.pi * |y|)) := by ring

lemma integrable_originalRightKernel_mul
    {C : ℝ} (hC : 0 ≤ C) (d N : ℕ) (f : ℝ → ℂ)
    (hfm : AEStronglyMeasurable f volume)
    (hf : ∀ y, ‖f y‖ ≤ C * (1 + (N : ℝ) + |y|) ^ d) :
    Integrable (fun y : ℝ =>
      originalContourKernel ((N : ℂ) + originalContourPoint y) * f y) := by
  have hm :=
    (original_integrable_one_add_abs_pow_exp d Real.pi_pos).const_mul
      ((2 * Real.pi * C) *
        ((1 + (N : ℝ)) ^ d * (1 / 2 : ℝ) ^ N))
  apply hm.mono'
    ((continuous_originalRightContourKernel N).aestronglyMeasurable.mul hfm)
  exact Filter.Eventually.of_forall
    (originalRightKernel_mul_norm_le hC d N f hf)

lemma originalRightKernel_absoluteIntegral_le
    {C : ℝ} (hC : 0 ≤ C) (d N : ℕ) (f : ℝ → ℂ)
    (hfm : AEStronglyMeasurable f volume)
    (hf : ∀ y, ‖f y‖ ≤ C * (1 + (N : ℝ) + |y|) ^ d) :
    (∫ y : ℝ,
      ‖originalContourKernel ((N : ℂ) + originalContourPoint y) * f y‖) ≤
      (2 * Real.pi * C) *
        ((1 + (N : ℝ)) ^ d * (1 / 2 : ℝ) ^ N) *
        (∫ y : ℝ, (1 + |y|) ^ d * Real.exp (-Real.pi * |y|)) := by
  have hF := integrable_originalRightKernel_mul hC d N f hfm hf
  have hm :=
    (original_integrable_one_add_abs_pow_exp d Real.pi_pos).const_mul
      ((2 * Real.pi * C) *
        ((1 + (N : ℝ)) ^ d * (1 / 2 : ℝ) ^ N))
  calc
    (∫ y : ℝ,
        ‖originalContourKernel ((N : ℂ) + originalContourPoint y) * f y‖) ≤
      ∫ y : ℝ,
        ((2 * Real.pi * C) *
          ((1 + (N : ℝ)) ^ d * (1 / 2 : ℝ) ^ N)) *
          ((1 + |y|) ^ d * Real.exp (-Real.pi * |y|)) :=
      integral_mono_ae hF.norm hm
        (Filter.Eventually.of_forall
          (originalRightKernel_mul_norm_le hC d N f hf))
    _ = (2 * Real.pi * C) *
        ((1 + (N : ℝ)) ^ d * (1 / 2 : ℝ) ^ N) *
        (∫ y : ℝ, (1 + |y|) ^ d * Real.exp (-Real.pi * |y|)) :=
      integral_const_mul _ _

lemma originalRightDecay_tendsto_zero (d : ℕ) :
    Tendsto (fun N : ℕ =>
      (1 + (N : ℝ)) ^ d * (1 / 2 : ℝ) ^ N) atTop (𝓝 0) := by
  have hs :=
    (summable_pow_mul_geometric_of_norm_lt_one d
      (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_atTop_zero
  have ht :
      Tendsto (fun N : ℕ =>
        ((N + 1 : ℕ) : ℝ) ^ d * (1 / 2 : ℝ) ^ (N + 1))
        atTop (𝓝 0) :=
    hs.comp (tendsto_add_atTop_nat 1)
  have heq :
      (fun N : ℕ => (1 + (N : ℝ)) ^ d * (1 / 2 : ℝ) ^ N) =
      (fun N : ℕ =>
        2 * (((N + 1 : ℕ) : ℝ) ^ d *
          (1 / 2 : ℝ) ^ (N + 1))) := by
    funext N
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  rw [heq]
  simpa only [mul_zero] using ht.const_mul 2

lemma originalRightKernel_absoluteIntegral_tendsto_zero
    {C : ℝ} (hC : 0 ≤ C) (d : ℕ) (f : ℕ → ℝ → ℂ)
    (hfm : ∀ N, AEStronglyMeasurable (f N) volume)
    (hf : ∀ N y, ‖f N y‖ ≤ C * (1 + (N : ℝ) + |y|) ^ d) :
    Tendsto (fun N : ℕ =>
      ∫ y : ℝ,
        ‖originalContourKernel ((N : ℂ) + originalContourPoint y) * f N y‖)
      atTop (𝓝 0) := by
  have hlim :
      Tendsto (fun N : ℕ =>
        (2 * Real.pi * C) *
          ((1 + (N : ℝ)) ^ d * (1 / 2 : ℝ) ^ N) *
          (∫ y : ℝ, (1 + |y|) ^ d * Real.exp (-Real.pi * |y|)))
        atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (((originalRightDecay_tendsto_zero d).const_mul
        (2 * Real.pi * C)).mul_const
          (∫ y : ℝ, (1 + |y|) ^ d * Real.exp (-Real.pi * |y|)))
  exact squeeze_zero
    (fun N => integral_nonneg (fun y => norm_nonneg _))
    (fun N => originalRightKernel_absoluteIntegral_le
      hC d N (f N) (hfm N) (hf N))
    hlim

end
end Li2

end
