module
public import Li2Unified.Modular.Base.OriginalContourKernel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option backward.privateInPublic true

@[expose] public section

namespace Li2
noncomputable section


lemma complexSin_norm_sq (z : ℂ) :
    ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.sin_eq,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.normSq_add_mul_I]
  linear_combination
    (Real.sin z.re) ^ 2 * (Real.cosh_sq z.im) +
    (Real.sinh z.im) ^ 2 * (Real.sin_sq_add_cos_sq z.re)

lemma complexSinh_abs_im_le_norm_sin (z : ℂ) :
    Real.sinh |z.im| ≤ ‖Complex.sin z‖ := by
  rw [← Real.abs_sinh]
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs, complexSin_norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

lemma exp_quarter_le_sinh {t : ℝ} (ht : 1 ≤ t) :
    Real.exp t / 4 ≤ Real.sinh t := by
  have hp : 2 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hm : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [Real.sinh_eq]
  linarith

lemma complexSin_norm_ge_exp (z : ℂ) (hz : 1 ≤ |z.im|) :
    Real.exp |z.im| / 4 ≤ ‖Complex.sin z‖ :=
  (exp_quarter_le_sinh hz).trans (complexSinh_abs_im_le_norm_sin z)

lemma complexSin_pi_norm_ge_exp (z : ℂ) (hz : 1 ≤ |z.im|) :
    Real.exp (Real.pi * |z.im|) / 4 ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
  have him : |((Real.pi : ℂ) * z).im| = Real.pi * |z.im| := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, abs_mul, abs_of_pos Real.pi_pos]
  have ht : 1 ≤ Real.pi * |z.im| := by
    have hmul := mul_le_mul_of_nonneg_left hz Real.pi_pos.le
    linarith [Real.two_le_pi]
  have h := complexSin_norm_ge_exp ((Real.pi : ℂ) * z) (by rw [him]; exact ht)
  simpa only [him] using h

lemma complexSin_pi_reciprocal_norm_le_exp (z : ℂ) (hz : 1 ≤ |z.im|) :
    1 / ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ 4 * Real.exp (-Real.pi * |z.im|) := by
  calc
    1 / ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤
        1 / (Real.exp (Real.pi * |z.im|) / 4) :=
      one_div_le_one_div_of_le (by positivity) (complexSin_pi_norm_ge_exp z hz)
    _ = 4 * Real.exp (-Real.pi * |z.im|) := by
      rw [show -Real.pi * |z.im| = -(Real.pi * |z.im|) by ring, Real.exp_neg]
      field_simp [Real.exp_ne_zero] <;> ring

lemma originalContourPower_norm_general (z : ℂ) :
    ‖originalContourPower z‖ = Real.exp (-Real.log 2 * z.re) := by
  rw [originalContourPower, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]

lemma originalContourKernel_norm_le_exp_general (z : ℂ) (hz : 1 ≤ |z.im|) :
    ‖originalContourKernel z‖ ≤
      (4 * Real.pi) * Real.exp (-Real.log 2 * z.re) *
        Real.exp (-Real.pi * |z.im|) := by
  rw [originalContourKernel, norm_div, norm_mul,
    Complex.norm_of_nonneg Real.pi_pos.le, originalContourPower_norm_general]
  calc
    Real.pi * Real.exp (-Real.log 2 * z.re) / ‖Complex.sin ((Real.pi : ℂ) * z)‖ =
      (Real.pi * Real.exp (-Real.log 2 * z.re)) *
        (1 / ‖Complex.sin ((Real.pi : ℂ) * z)‖) := by ring
    _ ≤ (Real.pi * Real.exp (-Real.log 2 * z.re)) *
        (4 * Real.exp (-Real.pi * |z.im|)) :=
      mul_le_mul_of_nonneg_left (complexSin_pi_reciprocal_norm_le_exp z hz) (by positivity)
    _ = (4 * Real.pi) * Real.exp (-Real.log 2 * z.re) *
        Real.exp (-Real.pi * |z.im|) := by ring

end
end Li2

end
