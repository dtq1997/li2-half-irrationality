module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic

set_option backward.privateInPublic true

@[expose] public section

namespace Li2
noncomputable section

def originalContourPoint (y : ℝ) : ℂ := (1 / 2 : ℂ) + (y : ℂ) * Complex.I

def originalContourPower (z : ℂ) : ℂ := Complex.exp (-(Real.log 2 : ℂ) * z)

def originalContourKernel (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * originalContourPower z / Complex.sin ((Real.pi : ℂ) * z)

def originalContourWeight (y : ℝ) : ℂ :=
  originalContourPoint y * originalContourPower (originalContourPoint y) *
    (-(Real.log 2 : ℂ) + Complex.I * (Real.pi : ℂ) * (Real.tanh (Real.pi * y) : ℂ)) /
      (2 * (Real.cosh (Real.pi * y) : ℂ))

lemma originalContour_vertical_arg (y : ℝ) :
    (Real.pi : ℂ) * originalContourPoint y =
      (Real.pi : ℂ) / 2 + ((Real.pi * y : ℝ) : ℂ) * Complex.I := by
  unfold originalContourPoint
  push_cast
  ring

lemma originalContour_sin (y : ℝ) :
    Complex.sin ((Real.pi : ℂ) * originalContourPoint y) =
      (Real.cosh (Real.pi * y) : ℂ) := by
  rw [originalContour_vertical_arg, Complex.sin_add_mul_I]
  simp only [Complex.sin_pi_div_two, Complex.cos_pi_div_two,
    one_mul, zero_mul, add_zero]
  exact (Complex.ofReal_cosh (Real.pi * y)).symm

lemma originalContour_cos (y : ℝ) :
    Complex.cos ((Real.pi : ℂ) * originalContourPoint y) =
      -((Real.sinh (Real.pi * y) : ℂ) * Complex.I) := by
  rw [originalContour_vertical_arg, Complex.cos_add_mul_I]
  simp only [Complex.cos_pi_div_two, Complex.sin_pi_div_two,
    zero_mul, one_mul, zero_sub]
  rw [← Complex.ofReal_sinh]

lemma originalContour_cosh_ne_zero (y : ℝ) :
    (Real.cosh (Real.pi * y) : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Real.cosh_pos (Real.pi * y)))

lemma originalContour_sin_ne_zero (y : ℝ) :
    Complex.sin ((Real.pi : ℂ) * originalContourPoint y) ≠ 0 := by
  rw [originalContour_sin]
  exact originalContour_cosh_ne_zero y

lemma originalContourKernel_vertical (y : ℝ) :
    originalContourKernel (originalContourPoint y) =
      (Real.pi : ℂ) * originalContourPower (originalContourPoint y) /
        (Real.cosh (Real.pi * y) : ℂ) := by
  unfold originalContourKernel
  rw [originalContour_sin]

lemma originalContourKernel_hasDerivAt (y : ℝ) :
    HasDerivAt originalContourKernel
      ((Real.pi : ℂ) * originalContourPower (originalContourPoint y) *
        (-(Real.log 2 : ℂ) + Complex.I * (Real.pi : ℂ) *
          (Real.tanh (Real.pi * y) : ℂ)) /
        (Real.cosh (Real.pi * y) : ℂ)) (originalContourPoint y) := by
  have he : HasDerivAt originalContourPower
      (originalContourPower (originalContourPoint y) * (-(Real.log 2 : ℂ)))
      (originalContourPoint y) := by
    simpa only [originalContourPower, mul_one] using!
      ((hasDerivAt_id (originalContourPoint y)).const_mul (-(Real.log 2 : ℂ))).cexp
  have hs : HasDerivAt (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z))
      (Complex.cos ((Real.pi : ℂ) * originalContourPoint y) * (Real.pi : ℂ))
      (originalContourPoint y) := by
    simpa only [mul_one] using!
      ((hasDerivAt_id (originalContourPoint y)).const_mul (Real.pi : ℂ)).csin
  have hk := (he.const_mul (Real.pi : ℂ)).fun_div hs (originalContour_sin_ne_zero y)
  change HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * originalContourPower z /
    Complex.sin ((Real.pi : ℂ) * z)) _ _
  apply hk.congr_deriv
  rw [originalContour_sin, originalContour_cos, Real.tanh_eq_sinh_div_cosh]
  rw [Complex.ofReal_div]
  apply (div_eq_div_iff
    (pow_ne_zero 2 (originalContour_cosh_ne_zero y))
    (originalContour_cosh_ne_zero y)).2
  linear_combination
    (-((Real.pi : ℂ) ^ 2) * originalContourPower (originalContourPoint y) *
      Complex.I * (Real.cosh (Real.pi * y) : ℂ)) *
      (div_mul_cancel₀ (Real.sinh (Real.pi * y) : ℂ)
        (originalContour_cosh_ne_zero y))

lemma originalContourWeight_eq_deriv (y : ℝ) :
    originalContourWeight y = originalContourPoint y *
      deriv originalContourKernel (originalContourPoint y) / (2 * (Real.pi : ℂ)) := by
  rw [(originalContourKernel_hasDerivAt y).deriv]
  unfold originalContourWeight
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [originalContour_cosh_ne_zero y, hpi]
  <;> ring

lemma originalContourPower_norm (y : ℝ) :
    ‖originalContourPower (originalContourPoint y)‖ = Real.exp (-Real.log 2 / 2) := by
  rw [originalContourPower, Complex.norm_exp]
  congr 1
  simp only [originalContourPoint, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  ring

lemma originalContourPower_norm_le_one (y : ℝ) :
    ‖originalContourPower (originalContourPoint y)‖ ≤ 1 := by
  rw [originalContourPower_norm]
  apply Real.exp_le_one_iff.mpr
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

lemma originalContourPoint_norm_le (y : ℝ) :
    ‖originalContourPoint y‖ ≤ (1 / 2 : ℝ) + |y| := by
  calc
    ‖originalContourPoint y‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = (1 / 2 : ℝ) + |y| := by
      norm_num [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]

lemma originalContourFactor_norm_le (y : ℝ) :
    ‖-(Real.log 2 : ℂ) + Complex.I * (Real.pi : ℂ) *
      (Real.tanh (Real.pi * y) : ℂ)‖ ≤ Real.log 2 + Real.pi := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    _ ≤ ‖-(Real.log 2 : ℂ)‖ +
      ‖Complex.I * (Real.pi : ℂ) * (Real.tanh (Real.pi * y) : ℂ)‖ := norm_add_le _ _
    _ = Real.log 2 + Real.pi * |Real.tanh (Real.pi * y)| := by
      simp only [norm_neg, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hlog,
        abs_of_nonneg Real.pi_pos.le, one_mul]
    _ ≤ Real.log 2 + Real.pi := by
      nlinarith [Real.abs_tanh_lt_one (Real.pi * y), Real.pi_pos]

lemma originalCosh_reciprocal_decay (t : ℝ) :
    1 / (2 * Real.cosh t) ≤ Real.exp (-|t|) := by
  have h : Real.exp |t| ≤ 2 * Real.cosh t := by
    rw [← Real.cosh_abs t, Real.cosh_eq]
    linarith [Real.exp_pos (-|t|)]
  calc
    1 / (2 * Real.cosh t) ≤ 1 / Real.exp |t| :=
      one_div_le_one_div_of_le (Real.exp_pos _) h
    _ = Real.exp (-|t|) := by rw [Real.exp_neg, one_div]

lemma originalContourKernel_norm (y : ℝ) :
    ‖originalContourKernel (originalContourPoint y)‖ =
      Real.pi * Real.exp (-Real.log 2 / 2) / Real.cosh (Real.pi * y) := by
  rw [originalContourKernel_vertical, norm_div, norm_mul,
    Complex.norm_of_nonneg Real.pi_pos.le, originalContourPower_norm,
    Complex.norm_of_nonneg (Real.cosh_pos _).le]

lemma originalContourKernel_norm_le_exp (y : ℝ) :
    ‖originalContourKernel (originalContourPoint y)‖ ≤
      (2 * Real.pi) * Real.exp (-Real.pi * |y|) := by
  have he : Real.exp (-Real.log 2 / 2) ≤ 1 := by
    simpa only [originalContourPower_norm] using originalContourPower_norm_le_one y
  have hc : Real.cosh (Real.pi * y) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have habs : -|Real.pi * y| = -Real.pi * |y| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    ring
  calc
    ‖originalContourKernel (originalContourPoint y)‖ =
        Real.pi * Real.exp (-Real.log 2 / 2) / Real.cosh (Real.pi * y) :=
      originalContourKernel_norm y
    _ ≤ Real.pi / Real.cosh (Real.pi * y) := by
      apply div_le_div_of_nonneg_right _ (Real.cosh_pos _).le
      nlinarith [Real.pi_pos]
    _ = (2 * Real.pi) * (1 / (2 * Real.cosh (Real.pi * y))) := by
      field_simp [hc]
      <;> ring
    _ ≤ (2 * Real.pi) * Real.exp (-|Real.pi * y|) :=
      mul_le_mul_of_nonneg_left (originalCosh_reciprocal_decay _) (by positivity)
    _ = (2 * Real.pi) * Real.exp (-Real.pi * |y|) := by rw [habs]

lemma originalContourWeight_norm_le_exp (y : ℝ) :
    ‖originalContourWeight y‖ ≤
      (Real.log 2 + Real.pi) * (1 + |y|) * Real.exp (-Real.pi * |y|) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hp : ‖originalContourPoint y‖ *
      ‖originalContourPower (originalContourPoint y)‖ ≤ 1 + |y| := by
    calc
      _ ≤ ‖originalContourPoint y‖ * 1 :=
        mul_le_mul_of_nonneg_left (originalContourPower_norm_le_one y) (norm_nonneg _)
      _ ≤ 1 + |y| := by
        have h := originalContourPoint_norm_le y
        simp only [mul_one]
        linarith
  have hn : ‖originalContourPoint y‖ *
      ‖originalContourPower (originalContourPoint y)‖ *
      ‖-(Real.log 2 : ℂ) + Complex.I * (Real.pi : ℂ) *
        (Real.tanh (Real.pi * y) : ℂ)‖ ≤
        (1 + |y|) * (Real.log 2 + Real.pi) :=
    mul_le_mul hp (originalContourFactor_norm_le y) (norm_nonneg _) (by positivity)
  have hw : ‖originalContourWeight y‖ =
      (‖originalContourPoint y‖ * ‖originalContourPower (originalContourPoint y)‖ *
        ‖-(Real.log 2 : ℂ) + Complex.I * (Real.pi : ℂ) *
          (Real.tanh (Real.pi * y) : ℂ)‖) /
      (2 * Real.cosh (Real.pi * y)) := by
    simp only [originalContourWeight, norm_div, norm_mul,
      Complex.norm_of_nonneg (Real.cosh_pos (Real.pi * y)).le]
    norm_num
  have habs : -|Real.pi * y| = -Real.pi * |y| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    ring
  calc
    ‖originalContourWeight y‖ = _ := hw
    _ ≤ ((1 + |y|) * (Real.log 2 + Real.pi)) /
        (2 * Real.cosh (Real.pi * y)) :=
      div_le_div_of_nonneg_right hn (by positivity)
    _ = ((1 + |y|) * (Real.log 2 + Real.pi)) *
        (1 / (2 * Real.cosh (Real.pi * y))) := by ring
    _ ≤ ((1 + |y|) * (Real.log 2 + Real.pi)) * Real.exp (-|Real.pi * y|) :=
      mul_le_mul_of_nonneg_left (originalCosh_reciprocal_decay _) (by positivity)
    _ = (Real.log 2 + Real.pi) * (1 + |y|) * Real.exp (-Real.pi * |y|) := by
      rw [habs]
      ring

end
end Li2

end
