module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Tactic

set_option backward.privateInPublic true

@[expose] public section

open MeasureTheory
namespace Li2
noncomputable section

/-- The explicit primitive; its value at zero is zero for every `x`. -/
def logNormIntegralPrimitive (x t : ℝ) : ℝ :=
  (t / 2) * Real.log (t ^ 2 + x ^ 2) - t +
    x * Real.arctan (t / x)

lemma log_norm_real_add_imag (t x : ℝ) :
    Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖ =
      (1 / 2 : ℝ) * Real.log (t ^ 2 + x ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_add_mul_I,
    Real.log_sqrt (add_nonneg (sq_nonneg t) (sq_nonneg x))]
  ring

@[simp] lemma log_norm_real_add_imag_zero (t : ℝ) :
    Real.log ‖(t : ℂ) + (0 : ℂ) * Complex.I‖ = Real.log t := by
  simp [Complex.norm_real, Real.norm_eq_abs, Real.log_abs]

lemma real_add_imag_ne_zero {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (t : ℂ) + (x : ℂ) * Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  have hx0 : x = 0 := by simpa using hi
  exact hx.ne' hx0

lemma continuous_log_norm_real_add_imag {x : ℝ} (hx : 0 < x) :
    Continuous (fun t : ℝ =>
      Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) := by
  have hz : Continuous (fun t : ℝ =>
      (t : ℂ) + (x : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  exact hz.norm.log (fun t =>
    norm_ne_zero_iff.mpr (real_add_imag_ne_zero hx t))

lemma hasDerivAt_logNormIntegralPrimitive {x : ℝ}
    (hx : 0 < x) (t : ℝ) :
    HasDerivAt (logNormIntegralPrimitive x)
      (Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) t := by
  have hx0 : x ≠ 0 := hx.ne'
  have hQ : t ^ 2 + x ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg t) (pow_pos hx 2))
  have hquot : 1 + (t / x) ^ 2 = (t ^ 2 + x ^ 2) / x ^ 2 := by
    field_simp [hx0]
    <;> ring
  have hlog : HasDerivAt
      (fun s : ℝ => Real.log (s ^ 2 + x ^ 2))
      (2 * t / (t ^ 2 + x ^ 2)) t := by
    convert! (((hasDerivAt_id t).pow 2).add_const (x ^ 2)).log hQ using 1
    <;> norm_num
    <;> ring
  have hatan : HasDerivAt
      (fun s : ℝ => x * Real.arctan (s / x))
      (x ^ 2 / (t ^ 2 + x ^ 2)) t := by
    convert! (((hasDerivAt_id t).div_const x).arctan).const_mul x using 1
    dsimp only [id_eq]
    rw [hquot]
    field_simp [hx0, hQ]
    <;> ring
  have h := ((((hasDerivAt_id t).div_const 2).mul hlog).sub
    (hasDerivAt_id t)).add hatan
  rw [log_norm_real_add_imag]
  convert! h using 1
  <;> dsimp [logNormIntegralPrimitive]
  <;> field_simp [hQ]
  <;> ring

lemma intervalIntegrable_log_norm_real_add_imag
    {x : ℝ} (hx : 0 ≤ x) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) volume a b := by
  by_cases hx0 : x = 0
  · subst x
    simpa only [Complex.ofReal_zero, log_norm_real_add_imag_zero] using
      (intervalIntegral.intervalIntegrable_log' (a := a) (b := b))
  · exact (continuous_log_norm_real_add_imag
      (lt_of_le_of_ne hx (Ne.symm hx0))).intervalIntegrable a b

lemma integral_log_norm_real_add_imag_of_pos
    {x : ℝ} (hx : 0 < x) (b : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..b,
      Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) =
      (b / 2) * Real.log (b ^ 2 + x ^ 2) - b +
        x * Real.arctan (b / x) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := b) (f := logNormIntegralPrimitive x)
    (f' := fun t : ℝ => Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖)
    (fun t _ => hasDerivAt_logNormIntegralPrimitive hx t)
    ((continuous_log_norm_real_add_imag hx).intervalIntegrable 0 b)
  simpa [logNormIntegralPrimitive] using h

/-- The integral from GLOBAL-INTEGRAL-v1, Section 2, with both boundary cases. -/
theorem integral_log_norm_real_add_imag
    {x b : ℝ} (hx : 0 ≤ x) (_hb : 0 ≤ b) :
    (∫ t : ℝ in (0 : ℝ)..b,
      Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) =
      (b / 2) * Real.log (b ^ 2 + x ^ 2) - b +
        x * Real.arctan (b / x) := by
  by_cases hb0 : b = 0
  · subst b
    simp
  by_cases hx0 : x = 0
  · subst x
    simp only [Complex.ofReal_zero, log_norm_real_add_imag_zero]
    rw [integral_log_from_zero]
    simp only [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, zero_mul]
    rw [Real.log_pow]
    ring
  · exact integral_log_norm_real_add_imag_of_pos
      (lt_of_le_of_ne hx (Ne.symm hx0)) b

end
end Li2

end
