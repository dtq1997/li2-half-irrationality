module
public import Li2Unified.Modular.Base.OriginalContourCompensated
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option backward.privateInPublic true

@[expose] public section

open Polynomial MeasureTheory
open scoped BigOperators
namespace Li2
noncomputable section

lemma hasDerivAt_originalComplexEval (F : ℚ[X]) (z : ℂ) :
    HasDerivAt (fun w : ℂ => F.eval₂ (Rat.castHom ℂ) w)
      (F.derivative.eval₂ (Rat.castHom ℂ) z) z := by
  simpa only [Polynomial.eval₂_eq_eval_map, Polynomial.derivative_map] using
    (F.map (Rat.castHom ℂ)).hasDerivAt z

lemma originalContourG_eq_eval₂_div (d : ℕ) (F : ℚ[X]) (z : ℂ) :
    originalContourG d F z =
      (X * F).eval₂ (Rat.castHom ℂ) z / (D d).eval₂ (Rat.castHom ℂ) z := by
  simp only [originalContourG, originalComplexQuotient, eval₂_mul, eval₂_X]
  ring

def originalContourGDerivativeNumerator (d : ℕ) (F : ℚ[X]) : ℚ[X] :=
  (X * F).derivative * D d - (X * F) * (D d).derivative

lemma originalContourG_hasDerivAt_of_den_ne_zero (d : ℕ) (F : ℚ[X]) {z : ℂ}
    (hz : (D d).eval₂ (Rat.castHom ℂ) z ≠ 0) :
    HasDerivAt (originalContourG d F)
      ((originalContourGDerivativeNumerator d F).eval₂ (Rat.castHom ℂ) z /
        ((D d).eval₂ (Rat.castHom ℂ) z) ^ 2) z := by
  have he : originalContourG d F =
      (fun w : ℂ => (X * F).eval₂ (Rat.castHom ℂ) w /
        (D d).eval₂ (Rat.castHom ℂ) w) :=
    funext (originalContourG_eq_eval₂_div d F)
  rw [he]
  have hdiv := (hasDerivAt_originalComplexEval (X * F) z).fun_div
    (hasDerivAt_originalComplexEval (D d) z) hz
  convert hdiv using 1 <;>
    simp only [originalContourGDerivativeNumerator, eval₂_sub, eval₂_mul]

lemma originalContourG_deriv_vertical (d : ℕ) (F : ℚ[X]) (y : ℝ) :
    deriv (originalContourG d F) (originalContourPoint y) =
      (originalContourGDerivativeNumerator d F).eval₂ (Rat.castHom ℂ)
        (originalContourPoint y) /
      ((D d).eval₂ (Rat.castHom ℂ) (originalContourPoint y)) ^ 2 :=
  (originalContourG_hasDerivAt_of_den_ne_zero d F
    (D_eval₂_complex_vertical_ne_zero d y)).deriv

lemma continuous_originalContourKernel_vertical :
    Continuous (fun y : ℝ => originalContourKernel (originalContourPoint y)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (originalContourKernel_hasDerivAt y).continuousAt.comp
    continuous_originalContourPoint.continuousAt

lemma integrable_originalContourKernel_mul_eval₂ (F : ℚ[X]) :
    Integrable (fun y : ℝ => originalContourKernel (originalContourPoint y) *
      F.eval₂ (Rat.castHom ℂ) (originalContourPoint y)) := by
  have hm :=
    (original_integrable_one_add_abs_pow_exp F.natDegree Real.pi_pos).const_mul
      (2 * Real.pi * originalCoefficientNormSum F)
  apply hm.mono'
    (continuous_originalContourKernel_vertical.mul
      ((F.continuous_eval₂ (Rat.castHom ℂ)).comp continuous_originalContourPoint)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => by
    change ‖originalContourKernel (originalContourPoint y) *
      F.eval₂ (Rat.castHom ℂ) (originalContourPoint y)‖ ≤
        (2 * Real.pi * originalCoefficientNormSum F) *
          ((1 + |y|) ^ F.natDegree * Real.exp (-Real.pi * |y|))
    rw [norm_mul]
    calc
      _ ≤ ((2 * Real.pi) * Real.exp (-Real.pi * |y|)) *
          (originalCoefficientNormSum F * (1 + |y|) ^ F.natDegree) :=
        mul_le_mul (originalContourKernel_norm_le_exp y)
          (originalComplexEval_vertical_norm_le F y) (norm_nonneg _) (by positivity)
      _ = (2 * Real.pi * originalCoefficientNormSum F) *
          ((1 + |y|) ^ F.natDegree * Real.exp (-Real.pi * |y|)) := by ring)

lemma integrable_originalContourKernel_mul_eval₂_div_pow
    (d : ℕ) (F : ℚ[X]) (s : ℕ) :
    Integrable (fun y : ℝ => originalContourKernel (originalContourPoint y) *
      (F.eval₂ (Rat.castHom ℂ) (originalContourPoint y) /
        ((D d).eval₂ (Rat.castHom ℂ) (originalContourPoint y)) ^ s)) := by
  have hc : Continuous (fun y : ℝ => originalContourKernel (originalContourPoint y) *
      (F.eval₂ (Rat.castHom ℂ) (originalContourPoint y) /
        ((D d).eval₂ (Rat.castHom ℂ) (originalContourPoint y)) ^ s)) :=
    continuous_originalContourKernel_vertical.mul
      (((F.continuous_eval₂ (Rat.castHom ℂ)).comp continuous_originalContourPoint).div
        ((((D d).continuous_eval₂ (Rat.castHom ℂ)).comp continuous_originalContourPoint).pow s)
        (fun y => pow_ne_zero s (D_eval₂_complex_vertical_ne_zero d y)))
  apply (integrable_originalContourKernel_mul_eval₂ F).mono hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => by
    simp only [norm_mul, norm_div, norm_pow]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact div_le_self (norm_nonneg _) (one_le_pow₀ (D_eval₂_complex_norm_ge_one d y)))

lemma integrable_originalContourKernel_mul_G (d : ℕ) (F : ℚ[X]) :
    Integrable (fun y : ℝ => originalContourKernel (originalContourPoint y) *
      originalContourG d F (originalContourPoint y)) := by
  simpa only [originalContourG_eq_eval₂_div, pow_one] using
    integrable_originalContourKernel_mul_eval₂_div_pow d (X * F) 1

lemma integrable_originalContourKernel_mul_G_deriv (d : ℕ) (F : ℚ[X]) :
    Integrable (fun y : ℝ => originalContourKernel (originalContourPoint y) *
      deriv (originalContourG d F) (originalContourPoint y)) := by
  simpa only [originalContourG_deriv_vertical] using
    integrable_originalContourKernel_mul_eval₂_div_pow d
      (originalContourGDerivativeNumerator d F) 2

lemma originalContourKernel_deriv_mul_G_eq_weight (d : ℕ) (F : ℚ[X]) (y : ℝ) :
    deriv originalContourKernel (originalContourPoint y) *
      originalContourG d F (originalContourPoint y) =
      (2 * (Real.pi : ℂ)) * (originalContourWeight y *
        originalComplexQuotient d F (originalContourPoint y)) := by
  rw [originalContourG, originalContourWeight_eq_deriv]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hpi] <;> ring

lemma integrable_originalContourKernel_deriv_mul_G (d : ℕ) (F : ℚ[X]) :
    Integrable (fun y : ℝ => deriv originalContourKernel (originalContourPoint y) *
      originalContourG d F (originalContourPoint y)) := by
  have he :
      (fun y : ℝ => deriv originalContourKernel (originalContourPoint y) *
        originalContourG d F (originalContourPoint y)) =
      (fun y : ℝ => (2 * (Real.pi : ℂ)) * (originalContourWeight y *
        originalComplexQuotient d F (originalContourPoint y))) :=
    funext (originalContourKernel_deriv_mul_G_eq_weight d F)
  rw [he]
  exact (integrable_originalContourWeight_mul_quotient d F).const_mul _

lemma originalContourPoint_hasDerivAt (y : ℝ) :
    HasDerivAt originalContourPoint Complex.I y := by
  have hr : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) y := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      (Complex.ofRealCLM.hasDerivAt (x := y))
  simpa only [originalContourPoint, one_mul] using!
    (hr.mul_const Complex.I).const_add (1 / 2 : ℂ)

lemma originalContourKernel_comp_hasDerivAt (y : ℝ) :
    HasDerivAt (fun t : ℝ => originalContourKernel (originalContourPoint t))
      (deriv originalContourKernel (originalContourPoint y) * Complex.I) y := by
  simpa only [Function.comp_apply] using!
    (originalContourKernel_hasDerivAt y).differentiableAt.hasDerivAt.comp y
      (originalContourPoint_hasDerivAt y)

lemma originalContourG_comp_hasDerivAt (d : ℕ) (F : ℚ[X]) (y : ℝ) :
    HasDerivAt (fun t : ℝ => originalContourG d F (originalContourPoint t))
      (deriv (originalContourG d F) (originalContourPoint y) * Complex.I) y := by
  simpa only [Function.comp_apply] using!
    (originalContourG_hasDerivAt_of_den_ne_zero d F
      (D_eval₂_complex_vertical_ne_zero d y)).differentiableAt.hasDerivAt.comp y
        (originalContourPoint_hasDerivAt y)

theorem integral_originalContourKernel_mul_G_deriv_eq_neg (d : ℕ) (F : ℚ[X]) :
    (∫ y : ℝ, originalContourKernel (originalContourPoint y) *
      deriv (originalContourG d F) (originalContourPoint y)) =
      -(∫ y : ℝ, deriv originalContourKernel (originalContourPoint y) *
        originalContourG d F (originalContourPoint y)) := by
  let u : ℝ → ℂ := fun y => originalContourKernel (originalContourPoint y)
  let v : ℝ → ℂ := fun y => originalContourG d F (originalContourPoint y)
  let u' : ℝ → ℂ := fun y => deriv originalContourKernel (originalContourPoint y) * Complex.I
  let v' : ℝ → ℂ := fun y => deriv (originalContourG d F) (originalContourPoint y) * Complex.I
  have huv' : Integrable (u * v') := by
    convert (integrable_originalContourKernel_mul_G_deriv d F).mul_const Complex.I using 1
    funext y
    simp only [u, v', Pi.mul_apply]
    ring
  have hu'v : Integrable (u' * v) := by
    convert (integrable_originalContourKernel_deriv_mul_G d F).mul_const Complex.I using 1
    funext y
    simp only [u', v, Pi.mul_apply]
    ring
  have huv : Integrable (u * v) := by
    simpa only [u, v, Pi.mul_apply] using! integrable_originalContourKernel_mul_G d F
  have h := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := u) (v := v) (u' := u') (v' := v')
    (fun y _ => originalContourKernel_comp_hasDerivAt y)
    (fun y _ => originalContourG_comp_hasDerivAt d F y) huv' hu'v huv
  have hL : (fun y : ℝ => u y * v' y) =
      (fun y : ℝ => (originalContourKernel (originalContourPoint y) *
        deriv (originalContourG d F) (originalContourPoint y)) * Complex.I) := by
    funext y
    dsimp only [u, v']
    ring
  have hR : (fun y : ℝ => u' y * v y) =
      (fun y : ℝ => (deriv originalContourKernel (originalContourPoint y) *
        originalContourG d F (originalContourPoint y)) * Complex.I) := by
    funext y
    dsimp only [u', v]
    ring
  rw [hL, hR, MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const] at h
  apply mul_right_cancel₀ Complex.I_ne_zero
  simpa only [neg_mul] using h

theorem integral_originalContourKernel_mul_G_deriv_eq_weight (d : ℕ) (F : ℚ[X]) :
    (∫ y : ℝ, originalContourKernel (originalContourPoint y) *
      deriv (originalContourG d F) (originalContourPoint y)) =
      -(2 * (Real.pi : ℂ)) *
        (∫ y : ℝ, originalContourWeight y *
          originalComplexQuotient d F (originalContourPoint y)) := by
  rw [integral_originalContourKernel_mul_G_deriv_eq_neg]
  simp_rw [originalContourKernel_deriv_mul_G_eq_weight]
  simpa only [neg_mul] using congrArg Neg.neg
    (MeasureTheory.integral_const_mul (2 * (Real.pi : ℂ))
      (fun y : ℝ => originalContourWeight y *
        originalComplexQuotient d F (originalContourPoint y)))

theorem integral_originalContourWeight_mul_quotient_eq_neg_kernel (d : ℕ) (F : ℚ[X]) :
    (∫ y : ℝ, originalContourWeight y *
      originalComplexQuotient d F (originalContourPoint y)) =
      -(∫ y : ℝ, originalContourKernel (originalContourPoint y) *
        deriv (originalContourG d F) (originalContourPoint y)) / (2 * (Real.pi : ℂ)) := by
  symm
  apply (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
    (by exact_mod_cast Real.pi_ne_zero : (Real.pi : ℂ) ≠ 0))).mpr
  rw [integral_originalContourKernel_mul_G_deriv_eq_weight]
  ring

end
end Li2

end
