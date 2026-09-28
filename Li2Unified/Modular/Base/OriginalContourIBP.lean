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

lemma continuous_originalContourKernel_vertical :
    Continuous (fun y : ℝ => originalContourKernel (originalContourPoint y)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (originalContourKernel_hasDerivAt y).continuousAt.comp
    continuous_originalContourPoint.continuousAt

lemma originalContourPoint_hasDerivAt (y : ℝ) :
    HasDerivAt originalContourPoint Complex.I y := by
  have hr : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) y := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      (Complex.ofRealCLM.hasDerivAt (x := y))
  simpa only [originalContourPoint, one_mul] using!
    (hr.mul_const Complex.I).const_add (1 / 2 : ℂ)

lemma originalContourG_comp_hasDerivAt (d : ℕ) (F : ℚ[X]) (y : ℝ) :
    HasDerivAt (fun t : ℝ => originalContourG d F (originalContourPoint t))
      (deriv (originalContourG d F) (originalContourPoint y) * Complex.I) y := by
  simpa only [Function.comp_apply] using!
    (originalContourG_hasDerivAt_of_den_ne_zero d F
      (D_eval₂_complex_vertical_ne_zero d y)).differentiableAt.hasDerivAt.comp y
        (originalContourPoint_hasDerivAt y)

end
end Li2

end
