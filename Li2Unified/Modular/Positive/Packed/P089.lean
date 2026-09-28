module
public import Li2Unified.Modular.Positive.Packed.P082
public import Li2Unified.Modular.Positive.Packed.P086
public import Li2Unified.Modular.Base.OriginalContourIBP

set_option backward.privateInPublic true

@[expose] public section

section
/-! Finite integration by parts on the genuine vertical arms. -/

open Polynomial MeasureTheory
open scoped Interval
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

private lemma vertical_G_deriv_continuous (d : ℕ) (F : ℚ[X]) :
    Continuous (fun y : ℝ =>
      deriv (Li2.originalContourG d F) (Li2.originalContourPoint y)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hz : 0 < (Li2.originalContourPoint y).re := by
    simp [Li2.originalContourPoint, Complex.add_re, Complex.mul_re]
  exact (Li2.analyticAt_originalContourG_deriv d F hz).continuousAt.comp
    (f := Li2.originalContourPoint) Li2.continuous_originalContourPoint.continuousAt

private lemma vertical_analytic_deriv_continuous (H : ℂ → ℂ)
    (hH : ∀ y : ℝ, AnalyticAt ℂ H (Li2.originalContourPoint y)) :
    Continuous (fun y : ℝ => deriv H (Li2.originalContourPoint y)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  exact ((hH y).deriv).continuousAt.comp
    (f := Li2.originalContourPoint) Li2.continuous_originalContourPoint.continuousAt

theorem vertical_finite_ibp (H : ℂ → ℂ)
    (hH : ∀ y : ℝ, AnalyticAt ℂ H (Li2.originalContourPoint y))
    (d : ℕ) (F : ℚ[X]) (a b : ℝ) :
    (∫ y in a..b,
      H (Li2.originalContourPoint y) *
        (deriv (Li2.originalContourG d F) (Li2.originalContourPoint y) * Complex.I)) =
      H (Li2.originalContourPoint b) *
        Li2.originalContourG d F (Li2.originalContourPoint b) -
      H (Li2.originalContourPoint a) *
        Li2.originalContourG d F (Li2.originalContourPoint a) -
      ∫ y in a..b,
        (deriv H (Li2.originalContourPoint y) * Complex.I) *
          Li2.originalContourG d F (Li2.originalContourPoint y) := by
  let u : ℝ → ℂ := fun y => H (Li2.originalContourPoint y)
  let v : ℝ → ℂ := fun y => Li2.originalContourG d F (Li2.originalContourPoint y)
  let u' : ℝ → ℂ := fun y => deriv H (Li2.originalContourPoint y) * Complex.I
  let v' : ℝ → ℂ := fun y =>
    deriv (Li2.originalContourG d F) (Li2.originalContourPoint y) * Complex.I
  have hu (y : ℝ) : HasDerivAt u (u' y) y := by
    simpa only [u, u', Function.comp_apply] using!
      ((hH y).differentiableAt.hasDerivAt.comp y (Li2.originalContourPoint_hasDerivAt y))
  have hv (y : ℝ) : HasDerivAt v (v' y) y := by
    exact Li2.originalContourG_comp_hasDerivAt d F y
  have hu' : IntervalIntegrable u' volume a b := by
    apply Continuous.intervalIntegrable
    exact (vertical_analytic_deriv_continuous H hH).mul_const _
  have hv' : IntervalIntegrable v' volume a b := by
    apply Continuous.intervalIntegrable
    exact (vertical_G_deriv_continuous d F).mul_const _
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun y _ => hu y) (fun y _ => hv y) hu' hv'

lemma upperKernel_vertical_analytic :
    ∀ y : ℝ, AnalyticAt ℂ (fun z => power z * kappaPlus z)
      (Li2.originalContourPoint y) := by
  intro y
  exact upperKernel_analyticAt_of_sin_ne (Li2.originalContour_sin_ne_zero y)

lemma lowerKernel_vertical_analytic :
    ∀ y : ℝ, AnalyticAt ℂ (fun z => power z * kappaMinus z)
      (Li2.originalContourPoint y) := by
  intro y
  exact lowerKernel_analyticAt_of_sin_ne (Li2.originalContour_sin_ne_zero y)

theorem upperLeftUpper_finite_ibp (d : ℕ) (F : ℚ[X]) (T : ℝ) :
    Complex.I * upperLeftUpperIntegral d F T =
      (power (Li2.originalContourPoint T) * kappaPlus (Li2.originalContourPoint T)) *
        Li2.originalContourG d F (Li2.originalContourPoint T) -
      (power (Li2.originalContourPoint 0) * kappaPlus (Li2.originalContourPoint 0)) *
        Li2.originalContourG d F (Li2.originalContourPoint 0) -
      ∫ y in (0 : ℝ)..T,
        (deriv (fun z => power z * kappaPlus z) (Li2.originalContourPoint y) *
          Complex.I) * Li2.originalContourG d F (Li2.originalContourPoint y) := by
  have h := vertical_finite_ibp (fun z => power z * kappaPlus z)
    upperKernel_vertical_analytic d F 0 T
  convert h using 1
  change Complex.I * (∫ y in (0 : ℝ)..T,
    (power (Li2.originalContourPoint y) * kappaPlus (Li2.originalContourPoint y)) *
      deriv (Li2.originalContourG d F) (Li2.originalContourPoint y)) = _
  rw [mul_comm Complex.I]
  simpa only [mul_assoc] using!
    (intervalIntegral.integral_mul_const (a := (0 : ℝ)) (b := T) (μ := volume)
      Complex.I (fun y : ℝ =>
        (power (Li2.originalContourPoint y) * kappaPlus (Li2.originalContourPoint y)) *
          deriv (Li2.originalContourG d F) (Li2.originalContourPoint y))).symm

theorem lowerLeftLower_finite_ibp (d : ℕ) (F : ℚ[X]) (T : ℝ) :
    Complex.I * lowerLeftLowerIntegral d F T =
      (power (Li2.originalContourPoint 0) * kappaMinus (Li2.originalContourPoint 0)) *
        Li2.originalContourG d F (Li2.originalContourPoint 0) -
      (power (Li2.originalContourPoint (-T)) * kappaMinus (Li2.originalContourPoint (-T))) *
        Li2.originalContourG d F (Li2.originalContourPoint (-T)) -
      ∫ y in (-T)..(0 : ℝ),
        (deriv (fun z => power z * kappaMinus z) (Li2.originalContourPoint y) *
          Complex.I) * Li2.originalContourG d F (Li2.originalContourPoint y) := by
  have h := vertical_finite_ibp (fun z => power z * kappaMinus z)
    lowerKernel_vertical_analytic d F (-T) 0
  convert h using 1
  change Complex.I * (∫ y in (-T)..(0 : ℝ),
    (power (Li2.originalContourPoint y) * kappaMinus (Li2.originalContourPoint y)) *
      deriv (Li2.originalContourG d F) (Li2.originalContourPoint y)) = _
  rw [mul_comm Complex.I]
  simpa only [mul_assoc] using!
    (intervalIntegral.integral_mul_const (a := -T) (b := (0 : ℝ)) (μ := volume)
      Complex.I (fun y : ℝ =>
        (power (Li2.originalContourPoint y) * kappaMinus (Li2.originalContourPoint y)) *
          deriv (Li2.originalContourG d F) (Li2.originalContourPoint y))).symm

end
end Li2Unified.Proofs.Contour

end

end
