module
public import Li2Unified.Modular.Positive.Packed.P080
public import Li2Unified.Modular.Base.OriginalContourIBP

set_option backward.privateInPublic true

@[expose] public section

section
/-! Exact splitting of the left vertical side at its real endpoint. -/

open Polynomial MeasureTheory Set
open scoped Interval
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

private lemma continuous_upperMultiplier : Continuous upperMultiplier := by
  unfold upperMultiplier
  fun_prop

private lemma continuous_lowerMultiplier : Continuous lowerMultiplier := by
  unfold lowerMultiplier
  fun_prop

private lemma continuous_vertical_G_deriv (d : ℕ) (F : ℚ[X]) :
    Continuous (fun y : ℝ => deriv (Li2.originalContourG d F) (Li2.originalContourPoint y)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hz : 0 < (Li2.originalContourPoint y).re := by
    have h : (Li2.originalContourPoint y).re = (1 / 2 : ℝ) := by
      simp [Li2.originalContourPoint, Complex.add_re, Complex.mul_re]
    rw [h]
    norm_num
  exact (Li2.analyticAt_originalContourG_deriv d F hz).continuousAt.comp
    (f := Li2.originalContourPoint) Li2.continuous_originalContourPoint.continuousAt

lemma continuous_upperLeftIntegrand (d : ℕ) (F : ℚ[X]) :
    Continuous (fun y : ℝ =>
      (power (point ⟨1, by decide⟩ y) * kappaPlus (point ⟨1, by decide⟩ y)) *
        deriv (Li2.originalContourG d F) (point ⟨1, by decide⟩ y)) := by
  have hc : Continuous (fun y : ℝ =>
      (upperMultiplier (Li2.originalContourPoint y) *
        Li2.originalContourKernel (Li2.originalContourPoint y)) *
        deriv (Li2.originalContourG d F) (Li2.originalContourPoint y)) :=
    ((continuous_upperMultiplier.comp Li2.continuous_originalContourPoint).mul
      Li2.continuous_originalContourKernel_vertical).mul
      (continuous_vertical_G_deriv d F)
  have heq : (fun y : ℝ =>
      (power (point ⟨1, by decide⟩ y) * kappaPlus (point ⟨1, by decide⟩ y)) *
        deriv (Li2.originalContourG d F) (point ⟨1, by decide⟩ y)) =
      (fun y : ℝ =>
        (upperMultiplier (Li2.originalContourPoint y) *
          Li2.originalContourKernel (Li2.originalContourPoint y)) *
          deriv (Li2.originalContourG d F) (Li2.originalContourPoint y)) := by
    funext y
    rw [point_up, show power (Li2.originalContourPoint y) *
      kappaPlus (Li2.originalContourPoint y) =
        upperMultiplier (Li2.originalContourPoint y) *
          Li2.originalContourKernel (Li2.originalContourPoint y) from
      kappaPlus_eq_kernel _ (Li2.originalContour_sin_ne_zero y)]
  rw [heq]
  exact hc

lemma continuous_lowerLeftIntegrand (d : ℕ) (F : ℚ[X]) :
    Continuous (fun y : ℝ =>
      (power (point ⟨1, by decide⟩ y) * kappaMinus (point ⟨1, by decide⟩ y)) *
        deriv (Li2.originalContourG d F) (point ⟨1, by decide⟩ y)) := by
  have hc : Continuous (fun y : ℝ =>
      (lowerMultiplier (Li2.originalContourPoint y) *
        Li2.originalContourKernel (Li2.originalContourPoint y)) *
        deriv (Li2.originalContourG d F) (Li2.originalContourPoint y)) :=
    ((continuous_lowerMultiplier.comp Li2.continuous_originalContourPoint).mul
      Li2.continuous_originalContourKernel_vertical).mul
      (continuous_vertical_G_deriv d F)
  have heq : (fun y : ℝ =>
      (power (point ⟨1, by decide⟩ y) * kappaMinus (point ⟨1, by decide⟩ y)) *
        deriv (Li2.originalContourG d F) (point ⟨1, by decide⟩ y)) =
      (fun y : ℝ =>
        (lowerMultiplier (Li2.originalContourPoint y) *
          Li2.originalContourKernel (Li2.originalContourPoint y)) *
          deriv (Li2.originalContourG d F) (Li2.originalContourPoint y)) := by
    funext y
    rw [point_up, show power (Li2.originalContourPoint y) *
      kappaMinus (Li2.originalContourPoint y) =
        lowerMultiplier (Li2.originalContourPoint y) *
          Li2.originalContourKernel (Li2.originalContourPoint y) from
      kappaMinus_eq_kernel _ (Li2.originalContour_sin_ne_zero y)]
  rw [heq]
  exact hc

def upperLeftLowerIntegral (d : ℕ) (F : ℚ[X]) (T : ℝ) : ℂ :=
  ∫ y : ℝ in (-T)..0,
    (power (point ⟨1, by decide⟩ y) * kappaPlus (point ⟨1, by decide⟩ y)) *
      deriv (Li2.originalContourG d F) (point ⟨1, by decide⟩ y)

def upperLeftUpperIntegral (d : ℕ) (F : ℚ[X]) (T : ℝ) : ℂ :=
  ∫ y : ℝ in 0..T,
    (power (point ⟨1, by decide⟩ y) * kappaPlus (point ⟨1, by decide⟩ y)) *
      deriv (Li2.originalContourG d F) (point ⟨1, by decide⟩ y)

def lowerLeftLowerIntegral (d : ℕ) (F : ℚ[X]) (T : ℝ) : ℂ :=
  ∫ y : ℝ in (-T)..0,
    (power (point ⟨1, by decide⟩ y) * kappaMinus (point ⟨1, by decide⟩ y)) *
      deriv (Li2.originalContourG d F) (point ⟨1, by decide⟩ y)

lemma upperLeftIntegral_split (d : ℕ) (F : ℚ[X]) (T : ℝ) :
    upperLeftIntegral d F T =
      upperLeftLowerIntegral d F T + upperLeftUpperIntegral d F T := by
  change (∫ y : ℝ in (-T)..T,
    (power (point ⟨1, by decide⟩ y) * kappaPlus (point ⟨1, by decide⟩ y)) *
      deriv (Li2.originalContourG d F) (point ⟨1, by decide⟩ y)) = _
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((continuous_upperLeftIntegrand d F).intervalIntegrable _ _)
    ((continuous_upperLeftIntegrand d F).intervalIntegrable _ _)).symm

lemma plainLowerLeft_eq_upper_add_lower (d : ℕ) (F : ℚ[X]) (T : ℝ) :
    plainLowerLeftIntegral d F T =
      upperLeftLowerIntegral d F T + lowerLeftLowerIntegral d F T := by
  let p : ℝ → ℂ := fun y =>
    (power (point ⟨1, by decide⟩ y) * kappaPlus (point ⟨1, by decide⟩ y)) *
      deriv (Li2.originalContourG d F) (point ⟨1, by decide⟩ y)
  let m : ℝ → ℂ := fun y =>
    (power (point ⟨1, by decide⟩ y) * kappaMinus (point ⟨1, by decide⟩ y)) *
      deriv (Li2.originalContourG d F) (point ⟨1, by decide⟩ y)
  have hp : IntervalIntegrable p volume (-T) 0 :=
    (continuous_upperLeftIntegrand d F).intervalIntegrable _ _
  have hm : IntervalIntegrable m volume (-T) 0 :=
    (continuous_lowerLeftIntegrand d F).intervalIntegrable _ _
  have hpoint (y : ℝ) :
      plainIntegrand d F (point ⟨1, by decide⟩ y) = p y + m y := by
    dsimp only [plainIntegrand, p, m]
    have hk := kappa_sum (point ⟨1, by decide⟩ y)
      (by rw [point_up]; exact Li2.originalContour_sin_ne_zero y)
    calc
      power (point ⟨1, by decide⟩ y) *
          deriv (Li2.originalContourG d F) (point ⟨1, by decide⟩ y) =
        (power (point ⟨1, by decide⟩ y) *
          (kappaPlus (point ⟨1, by decide⟩ y) +
            kappaMinus (point ⟨1, by decide⟩ y))) *
          deriv (Li2.originalContourG d F) (point ⟨1, by decide⟩ y) := by rw [hk]; ring
      _ = _ := by ring
  change (∫ y : ℝ in (-T)..0, plainIntegrand d F (point ⟨1, by decide⟩ y)) =
    (∫ y : ℝ in (-T)..0, p y) + (∫ y : ℝ in (-T)..0, m y)
  rw [← intervalIntegral.integral_add hp hm]
  exact congrArg (fun g : ℝ → ℂ => ∫ y : ℝ in (-T)..0, g y)
    (funext hpoint)

end
end Li2Unified.Proofs.Contour

end

end
