module
public import Li2Unified.Modular.Positive.Packed.P086
public import Li2Unified.Modular.Base.OriginalContourIntegrable
public import Li2Unified.Modular.Base.OriginalContourRational

set_option backward.privateInPublic true

@[expose] public section

section
/-! The actual upper and lower star densities are integrable on positive time. -/

open Polynomial MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

private lemma continuous_up_density_integrand (d : ℕ) (F : ℚ[X]) :
    Continuous (fun t : ℝ => density ⟨1, by decide⟩ t *
      Li2.originalComplexQuotient d F (point ⟨1, by decide⟩ t)) := by
  have hp : Continuous (fun t : ℝ => point ⟨1, by decide⟩ t) := by
    simp only [point_up]
    exact Li2.continuous_originalContourPoint
  have hder : Continuous (fun t : ℝ =>
      deriv (fun z => power z * kappaPlus z) (point ⟨1, by decide⟩ t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hz : Complex.sin ((Real.pi : ℂ) * point ⟨1, by decide⟩ t) ≠ 0 := by
      simpa only [point_up] using Li2.originalContour_sin_ne_zero t
    exact ((upperKernel_analyticAt_of_sin_ne hz).deriv).continuousAt.comp
      (f := fun s : ℝ => point ⟨1, by decide⟩ s) hp.continuousAt
  have hq : Continuous (fun t : ℝ =>
      Li2.originalComplexQuotient d F (point ⟨1, by decide⟩ t)) := by
    simpa only [point_up] using Li2.continuous_originalComplexQuotient_vertical d F
  change Continuous (fun t : ℝ =>
    ((Complex.I * point ⟨1, by decide⟩ t) *
      deriv (fun z => power z * kappaPlus z) (point ⟨1, by decide⟩ t)) *
      Li2.originalComplexQuotient d F (point ⟨1, by decide⟩ t))
  exact ((continuous_const.mul hp).mul hder).mul hq

private lemma continuous_down_density_integrand (d : ℕ) (F : ℚ[X]) :
    Continuous (fun t : ℝ => density ⟨2, by decide⟩ t *
      Li2.originalComplexQuotient d F (point ⟨2, by decide⟩ t)) := by
  have hp : Continuous (fun t : ℝ => point ⟨2, by decide⟩ t) := by
    simp only [point_down]
    exact Li2.continuous_originalContourPoint.comp continuous_neg
  have hder : Continuous (fun t : ℝ =>
      deriv (fun z => power z * kappaMinus z) (point ⟨2, by decide⟩ t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hz : Complex.sin ((Real.pi : ℂ) * point ⟨2, by decide⟩ t) ≠ 0 := by
      simpa only [point_down] using Li2.originalContour_sin_ne_zero (-t)
    exact ((lowerKernel_analyticAt_of_sin_ne hz).deriv).continuousAt.comp
      (f := fun s : ℝ => point ⟨2, by decide⟩ s) hp.continuousAt
  have hq : Continuous (fun t : ℝ =>
      Li2.originalComplexQuotient d F (point ⟨2, by decide⟩ t)) := by
    simpa only [point_down] using
      (Li2.continuous_originalComplexQuotient_vertical d F).comp continuous_neg
  change Continuous (fun t : ℝ =>
    ((-Complex.I * point ⟨2, by decide⟩ t) *
      deriv (fun z => power z * kappaMinus z) (point ⟨2, by decide⟩ t)) *
      Li2.originalComplexQuotient d F (point ⟨2, by decide⟩ t))
  exact ((continuous_const.mul hp).mul hder).mul hq

lemma up_density_norm_le (d : ℕ) (F : ℚ[X]) (t : ℝ) (ht : 0 ≤ t) :
    ‖density ⟨1, by decide⟩ t *
      Li2.originalComplexQuotient d F (point ⟨1, by decide⟩ t)‖ ≤
      (Real.log 2 + 2 * Real.pi) * Li2.originalCoefficientNormSum F *
        ((1 + t) ^ (F.natDegree + 1) * Real.exp (-2 * Real.pi * t)) := by
  let z : ℂ := point ⟨1, by decide⟩ t
  have hz : ‖z‖ ≤ 1 + t := by
    change ‖point ⟨1, by decide⟩ t‖ ≤ 1 + t
    rw [point_up]
    have h := Li2.originalContourPoint_norm_le t
    rw [abs_of_nonneg ht] at h
    linarith
  have hq : ‖Li2.originalComplexQuotient d F z‖ ≤
      Li2.originalCoefficientNormSum F * (1 + t) ^ F.natDegree := by
    change ‖Li2.originalComplexQuotient d F (point ⟨1, by decide⟩ t)‖ ≤ _
    rw [point_up]
    simpa only [abs_of_nonneg ht] using
      Li2.originalComplexQuotient_vertical_polynomial_growth d F t
  have hd := upperKernel_deriv_upper_norm_le t
  change ‖(Complex.I * z * deriv (fun z => power z * kappaPlus z) z) *
    Li2.originalComplexQuotient d F z‖ ≤ _
  calc
    _ = ‖z‖ * ‖deriv (fun z => power z * kappaPlus z) z‖ *
          ‖Li2.originalComplexQuotient d F z‖ := by
      simp only [norm_mul, Complex.norm_I, one_mul]
    _ ≤ (1 + t) * ((Real.log 2 + 2 * Real.pi) * Real.exp (-2 * Real.pi * t)) *
          (Li2.originalCoefficientNormSum F * (1 + t) ^ F.natDegree) := by
      gcongr
    _ = _ := by rw [pow_succ]; ring

lemma down_density_norm_le (d : ℕ) (F : ℚ[X]) (t : ℝ) (ht : 0 ≤ t) :
    ‖density ⟨2, by decide⟩ t *
      Li2.originalComplexQuotient d F (point ⟨2, by decide⟩ t)‖ ≤
      (Real.log 2 + 2 * Real.pi) * Li2.originalCoefficientNormSum F *
        ((1 + t) ^ (F.natDegree + 1) * Real.exp (-2 * Real.pi * t)) := by
  let z : ℂ := point ⟨2, by decide⟩ t
  have hz : ‖z‖ ≤ 1 + t := by
    change ‖point ⟨2, by decide⟩ t‖ ≤ 1 + t
    rw [point_down]
    have h := Li2.originalContourPoint_norm_le (-t)
    rw [abs_neg, abs_of_nonneg ht] at h
    linarith
  have hq : ‖Li2.originalComplexQuotient d F z‖ ≤
      Li2.originalCoefficientNormSum F * (1 + t) ^ F.natDegree := by
    change ‖Li2.originalComplexQuotient d F (point ⟨2, by decide⟩ t)‖ ≤ _
    rw [point_down]
    simpa only [abs_neg, abs_of_nonneg ht] using
      Li2.originalComplexQuotient_vertical_polynomial_growth d F (-t)
  have hd := lowerKernel_deriv_lower_norm_le t
  change ‖(-Complex.I * z * deriv (fun z => power z * kappaMinus z) z) *
    Li2.originalComplexQuotient d F z‖ ≤ _
  calc
    _ = ‖z‖ * ‖deriv (fun z => power z * kappaMinus z) z‖ *
          ‖Li2.originalComplexQuotient d F z‖ := by
      simp only [norm_mul, norm_neg, Complex.norm_I, one_mul]
    _ ≤ (1 + t) * ((Real.log 2 + 2 * Real.pi) * Real.exp (-2 * Real.pi * t)) *
          (Li2.originalCoefficientNormSum F * (1 + t) ^ F.natDegree) := by
      gcongr
    _ = _ := by rw [pow_succ]; ring

lemma up_density_integrableOn (d : ℕ) (F : ℚ[X]) :
    IntegrableOn (fun t : ℝ => density ⟨1, by decide⟩ t *
      Li2.originalComplexQuotient d F (point ⟨1, by decide⟩ t)) (Ioi 0) := by
  let C : ℝ := (Real.log 2 + 2 * Real.pi) * Li2.originalCoefficientNormSum F
  have hm : Integrable (fun t : ℝ =>
      C * ((1 + |t|) ^ (F.natDegree + 1) * Real.exp (-(2 * Real.pi) * |t|))) :=
    (Li2.original_integrable_one_add_abs_pow_exp (F.natDegree + 1)
      (by positivity : 0 < 2 * Real.pi)).const_mul C
  apply hm.integrableOn.mono'
    (continuous_up_density_integrand d F).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  change ‖density ⟨1, by decide⟩ t *
    Li2.originalComplexQuotient d F (point ⟨1, by decide⟩ t)‖ ≤ _
  dsimp [C]
  rw [abs_of_pos ht]
  simpa only [show -(2 * Real.pi) * t = -2 * Real.pi * t by ring] using
    up_density_norm_le d F t ht.le

lemma down_density_integrableOn (d : ℕ) (F : ℚ[X]) :
    IntegrableOn (fun t : ℝ => density ⟨2, by decide⟩ t *
      Li2.originalComplexQuotient d F (point ⟨2, by decide⟩ t)) (Ioi 0) := by
  let C : ℝ := (Real.log 2 + 2 * Real.pi) * Li2.originalCoefficientNormSum F
  have hm : Integrable (fun t : ℝ =>
      C * ((1 + |t|) ^ (F.natDegree + 1) * Real.exp (-(2 * Real.pi) * |t|))) :=
    (Li2.original_integrable_one_add_abs_pow_exp (F.natDegree + 1)
      (by positivity : 0 < 2 * Real.pi)).const_mul C
  apply hm.integrableOn.mono'
    (continuous_down_density_integrand d F).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  change ‖density ⟨2, by decide⟩ t *
    Li2.originalComplexQuotient d F (point ⟨2, by decide⟩ t)‖ ≤ _
  dsimp [C]
  rw [abs_of_pos ht]
  simpa only [show -(2 * Real.pi) * t = -2 * Real.pi * t by ring] using
    down_density_norm_le d F t ht.le

end
end Li2Unified.Proofs.Contour

end


end
