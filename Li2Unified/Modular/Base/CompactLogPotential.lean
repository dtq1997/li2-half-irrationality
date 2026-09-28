module
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Tactic.Linarith

set_option backward.privateInPublic true

@[expose] public section

open MeasureTheory Set
namespace Li2
noncomputable section

lemma locallyIntegrable_real_log : LocallyIntegrable Real.log volume := by
  intro x
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le
    (show x - 1 ≤ x + 1 by linarith)).mp
    (intervalIntegral.intervalIntegrable_log' (a := x - 1) (b := x + 1))

/-- The real logarithmic potential, without any normalization on the density. -/
def compactLogPotential (ρ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t : ℝ, ρ t * Real.log |x - t|

/-- The defining integrand is integrable at every point, including support points. -/
theorem integrable_compactLogPotential_integrand
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρsupport : HasCompactSupport ρ)
    (x : ℝ) :
    Integrable (fun t : ℝ => ρ t * Real.log |x - t|) volume := by
  simpa only [MeasureTheory.ConvolutionExistsAt,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul, Real.log_abs] using
    (hρsupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      hρ locallyIntegrable_real_log x)

/-- A continuous compactly supported real density has a continuous logarithmic potential. -/
theorem continuous_compactLogPotential
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρsupport : HasCompactSupport ρ) :
    Continuous (compactLogPotential ρ) := by
  have h := hρsupport.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    hρ locallyIntegrable_real_log
  change Continuous (fun x : ℝ => ∫ t : ℝ, ρ t * Real.log (x - t)) at h
  change Continuous (fun x : ℝ => ∫ t : ℝ, ρ t * Real.log |x - t|)
  simpa only [Real.log_abs] using h

end
end Li2

end
