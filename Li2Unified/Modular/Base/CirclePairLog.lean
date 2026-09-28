module
public import Li2Unified.Modular.Base.CircleLogTools
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

set_option backward.privateInPublic true

@[expose] public section
open MeasureTheory Set Real intervalIntegral
namespace Li2
noncomputable section

lemma circle_log_integral (c a : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (∫ θ in (0 : ℝ)..2 * π, Real.log ‖circleMap c R θ - a‖) =
      2 * π * (Real.log R + log⁺ (R⁻¹ * ‖c - a‖)) := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := a) (c := c) hR
  rw [circleAverage_def, smul_eq_mul] at h
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  rw [← h, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]

lemma circle_log_integral_rev (c a : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (∫ θ in (0 : ℝ)..2 * π, Real.log ‖a - circleMap c R θ‖) =
      2 * π * (Real.log R + log⁺ (R⁻¹ * ‖c - a‖)) := by
  rw [← circle_log_integral c a hR]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [norm_sub_rev]

private lemma continuous_posLog_of_nonneg {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) : Continuous (fun x => log⁺ (f x)) := by
  have he : (fun x => log⁺ (f x)) = (fun x => Real.log (max 1 (f x))) :=
    funext (fun x => Real.posLog_eq_log_max_one (hf0 x))
  rw [he]
  exact (continuous_const.max hf).log
    (fun x => (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).ne')

private lemma circle_abs_log_eq (x : ℝ) : |Real.log x| = 2 * log⁺ x - Real.log x := by
  rw [Real.posLog_def]
  rcases le_total 0 (Real.log x) with h | h
  · rw [max_eq_right h, abs_of_nonneg h]; ring
  · rw [max_eq_left h, abs_of_nonpos h]; ring

lemma continuous_circle_log_row (c d : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun θ : ℝ => ∫ φ in (0 : ℝ)..2 * π,
      Real.log ‖circleMap c ε θ - circleMap d ε φ‖) := by
  have he : (fun θ : ℝ => ∫ φ in (0 : ℝ)..2 * π,
        Real.log ‖circleMap c ε θ - circleMap d ε φ‖) =
      (fun θ : ℝ => 2 * π * (Real.log ε + log⁺ (ε⁻¹ * ‖d - circleMap c ε θ‖))) :=
    funext (fun θ => circle_log_integral_rev d (circleMap c ε θ) hε.ne')
  rw [he]
  apply continuous_const.mul
  apply continuous_const.add
  apply continuous_posLog_of_nonneg
  · exact continuous_const.mul (continuous_const.sub (continuous_circleMap c ε)).norm
  · intro θ; positivity

/-- Joint absolute integrability is established before any Fubini use. -/
theorem integrable_circle_pair_log (c d : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℝ × ℝ => Real.log ‖circleMap c ε p.1 - circleMap d ε p.2‖)
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict (Ioc 0 (2 * π)))) := by
  let K : ℝ → ℝ → ℝ := fun θ φ => Real.log ‖circleMap c ε θ - circleMap d ε φ‖
  let P : ℝ → ℝ → ℝ := fun θ φ => log⁺ ‖circleMap c ε θ - circleMap d ε φ‖
  have hT : (0 : ℝ) ≤ 2 * π := by positivity
  have hK (θ : ℝ) : IntervalIntegrable (K θ) volume 0 (2 * π) := by
    simpa only [K, norm_sub_rev] using circle_log_integrable d (circleMap c ε θ) ε
  have hP : Continuous (Function.uncurry P) := by
    change Continuous (fun p : ℝ × ℝ => log⁺ ‖circleMap c ε p.1 - circleMap d ε p.2‖)
    apply continuous_posLog_of_nonneg
    · exact (((continuous_circleMap c ε).comp continuous_fst).sub
        ((continuous_circleMap d ε).comp continuous_snd)).norm
    · intro p; exact norm_nonneg _
  have hPi (θ : ℝ) : IntervalIntegrable (P θ) volume 0 (2 * π) :=
    (hP.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 (2 * π)
  have hN : Continuous (fun θ : ℝ => ∫ φ in (0 : ℝ)..2 * π, ‖K θ φ‖) := by
    have he : (fun θ : ℝ => ∫ φ in (0 : ℝ)..2 * π, ‖K θ φ‖) =
        (fun θ : ℝ => 2 * (∫ φ in (0 : ℝ)..2 * π, P θ φ) -
          (∫ φ in (0 : ℝ)..2 * π, K θ φ)) := by
      funext θ
      calc
        _ = ∫ φ in (0 : ℝ)..2 * π, 2 * P θ φ - K θ φ := by
          apply intervalIntegral.integral_congr
          intro φ _
          dsimp only [K, P]
          rw [Real.norm_eq_abs]
          exact circle_abs_log_eq _
        _ = _ := by
          rw [intervalIntegral.integral_sub ((hPi θ).const_mul 2) (hK θ),
            intervalIntegral.integral_const_mul]
    rw [he]
    exact (continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hP 0 (2 * π))).sub
        (continuous_circle_log_row c d hε)
  have hm : Measurable (fun p : ℝ × ℝ => K p.1 p.2) := by
    apply Real.measurable_log.comp
    exact (((continuous_circleMap c ε).comp continuous_fst).sub
      ((continuous_circleMap d ε).comp continuous_snd)).norm.measurable
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun θ =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp (hK θ))
  · have hi : IntegrableOn (fun θ : ℝ => ∫ φ in (0 : ℝ)..2 * π, ‖K θ φ‖)
        (Ioc (0 : ℝ) (2 * π)) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
        (hN.intervalIntegrable 0 (2 * π))
    simpa only [intervalIntegral.integral_of_le hT] using hi

theorem circle_pair_log_self (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..2 * π,
      Real.log ‖circleMap c ε θ - circleMap c ε φ‖) = (2 * π) ^ 2 * Real.log ε := by
  have hin (θ : ℝ) : (∫ φ in (0 : ℝ)..2 * π,
        Real.log ‖circleMap c ε θ - circleMap c ε φ‖) = 2 * π * Real.log ε := by
    rw [circle_log_integral_rev _ _ hε.ne', norm_sub_rev c, circleMap_sub_center,
      norm_circleMap_zero, abs_of_pos hε, inv_mul_cancel₀ hε.ne', Real.posLog_one, add_zero]
  simp_rw [hin]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

private lemma log_le_log_add_posLog {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    Real.log x ≤ Real.log ε + log⁺ (ε⁻¹ * x) := by
  have h1 : Real.log (ε⁻¹ * x) ≤ log⁺ (ε⁻¹ * x) := le_max_right _ _
  rw [Real.log_mul (inv_ne_zero hε.ne') hx.ne', Real.log_inv] at h1
  linarith

theorem circle_pair_log_lower (c d : ℂ) {ε : ℝ} (hε : 0 < ε) (hne : c ≠ d) :
    (2 * π) ^ 2 * Real.log ‖c - d‖ ≤ ∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..2 * π,
      Real.log ‖circleMap c ε θ - circleMap d ε φ‖ := by
  have hin (θ : ℝ) (hθ : circleMap c ε θ ≠ d) :
      2 * π * Real.log ‖circleMap c ε θ - d‖ ≤ ∫ φ in (0 : ℝ)..2 * π,
        Real.log ‖circleMap c ε θ - circleMap d ε φ‖ := by
    rw [circle_log_integral_rev _ _ hε.ne', norm_sub_rev d]
    exact mul_le_mul_of_nonneg_left
      (log_le_log_add_posLog hε (norm_pos_iff.mpr (sub_ne_zero.mpr hθ))) (by positivity)
  have h1 : (∫ θ in (0 : ℝ)..2 * π, 2 * π * Real.log ‖circleMap c ε θ - d‖) ≤
      ∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..2 * π,
        Real.log ‖circleMap c ε θ - circleMap d ε φ‖ := by
    apply intervalIntegral.integral_mono_ae (by positivity)
      ((circle_log_integrable c d ε).const_mul _)
      ((continuous_circle_log_row c d hε).intervalIntegrable _ _)
    have hc := ((countable_singleton d).preimage_circleMap c hε.ne').measure_zero (volume : Measure ℝ)
    filter_upwards [compl_mem_ae_iff.mpr hc] with θ hθ
    exact hin θ hθ
  have h2 : (∫ θ in (0 : ℝ)..2 * π, 2 * π * Real.log ‖circleMap c ε θ - d‖) =
      2 * π * (2 * π * (Real.log ε + log⁺ (ε⁻¹ * ‖c - d‖))) := by
    rw [intervalIntegral.integral_const_mul, circle_log_integral c d hε.ne']
  have h3 := log_le_log_add_posLog hε (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  calc
    _ ≤ (2 * π) ^ 2 * (Real.log ε + log⁺ (ε⁻¹ * ‖c - d‖)) :=
      mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    _ = ∫ θ in (0 : ℝ)..2 * π, 2 * π * Real.log ‖circleMap c ε θ - d‖ := by rw [h2]; ring
    _ ≤ _ := h1
end
end Li2

end
