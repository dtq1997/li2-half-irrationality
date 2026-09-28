module
public import Li2Unified.Modular.Base.CirclePairLog

set_option backward.privateInPublic true

@[expose] public section

section
/-! Mixed curve/circle logarithmic integrals for arbitrary complex centers.
The joint L1 proof adapts Li2.CirclePairLog to any continuous curve on a finite
real interval. No injectivity, separation, or real-center condition is imposed.
The circle has strictly positive radius; no radius-zero statement is claimed. -/
open MeasureTheory Set Real intervalIntegral
namespace Li2Unified.ParameterFamily.Energy
noncomputable section

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

private lemma log_radius_add_posLog {ε y : ℝ} (hε : 0 < ε) (hy : 0 ≤ y) :
    Real.log ε + Real.posLog (ε⁻¹ * y) = Real.log (max ε y) := by
  have he : ε⁻¹ * y = y / ε := by ring
  rw [he]
  by_cases h : y ≤ ε
  · have hdiv0 : 0 ≤ y / ε := div_nonneg hy hε.le
    have hdiv1 : y / ε ≤ 1 := (div_le_one hε).mpr h
    have hp : Real.posLog (y / ε) = 0 := (Real.posLog_eq_zero_iff _).mpr (by
      rw [abs_of_nonneg hdiv0]; exact hdiv1)
    rw [hp, max_eq_left h, add_zero]
  · have hεy : ε < y := lt_of_not_ge h
    have hyp : 0 < y := hε.trans hεy
    have hdiv1 : 1 ≤ y / ε := (one_le_div hε).mpr hεy.le
    have hp : 1 ≤ |y / ε| := by rw [abs_of_pos (div_pos hyp hε)]; exact hdiv1
    rw [Real.posLog_eq_log hp, Real.log_div hyp.ne' hε.ne', max_eq_right hεy.le]
    ring

lemma circle_log_integral_max (c z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ θ in (0 : ℝ)..2 * π, Real.log ‖z - circleMap c ε θ‖) =
      2 * π * Real.log (max ε ‖z - c‖) := by
  rw [Li2.circle_log_integral_rev c z hε.ne', norm_sub_rev c,
    log_radius_add_posLog hε (norm_nonneg _)]

lemma continuous_curve_circle_log_row {γ : ℝ → ℂ} (hγ : Continuous γ)
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun t : ℝ => ∫ θ in (0 : ℝ)..2 * π,
      Real.log ‖γ t - circleMap c ε θ‖) := by
  have he : (fun t : ℝ => ∫ θ in (0 : ℝ)..2 * π,
      Real.log ‖γ t - circleMap c ε θ‖) =
      (fun t : ℝ => 2 * π * Real.log (max ε ‖γ t - c‖)) :=
    funext (fun t => circle_log_integral_max c (γ t) hε)
  rw [he]
  exact continuous_const.mul ((continuous_const.max (hγ.sub continuous_const).norm).log
    (fun t => (lt_of_lt_of_le hε (le_max_left _ _)).ne'))

/-- Joint absolute integrability is established before any Fubini use. -/
theorem integrable_curve_circle_log {γ : ℝ → ℂ} (hγ : Continuous γ) (d : ℂ) {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (hab : a ≤ b) :
    Integrable (fun p : ℝ × ℝ => Real.log ‖γ p.1 - circleMap d ε p.2‖)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc 0 (2 * π)))) := by
  let K : ℝ → ℝ → ℝ := fun θ φ => Real.log ‖γ θ - circleMap d ε φ‖
  let P : ℝ → ℝ → ℝ := fun θ φ => log⁺ ‖γ θ - circleMap d ε φ‖
  have hT : (0 : ℝ) ≤ 2 * π := by positivity
  have hK (θ : ℝ) : IntervalIntegrable (K θ) volume 0 (2 * π) := by
    simpa only [K, norm_sub_rev] using Li2.circle_log_integrable d (γ θ) ε
  have hP : Continuous (Function.uncurry P) := by
    change Continuous (fun p : ℝ × ℝ => log⁺ ‖γ p.1 - circleMap d ε p.2‖)
    apply continuous_posLog_of_nonneg
    · exact ((hγ.comp continuous_fst).sub
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
        (continuous_curve_circle_log_row hγ d hε)
  have hm : Measurable (fun p : ℝ × ℝ => K p.1 p.2) := by
    apply Real.measurable_log.comp
    exact ((hγ.comp continuous_fst).sub
      ((continuous_circleMap d ε).comp continuous_snd)).norm.measurable
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun θ =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp (hK θ))
  · have hi : IntegrableOn (fun θ : ℝ => ∫ φ in (0 : ℝ)..2 * π, ‖K θ φ‖)
        (Ioc a b) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
        (hN.intervalIntegrable a b)
    simpa only [intervalIntegral.integral_of_le hT] using hi

/-- Joint L1 precedes the exchange of the circle and curve parameters. -/
theorem integral_circle_curve_log {γ : ℝ → ℂ} (hγ : Continuous γ)
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (hab : a ≤ b) :
    (∫ θ in (0 : ℝ)..2 * π, ∫ t in a..b,
      Real.log ‖γ t - circleMap c ε θ‖) =
      2 * π * (∫ t in a..b, Real.log (max ε ‖γ t - c‖)) := by
  have hJ := integrable_curve_circle_log hγ c hε hab
  have hT : (0 : ℝ) ≤ 2 * π := by positivity
  calc
    _ = ∫ θ in Ioc (0 : ℝ) (2 * π), ∫ t in Ioc a b,
        Real.log ‖γ t - circleMap c ε θ‖ := by
      simp_rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hab]
    _ = ∫ t in Ioc a b, ∫ θ in Ioc (0 : ℝ) (2 * π),
        Real.log ‖γ t - circleMap c ε θ‖ :=
      (MeasureTheory.integral_integral_swap
        (f := fun t θ => Real.log ‖γ t - circleMap c ε θ‖) hJ).symm
    _ = ∫ t in a..b, 2 * π * Real.log (max ε ‖γ t - c‖) := by
      rw [intervalIntegral.integral_of_le hab]
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        dsimp only
        rw [← intervalIntegral.integral_of_le hT, circle_log_integral_max c (γ t) hε])
    _ = _ := by rw [intervalIntegral.integral_const_mul]

end
end Li2Unified.ParameterFamily.Energy

end


end
