module
public import Li2Unified.Modular.Positive.Packed.P185
public import Li2Unified.Modular.Positive.Packed.P069
public import Li2Unified.Modular.Positive.Packed.P186

set_option backward.privateInPublic true

@[expose] public section

section
/-! Joint absolute integrability for the actual particle circle against any
one of the fixed 36 comparison layers. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

private lemma selected_layer_le_aux (ss : List StarLayer) {t : StarLayer}
    (ht : t ∈ ss) : t.measure ≤ starLayerMeasure ss := by
  induction ss with
  | nil => simp at ht
  | cons s ss ih =>
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Measure.le_add_right le_rfl
      · exact (ih ht').trans (Measure.le_add_left le_rfl)

private lemma selected_layer_le {t : StarLayer} (ht : t ∈ layerData) :
    t.measure ≤ comparisonMeasure := selected_layer_le_aux layerData ht

def circleLayerPairKernel (c : ℂ) (ε : ℝ) (t : StarLayer)
    (θ φ : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * starLayerAngularDensity t *
    Real.log ‖circleMap c ε θ - starLayerCurve t φ‖

theorem integrable_circleLayerPairKernel (c : ℂ) (ε : ℝ)
    {t : StarLayer} (ht : t ∈ layerData) :
    Integrable (fun p : ℝ × ℝ => circleLayerPairKernel c ε t p.1 p.2)
      (μcirc.prod μcirc) := by
  have hvt := layerData_valid t ht
  have hrt := (layerData_radii t ht).1
  have hρc : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  have hρt : 0 ≤ starLayerAngularDensity t := by
    have hd : (0 : ℝ) ≤ t.density := by exact_mod_cast hvt.2
    exact div_nonneg (mul_nonneg hd (sub_nonneg.mpr (t.left_le_right hvt.1)))
      (by positivity)
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      circleLayerPairKernel c ε t p.1 p.2) := by
    unfold circleLayerPairKernel
    exact (measurable_const.mul measurable_const).mul
      ((((continuous_circleMap c ε).measurable.comp measurable_fst).sub
        ((continuous_starLayerCurve t).measurable.comp measurable_snd)).norm.log)
  have hrow (θ : ℝ) : IntervalIntegrable
      (fun φ => circleLayerPairKernel c ε t θ φ) volume 0 (2 * Real.pi) := by
    have h := starLayer_intervalIntegrable_log t
      (by
        have hr : (0 : ℝ) < t.radius := Rat.cast_pos.mpr hrt
        cases hv : t.vertical <;>
          simp [StarLayer.left, StarLayer.right, hv] <;> linarith)
      (circleMap c ε θ)
    change IntervalIntegrable
      (fun φ => (2 * Real.pi)⁻¹ * starLayerAngularDensity t *
        Real.log ‖circleMap c ε θ - starLayerCurve t φ‖)
      volume 0 (2 * Real.pi)
    have hsymmetric : ∀ φ : ℝ,
        Real.log ‖circleMap c ε θ - starLayerCurve t φ‖ =
          Real.log ‖starLayerCurve t φ - circleMap c ε θ‖ := by
      intro φ; rw [norm_sub_rev]
    simpa only [hsymmetric] using! h.const_mul
      ((2 * Real.pi)⁻¹ * starLayerAngularDensity t)
  have hrow_norm (θ : ℝ) :
      (∫ φ in (0 : ℝ)..2 * Real.pi,
        ‖circleLayerPairKernel c ε t θ φ‖) =
        (2 * Real.pi)⁻¹ *
          (∫ z : ℂ, |Real.log ‖circleMap c ε θ - z‖| ∂t.measure) := by
    have he (φ : ℝ) :
        ‖circleLayerPairKernel c ε t θ φ‖ =
          (2 * Real.pi)⁻¹ * starLayerAngularDensity t *
            |Real.log ‖circleMap c ε θ - starLayerCurve t φ‖| := by
      simp only [circleLayerPairKernel, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg hρc, abs_of_nonneg hρt]
    calc
      _ = (2 * Real.pi)⁻¹ *
          (∫ φ in (0 : ℝ)..2 * Real.pi,
            starLayerAngularDensity t *
              |Real.log ‖circleMap c ε θ - starLayerCurve t φ‖|) := by
        simp_rw [he, mul_assoc]
        rw [intervalIntegral.integral_const_mul]
      _ = (2 * Real.pi)⁻¹ *
          ((t.density : ℝ) * ∫ y in t.left..t.right,
            |Real.log ‖circleMap c ε θ - ((y : ℂ) * t.direction)‖|) := by
        congr 1
        exact starLayer_angular_integral t
          (fun z => |Real.log ‖circleMap c ε θ - z‖|)
      _ = _ := by
        congr 1
        exact (t.integral_eq hvt (fun z => |Real.log ‖circleMap c ε θ - z‖|)
          (by simpa only [Real.norm_eq_abs] using!
            ((measurable_const (a := circleMap c ε θ)).sub measurable_id).norm.log.norm)).symm
  have hmt : t.measure ≤ comparisonMeasure := selected_layer_le ht
  have hrow_le (θ : ℝ) :
      (∫ φ in (0 : ℝ)..2 * Real.pi,
        ‖circleLayerPairKernel c ε t θ φ‖) ≤
          (2 * Real.pi)⁻¹ *
            (11 / 10 + Real.log (56 / 5 + ‖c‖ + |ε|)) := by
    rw [hrow_norm]
    have hw : ‖circleMap c ε θ‖ ≤ ‖c‖ + |ε| := by
      calc
        _ ≤ ‖c‖ + ‖circleMap 0 ε θ‖ := by
          simpa only [circleMap, zero_add] using!
            (norm_add_le c (circleMap 0 ε θ))
        _ = _ := by rw [norm_circleMap_zero]
    have hcomp : Integrable (fun z : ℂ =>
        |Real.log ‖circleMap c ε θ - z‖|) comparisonMeasure := by
      simpa only [norm_sub_rev] using!
        (integrable_log_comparisonMeasure (circleMap c ε θ)).abs
    have hm :
        (∫ z : ℂ, |Real.log ‖circleMap c ε θ - z‖| ∂t.measure) ≤
          ∫ z : ℂ, |Real.log ‖circleMap c ε θ - z‖| ∂comparisonMeasure := by
      apply integral_mono_measure hmt
      · exact Filter.Eventually.of_forall (fun z => abs_nonneg _)
      · exact hcomp
    have hc :
        (∫ z : ℂ, |Real.log ‖circleMap c ε θ - z‖| ∂comparisonMeasure) ≤
          11 / 10 + Real.log (56 / 5 + ‖circleMap c ε θ‖) := by
      simpa only [norm_sub_rev] using!
        integral_abs_log_comparisonMeasure_le (circleMap c ε θ)
    have hlog : Real.log (56 / 5 + ‖circleMap c ε θ‖) ≤
        Real.log (56 / 5 + ‖c‖ + |ε|) :=
      Real.log_le_log (by linarith [norm_nonneg (circleMap c ε θ)]) (by linarith)
    exact mul_le_mul_of_nonneg_left
      (hm.trans (hc.trans (add_le_add le_rfl hlog))) hρc
  apply (integrable_prod_iff hmeas.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (fun θ =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1 (hrow θ))
  · have hm : AEStronglyMeasurable
        (fun θ : ℝ => ∫ φ : ℝ,
          ‖circleLayerPairKernel c ε t θ φ‖ ∂μcirc) μcirc :=
        hmeas.aestronglyMeasurable.norm.integral_prod_right'
    apply (integrable_const
      ((2 * Real.pi)⁻¹ *
        (11 / 10 + Real.log (56 / 5 + ‖c‖ + |ε|)))).mono' hm
    filter_upwards [] with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
      ← intervalIntegral.integral_of_le (by positivity)]
    exact hrow_le θ

end
end Li2Unified.Proofs.Contour

end


end
