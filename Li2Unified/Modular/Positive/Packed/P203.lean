module
public import Li2Unified.Modular.Positive.Packed.P069
public import Li2Unified.Modular.Positive.Packed.P202

set_option backward.privateInPublic true

@[expose] public section

section
/-! Pairwise product integrability and transport to the actual star-layer segments. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Energy
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

private lemma layer_measure_le (ss : List StarLayer) {s : StarLayer} (hs : s ∈ ss) :
    s.measure ≤ starLayerMeasure ss := by
  induction ss with
  | nil => simp at hs
  | cons t ss ih =>
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact Measure.le_add_right le_rfl
    · exact (ih hs').trans (Measure.le_add_left le_rfl)

private lemma finite_layer (s : StarLayer) (hs : s.Valid) :
    IsFiniteMeasure s.measure := by
  refine ⟨?_⟩
  rw [s.measure_univ hs]
  exact ENNReal.ofReal_lt_top

theorem integrable_log_pair_product {s t : StarLayer}
    (hs : s ∈ layerData) (ht : t ∈ layerData) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖)
      (s.measure.prod t.measure) := by
  letI : IsFiniteMeasure s.measure := finite_layer s (layerData_valid s hs)
  letI : IsFiniteMeasure t.measure := finite_layer t (layerData_valid t ht)
  have hmt : t.measure ≤ comparisonMeasure := layer_measure_le layerData ht
  have hms : ∀ᵐ w ∂s.measure, ‖w‖ ≤ 56/5 :=
    ae_mono (layer_measure_le layerData hs) ae_norm_comparisonMeasure
  have hm : AEStronglyMeasurable
      (fun p : ℂ × ℂ => Real.log ‖p.2-p.1‖)
      (s.measure.prod t.measure) :=
    ((measurable_snd.sub measurable_fst).norm.log).aestronglyMeasurable
  have hi : Integrable (fun p : ℂ × ℂ => Real.log ‖p.2-p.1‖)
      (s.measure.prod t.measure) := by
    apply (integrable_prod_iff hm).2
    constructor
    · exact Filter.Eventually.of_forall (fun w => t.integrable_log w)
    · have hmeas : AEStronglyMeasurable
          (fun w : ℂ => ∫ z : ℂ, ‖Real.log ‖z-w‖‖ ∂t.measure) s.measure :=
        hm.norm.integral_prod_right'
      apply (integrable_const (11/10 + Real.log (112/5:ℝ))).mono' hmeas
      filter_upwards [hms] with w hw
      have hn : 0 ≤ ∫ z : ℂ, ‖Real.log ‖z-w‖‖ ∂t.measure :=
        integral_nonneg (fun z => norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      have hbound : (∫ z : ℂ, |Real.log ‖z-w‖| ∂t.measure) ≤
          ∫ z : ℂ, |Real.log ‖z-w‖| ∂comparisonMeasure := by
        apply integral_mono_measure hmt
        · exact Filter.Eventually.of_forall (fun z => abs_nonneg _)
        · exact (integrable_log_comparisonMeasure w).abs
      have hlog : Real.log (56/5+‖w‖) ≤ Real.log (112/5:ℝ) :=
        Real.log_le_log (by linarith [norm_nonneg w]) (by linarith)
      simpa only [Real.norm_eq_abs] using
        hbound.trans ((integral_abs_log_comparisonMeasure_le w).trans
          (add_le_add le_rfl hlog))
  simpa only [norm_sub_rev] using hi

theorem pair_product_eq_interval {s t : StarLayer}
    (hs : s ∈ layerData) (ht : t ∈ layerData) :
    (∫ p : ℂ × ℂ, Real.log ‖p.1-p.2‖ ∂(s.measure.prod t.measure)) =
      (s.density : ℝ) * (t.density : ℝ) *
        (∫ x in s.left..s.right, ∫ y in t.left..t.right,
          Real.log ‖(x:ℂ)*s.direction-(y:ℂ)*t.direction‖) := by
  letI : IsFiniteMeasure s.measure := finite_layer s (layerData_valid s hs)
  letI : IsFiniteMeasure t.measure := finite_layer t (layerData_valid t ht)
  have hi := integrable_log_pair_product hs ht
  have hk : Measurable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) :=
    (measurable_fst.sub measurable_snd).norm.log
  have houter : Measurable (fun w : ℂ =>
      ∫ z : ℂ, Real.log ‖w-z‖ ∂t.measure) :=
    hk.stronglyMeasurable.integral_prod_right'.measurable
  calc
    _ = ∫ w : ℂ, ∫ z : ℂ, Real.log ‖w-z‖ ∂t.measure ∂s.measure :=
      integral_prod _ hi
    _ = (s.density : ℝ) * ∫ x in s.left..s.right,
        ∫ z : ℂ, Real.log ‖(x:ℂ)*s.direction-z‖ ∂t.measure :=
      s.integral_eq (layerData_valid s hs) _ houter
    _ = (s.density : ℝ) * ∫ x in s.left..s.right,
        (t.density : ℝ) * ∫ y in t.left..t.right,
          Real.log ‖(x:ℂ)*s.direction-(y:ℂ)*t.direction‖ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro x _
      exact t.integral_eq (layerData_valid t ht) _
        ((measurable_const.sub measurable_id).norm.log)
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

end
end Li2Unified.Proofs.Energy

end


end
