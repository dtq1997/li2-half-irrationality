module
public import Li2Unified.Modular.Positive.Packed.P069
public import Mathlib.MeasureTheory.Integral.Prod

set_option backward.privateInPublic true

@[expose] public section

section
/-! The actual comparison measure's finite product decomposition. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Energy
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

private lemma finite_layer (s : StarLayer) (hs : s.Valid) :
    IsFiniteMeasure s.measure := by
  refine ⟨?_⟩
  rw [s.measure_univ hs]
  exact ENNReal.ofReal_lt_top

private lemma finite_layers (ss : List StarLayer) (hs : ∀ s ∈ ss, s.Valid) :
    IsFiniteMeasure (starLayerMeasure ss) := by
  refine ⟨?_⟩
  rw [starLayerMeasure_univ ss hs]
  exact ENNReal.ofReal_lt_top

private lemma prod_layers_right (s : StarLayer) (tt : List StarLayer)
    (hs : s.Valid) (ht : ∀ t ∈ tt, t.Valid) :
    s.measure.prod (starLayerMeasure tt) =
      (tt.map (fun t => s.measure.prod t.measure)).sum := by
  induction tt with
  | nil => simp [starLayerMeasure]
  | cons t tt ih =>
    have hhead : t.Valid := ht t (by simp)
    have htail : ∀ u ∈ tt, u.Valid := fun u hu => ht u (by simp [hu])
    letI : IsFiniteMeasure s.measure := finite_layer s hs
    letI : IsFiniteMeasure t.measure := finite_layer t hhead
    letI : IsFiniteMeasure (starLayerMeasure tt) := finite_layers tt htail
    rw [starLayerMeasure, Measure.prod_add, ih htail]
    simp only [List.map_cons, List.sum_cons]

private lemma prod_layers (ss tt : List StarLayer)
    (hs : ∀ s ∈ ss, s.Valid) (ht : ∀ t ∈ tt, t.Valid) :
    (starLayerMeasure ss).prod (starLayerMeasure tt) =
      (ss.map (fun s => (tt.map (fun t => s.measure.prod t.measure)).sum)).sum := by
  induction ss with
  | nil => simp [starLayerMeasure]
  | cons s ss ih =>
    have hhead : s.Valid := hs s (by simp)
    have htail : ∀ u ∈ ss, u.Valid := fun u hu => hs u (by simp [hu])
    letI : IsFiniteMeasure s.measure := finite_layer s hhead
    letI : IsFiniteMeasure (starLayerMeasure ss) := finite_layers ss htail
    letI : IsFiniteMeasure (starLayerMeasure tt) := finite_layers tt ht
    rw [starLayerMeasure, Measure.add_prod, prod_layers_right s tt hhead ht, ih htail]
    simp only [List.map_cons, List.sum_cons]

private lemma integral_list_sum {α : Type*} [MeasurableSpace α]
    (ms : List (Measure α)) (f : α → ℝ) (hf : Integrable f ms.sum) :
    (∫ x, f x ∂ms.sum) = (ms.map (fun μ => ∫ x, f x ∂μ)).sum := by
  induction ms with
  | nil => simp
  | cons μ ms ih =>
    have hμ : Integrable f μ := hf.left_of_add_measure
    have hms : Integrable f ms.sum := hf.right_of_add_measure
    rw [List.sum_cons, integral_add_measure hμ hms, List.map_cons, List.sum_cons, ih hms]

private lemma integrable_of_mem_sum {α : Type*} [MeasurableSpace α]
    {ms : List (Measure α)} {μ : Measure α} (hμ : μ ∈ ms)
    {f : α → ℝ} (hf : Integrable f ms.sum) : Integrable f μ := by
  induction ms with
  | nil => simp at hμ
  | cons ν ms ih =>
    rcases List.mem_cons.mp hμ with rfl | htail
    · exact hf.left_of_add_measure
    · exact ih htail hf.right_of_add_measure

private def logKernel (p : ℂ × ℂ) : ℝ := Real.log ‖p.1-p.2‖

theorem comparisonEnergy_eq_pair_measure_sum :
    comparisonEnergy =
      (layerData.map (fun s => (layerData.map (fun t =>
        ∫ p : ℂ × ℂ, logKernel p ∂(s.measure.prod t.measure))).sum)).sum := by
  let ms : List (Measure (ℂ × ℂ)) :=
    layerData.map (fun s => (layerData.map (fun t => s.measure.prod t.measure)).sum)
  have hp : comparisonMeasure.prod comparisonMeasure = ms.sum := by
    exact prod_layers layerData layerData layerData_valid layerData_valid
  have hi : Integrable logKernel ms.sum := by
    rw [← hp]
    exact integrable_log_comparison_prod
  have ho := integral_list_sum ms logKernel hi
  have hinner (s : StarLayer) (hs : s ∈ layerData) :
      (∫ p : ℂ × ℂ, logKernel p ∂(layerData.map
        (fun t => s.measure.prod t.measure)).sum) =
      (layerData.map (fun t => ∫ p : ℂ × ℂ,
        logKernel p ∂(s.measure.prod t.measure))).sum := by
    apply integral_list_sum
    apply integrable_of_mem_sum (ms := ms) _ hi
    exact List.mem_map.mpr ⟨s, hs, rfl⟩
  rw [show comparisonEnergy = ∫ p : ℂ × ℂ, logKernel p ∂ms.sum from by
    simp only [comparisonEnergy, logKernel]
    rw [← hp]]
  rw [ho]
  simp only [ms, List.map_map]
  congr 1
  exact List.map_congr_left hinner

end
end Li2Unified.Proofs.Energy

end


end
