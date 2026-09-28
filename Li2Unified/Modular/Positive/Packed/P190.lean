module
public import Li2Unified.Modular.Positive.Packed.P185
public import Li2Unified.Modular.Positive.Packed.P187
public import Li2Unified.Modular.Positive.Packed.P189
public import Li2Unified.Modular.Positive.Packed.P069
public import Li2Unified.Modular.Positive.Packed.P186

set_option backward.privateInPublic true

@[expose] public section

section
/-! The circle-to-all-layers block is exactly the circle average of the
actual comparison potential. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

theorem starProfile_circle_layer_sum (h : ℕ) (x : Fin h → ℂ)
    (ε : ℝ) (i : Fin h) :
    (∑ j : Fin layerData.length,
      weightedPairInt (starProfileDensity h) (starProfileCurve h x ε)
        (fun z w : ℂ => Real.log ‖z - w‖) (.inl i) (.inr j)) =
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          comparisonPotential (circleMap (x i) ε θ)) := by
  let F : Fin layerData.length → ℝ → ℝ := fun j θ =>
    ∫ φ in (0 : ℝ)..2 * Real.pi,
      (2 * Real.pi)⁻¹ * starLayerAngularDensity (layerData.get j) *
        Real.log ‖circleMap (x i) ε θ - starLayerCurve (layerData.get j) φ‖
  have hT : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hP (j : Fin layerData.length) :
      weightedPairInt (starProfileDensity h) (starProfileCurve h x ε)
        (fun z w : ℂ => Real.log ‖z - w‖) (.inl i) (.inr j) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, F j θ := rfl
  have houter (j : Fin layerData.length) :
      IntervalIntegrable (F j) volume 0 (2 * Real.pi) := by
    have hi := (integrable_circleLayerPairKernel (x i) ε
      (List.get_mem layerData j)).integral_prod_left
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
    simpa only [F, μcirc, circleLayerPairKernel,
      intervalIntegral.integral_of_le hT] using hi
  have hrow (θ : ℝ) :
      (∑ j : Fin layerData.length, F j θ) =
        (2 * Real.pi)⁻¹ * comparisonPotential (circleMap (x i) ε θ) := by
    have hj (j : Fin layerData.length) : F j θ =
        (2 * Real.pi)⁻¹ *
          (∫ φ in (0 : ℝ)..2 * Real.pi,
            starLayerAngularDensity (layerData.get j) *
              Real.log ‖circleMap (x i) ε θ -
                starLayerCurve (layerData.get j) φ‖) := by
      dsimp only [F]
      simp_rw [mul_assoc]
      rw [intervalIntegral.integral_const_mul]
    simp_rw [hj, ← Finset.mul_sum, star_comparisonPotential_angular]
  simp_rw [hP]
  calc
    (∑ j : Fin layerData.length,
      ∫ θ in (0 : ℝ)..2 * Real.pi, F j θ) =
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          ∑ j : Fin layerData.length, F j θ :=
      (intervalIntegral.integral_finset_sum (f := F)
        (fun j _ => houter j)).symm
    _ = _ := by simp_rw [hrow, intervalIntegral.integral_const_mul]

end
end Li2Unified.Proofs.Contour

end

section
/-! The actual circle against the 36-layer measure, reduced by Fubini to its
finite list of truncated line potentials. -/

open MeasureTheory Set intervalIntegral
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

private def layerCircleCross (s : StarLayer) (c : ℂ) (ε θ : ℝ) : ℝ :=
  (s.density : ℝ) * ∫ x in s.left..s.right,
    Real.log ‖(x : ℂ) * s.direction - circleMap c ε θ‖

private def layerCircleTrunc (s : StarLayer) (c : ℂ) (ε : ℝ) : ℝ :=
  (s.density : ℝ) * ∫ x in s.left..s.right,
    Real.log (max ε ‖(x : ℂ) * s.direction - c‖)

private lemma layerCircleCross_intervalIntegrable (s : StarLayer)
    (hs : s.Valid) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable (layerCircleCross s c ε) volume 0 (2 * Real.pi) := by
  have hγ : Continuous (fun x : ℝ => (x : ℂ) * s.direction) := by fun_prop
  have hab := s.left_le_right hs.1
  have hJ := integrable_curve_circle_log hγ c hε hab
  have hT : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hi : Integrable (fun θ : ℝ => ∫ x in s.left..s.right,
      Real.log ‖(x : ℂ) * s.direction - circleMap c ε θ‖)
      (volume.restrict (Ioc 0 (2 * Real.pi))) := by
    simpa only [intervalIntegral.integral_of_le hab] using hJ.swap.integral_prod_left
  change IntervalIntegrable (fun θ : ℝ => (s.density : ℝ) *
    ∫ x in s.left..s.right,
      Real.log ‖(x : ℂ) * s.direction - circleMap c ε θ‖)
    volume 0 (2 * Real.pi)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 (hi.const_mul _)

private lemma layerCircleCross_integral_eq (s : StarLayer)
    (hs : s.Valid) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, layerCircleCross s c ε θ) =
      2 * Real.pi * layerCircleTrunc s c ε := by
  have hγ : Continuous (fun x : ℝ => (x : ℂ) * s.direction) := by fun_prop
  have hab := s.left_le_right hs.1
  have hmain := integral_circle_curve_log hγ c hε hab
  unfold layerCircleCross layerCircleTrunc
  rw [intervalIntegral.integral_const_mul]
  rw [hmain]
  ring

private lemma layerListCircleCross_integral_eq (ss : List StarLayer)
    (hvalid : ∀ s ∈ ss, s.Valid) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable
      (fun θ => (ss.map fun s => layerCircleCross s c ε θ).sum)
      volume 0 (2 * Real.pi) ∧
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      (ss.map fun s => layerCircleCross s c ε θ).sum) =
      2 * Real.pi * (ss.map fun s => layerCircleTrunc s c ε).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    have hs : s.Valid := hvalid s (by simp)
    have hrest : ∀ t ∈ ss, t.Valid := by
      intro t ht
      exact hvalid t (by simp [ht])
    obtain ⟨htailInt, htailEq⟩ := ih hrest
    have hsingleInt := layerCircleCross_intervalIntegrable s hs c hε
    have hsingleEq := layerCircleCross_integral_eq s hs c hε
    constructor
    · simpa only [List.map_cons, List.sum_cons] using
        hsingleInt.add htailInt
    · simp only [List.map_cons, List.sum_cons]
      rw [intervalIntegral.integral_add hsingleInt htailInt,
        hsingleEq, htailEq]
      ring

theorem actual_circle_comparisonPotential_eq_truncation
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      comparisonPotential (circleMap c ε θ)) =
      2 * Real.pi * (layerData.map fun s => (s.density : ℝ) *
        ∫ x in s.left..s.right,
          Real.log (max ε ‖(x : ℂ) * s.direction - c‖)).sum := by
  have hsum := (layerListCircleCross_integral_eq layerData
    layerData_valid c hε).2
  calc
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      comparisonPotential (circleMap c ε θ)) =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        (layerData.map fun s => layerCircleCross s c ε θ).sum := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [comparisonPotential_eq]
      rfl
    _ = _ := by simpa only [layerCircleTrunc] using hsum

end
end Li2Unified.Proofs.Contour

end


end
