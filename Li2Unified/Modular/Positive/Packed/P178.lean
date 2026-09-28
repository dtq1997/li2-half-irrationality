module
public import Li2Unified.Modular.Positive.Packed.P110
public import Li2Unified.Modular.Positive.Packed.P167
public import Li2Unified.Modular.Positive.Packed.P177
public import Li2Unified.Modular.Positive.Packed.P164
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

set_option backward.privateInPublic true

@[expose] public section

section
/-! The fixed rational term lists have exactly the original half-parameter
real potential as their sum. This is the sole bridge from compact certificates
to the actual layer data. -/
namespace Li2Unified.Proofs.Potential.CompactAffine

open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.ReflectionProgram
open Li2Unified.Stage0.HalfPotentialExpressions

noncomputable section

private theorem halfRayLayerData_sound :
    halfRayLayerData.map (fun q => (q.1.toRat, q.2.toRat)) = rayLayers := by
  norm_num [halfRayLayerData, rayLayers, QPair.toRat]

private theorem halfVerticalLayerData_sound :
    halfVerticalLayerData.map (fun q => (q.1.toRat, q.2.toRat)) = verticalLayers := by
  norm_num [halfVerticalLayerData, verticalLayers, QPair.toRat]

private theorem halfRayDensity_sound :
    (halfRayDensity.toRat : ℝ) = rayDensitySum := by
  norm_num [halfRayDensity, QPair.toRat, rayDensitySum, rayLayers]

private theorem coeff4 (q : QPair) :
    ((qMul ⟨4, 1⟩ q).toRat : ℝ) = 4 * (q.toRat : ℝ) := by
  rw [toRat_qMul]
  norm_num [QPair.toRat]

private theorem coeff8 (q : QPair) :
    ((qMul ⟨8, 1⟩ q).toRat : ℝ) = 8 * (q.toRat : ℝ) := by
  rw [toRat_qMul]
  norm_num [QPair.toRat]

private theorem halfConstantExpr_sound :
    halfConstantExpr.denote 0 = 8 * Real.log 2 - 4 := by
  norm_num [halfConstantExpr, Expr.denote, QPair.toRat]
  ring

private theorem halfRayDensityCoeff_sound :
    ((qSub (qMul ⟨4, 1⟩ halfRayDensity) ⟨2, 1⟩).toRat : ℝ) =
      4 * rayDensitySum - 2 := by
  rw [← halfRayDensity_sound]
  norm_num [qSub, qAdd, qMul, qNeg, halfRayDensity, QPair.toRat]

private theorem halfUpDensityCoeff_sound :
    ((qSub (qMul ⟨2, 1⟩ halfRayDensity) qOne).toRat : ℝ) =
      2 * rayDensitySum - 1 := by
  rw [← halfRayDensity_sound]
  norm_num [qSub, qAdd, qMul, qNeg, qOne, halfRayDensity, QPair.toRat]

private theorem rayLayer_eval (L : List (QPair × QPair)) (x : ℝ) :
    ((L.map (fun q => Term.H (qMul ⟨4, 1⟩ q.2) q.1 true)).map
        (fun t => t.eval x)).sum =
      (L.map (fun q => 4 * (q.2.toRat : ℝ) * H ((q.1.toRat : ℝ) - x))).sum := by
  induction L with
  | nil => simp
  | cons q qs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      simp [Term.eval, coeff4, sub_eq_add_neg]

private theorem upLayer_eval (L : List (QPair × QPair)) (x : ℝ) :
    ((L.map (fun q => Term.F (qMul ⟨4, 1⟩ q.2) q.1)).map
        (fun t => t.eval x)).sum =
      (L.map (fun q => 4 * (q.2.toRat : ℝ) * F (q.1.toRat : ℝ) x)).sum := by
  induction L with
  | nil => simp
  | cons q qs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      simp [Term.eval, coeff4]

private theorem rayLayer_actual (x : ℝ) :
    ((halfRayLayerData.map (fun q => Term.H (qMul ⟨4, 1⟩ q.2) q.1 true)).map
        (fun t => t.eval x)).sum =
      (rayLayers.map (fun q => 4 * (q.2 : ℝ) * H ((q.1 : ℝ) - x))).sum := by
  rw [rayLayer_eval]
  rw [← halfRayLayerData_sound]
  simp only [List.map_map, Function.comp_def]

private theorem upLayer_actual (x : ℝ) :
    ((halfRayLayerData.map (fun q => Term.F (qMul ⟨4, 1⟩ q.2) q.1)).map
        (fun t => t.eval x)).sum =
      (rayLayers.map (fun q => 4 * (q.2 : ℝ) * F (q.1 : ℝ) x)).sum := by
  rw [upLayer_eval]
  rw [← halfRayLayerData_sound]
  simp only [List.map_map, Function.comp_def]

private theorem rayVerticalLayer_eval (L : List (QPair × QPair)) (x : ℝ) :
    ((L.flatMap (fun q =>
      [Term.F (qMul ⟨8, 1⟩ q.2) q.1,
       Term.linear (.mul (.rat (qMul ⟨4, 1⟩ q.2)) .pi)])).map
        (fun t => t.eval x)).sum =
      (L.map (fun q =>
        8 * (q.2.toRat : ℝ) * (F (q.1.toRat : ℝ) x + Real.pi * x / 2))).sum := by
  induction L with
  | nil => simp
  | cons q qs ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      rw [ih]
      simp [Term.eval, Expr.denote, coeff4, coeff8]
      ring

private theorem upVerticalLayer_eval (L : List (QPair × QPair)) (x : ℝ) :
    ((L.flatMap (fun q =>
      [Term.H (qMul ⟨4, 1⟩ q.2) q.1 true,
       Term.H (qMul ⟨4, 1⟩ q.2) q.1 false])).map
        (fun t => t.eval x)).sum =
      (L.map (fun q =>
        4 * (q.2.toRat : ℝ) *
          (H ((q.1.toRat : ℝ) - x) + H ((q.1.toRat : ℝ) + x)))).sum := by
  induction L with
  | nil => simp
  | cons q qs ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      rw [ih]
      simp [Term.eval, coeff4, sub_eq_add_neg]
      ring

private theorem rayVerticalLayer_actual (x : ℝ) :
    ((halfVerticalLayerData.flatMap (fun q =>
      [Term.F (qMul ⟨8, 1⟩ q.2) q.1,
       Term.linear (.mul (.rat (qMul ⟨4, 1⟩ q.2)) .pi)])).map
        (fun t => t.eval x)).sum =
      (verticalLayers.map (fun q =>
        8 * (q.2 : ℝ) * (F (q.1 : ℝ) x + Real.pi * x / 2))).sum := by
  rw [rayVerticalLayer_eval]
  rw [← halfVerticalLayerData_sound]
  simp only [List.map_map, Function.comp_def]

private theorem upVerticalLayer_actual (x : ℝ) :
    ((halfVerticalLayerData.flatMap (fun q =>
      [Term.H (qMul ⟨4, 1⟩ q.2) q.1 true,
       Term.H (qMul ⟨4, 1⟩ q.2) q.1 false])).map
        (fun t => t.eval x)).sum =
      (verticalLayers.map (fun q =>
        4 * (q.2 : ℝ) * (H ((q.1 : ℝ) - x) + H ((q.1 : ℝ) + x)))).sum := by
  rw [upVerticalLayer_eval]
  rw [← halfVerticalLayerData_sound]
  simp only [List.map_map, Function.comp_def]

theorem halfRayTerms_eval (x : ℝ) :
    (halfRayTerms.map (fun t => t.eval x)).sum = rayCompactExpr x := by
  unfold halfRayTerms rayCompactExpr
  simp only [List.map_append, List.sum_append, List.map_cons,
    List.sum_cons, List.map_nil, List.sum_nil]
  rw [rayLayer_actual x, rayVerticalLayer_actual x]
  simp only [Term.eval, Expr.denote, halfConstantExpr_sound,
    halfRayDensityCoeff_sound]
  norm_num [QPair.toRat, qOne, qZero]
  ring

theorem halfUpTerms_eval (x : ℝ) :
    (halfUpTerms.map (fun t => t.eval x)).sum = verticalCompactExpr x := by
  unfold halfUpTerms verticalCompactExpr
  simp only [List.map_append, List.sum_append, List.map_cons,
    List.sum_cons, List.map_nil, List.sum_nil]
  rw [upLayer_actual x, upVerticalLayer_actual x]
  simp only [Term.eval, Expr.denote, halfConstantExpr_sound,
    halfUpDensityCoeff_sound]
  norm_num [QPair.toRat, qOne]
  rw [← halfRayDensity_sound]
  norm_num [halfRayDensity, QPair.toRat]
  ring

theorem halfRayTerms_actual (x : ℝ) (hx : 0 ≤ x) :
    (halfRayTerms.map (fun t => t.eval x)).sum =
      Li2Unified.Stage0.HalfAnalytic.psiRay x := by
  rw [halfRayTerms_eval, rayCompactExpr_actual x hx]

theorem halfUpTerms_actual (x : ℝ) (hx : 0 ≤ x) :
    (halfUpTerms.map (fun t => t.eval x)).sum =
      Li2Unified.Stage0.HalfAnalytic.psiUp x := by
  rw [halfUpTerms_eval, verticalCompactExpr_actual x hx]

end
end Li2Unified.Proofs.Potential.CompactAffine

#print axioms Li2Unified.Proofs.Potential.CompactAffine.halfRayTerms_eval
#print axioms Li2Unified.Proofs.Potential.CompactAffine.halfUpTerms_eval
#print axioms Li2Unified.Proofs.Potential.CompactAffine.halfRayTerms_actual
#print axioms Li2Unified.Proofs.Potential.CompactAffine.halfUpTerms_actual

end


end
