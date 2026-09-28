module
public import Li2Unified.Modular.Positive.Packed.P201
public import Li2Unified.Modular.Positive.Packed.P203
public import Li2Unified.Modular.Positive.Packed.P200

set_option backward.privateInPublic true

@[expose] public section

section
/-! Exact pairwise primitive formula for the actual 36-layer energy. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Energy
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

def pairFormula (s t : StarLayer) : ℝ :=
  if s.vertical then
    if t.vertical then
      2*(logSecondPrimitive ((s.radius : ℝ)+(t.radius : ℝ)) -
        logSecondPrimitive ((s.radius : ℝ)-(t.radius : ℝ)))
    else
      2*(if s.radius = 0 then 0 else
        perpendicularPrimitive (s.radius : ℝ) (t.radius : ℝ))
  else
    if t.vertical then
      2*(if t.radius = 0 then 0 else
        perpendicularPrimitive (t.radius : ℝ) (s.radius : ℝ))
    else
      logSecondPrimitive (s.radius : ℝ) +
        logSecondPrimitive (t.radius : ℝ) -
        logSecondPrimitive ((s.radius : ℝ)-(t.radius : ℝ))

theorem pair_interval_eq_formula {s t : StarLayer}
    (hs : s ∈ layerData) (ht : t ∈ layerData) :
    (∫ x in s.left..s.right, ∫ y in t.left..t.right,
      Real.log ‖(x:ℂ)*s.direction-(y:ℂ)*t.direction‖) =
      pairFormula s t := by
  have hrs : (0:ℝ) ≤ s.radius := by exact_mod_cast (layerData_valid s hs).1
  have hrt : (0:ℝ) ≤ t.radius := by exact_mod_cast (layerData_valid t ht).1
  cases hsv : s.vertical <;> cases htv : t.vertical
  · simpa [pairFormula, StarLayer.left, StarLayer.right,
      StarLayer.direction, hsv, htv] using!
        horizontal_horizontal (s.radius : ℝ) (t.radius : ℝ) hrs hrt
  · simpa [pairFormula, StarLayer.left, StarLayer.right,
      StarLayer.direction, hsv, htv] using!
        horizontal_vertical (s.radius : ℝ) (t.radius : ℝ) hrs hrt
  · simpa [pairFormula, StarLayer.left, StarLayer.right,
      StarLayer.direction, hsv, htv] using!
        vertical_horizontal (t.radius : ℝ) (s.radius : ℝ) hrt hrs
  · simpa [pairFormula, StarLayer.left, StarLayer.right,
      StarLayer.direction, hsv, htv] using!
        vertical_vertical (s.radius : ℝ) (t.radius : ℝ) hrs hrt

theorem comparisonEnergy_eq_pairFormula_sum :
    comparisonEnergy =
      (layerData.map (fun s => (layerData.map (fun t =>
        (s.density : ℝ) * (t.density : ℝ) * pairFormula s t)).sum)).sum := by
  have h := comparisonEnergy_eq_pair_measure_sum
  change comparisonEnergy =
    (layerData.map (fun s => (layerData.map (fun t =>
      ∫ p : ℂ × ℂ, Real.log ‖p.1-p.2‖
        ∂(s.measure.prod t.measure))).sum)).sum at h
  rw [h]
  congr 1
  apply List.map_congr_left
  intro s hs
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [pair_product_eq_interval hs ht, pair_interval_eq_formula hs ht]

end
end Li2Unified.Proofs.Energy

end

section
namespace Li2Unified.Proofs.Energy.CompactEnergy
open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.ReflectionProgram
open Li2Unified.Proofs.Potential.CompactAffine
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison
noncomputable section

def LayerQ.toLayer (s : LayerQ) : StarLayer :=
  ⟨s.radius.toRat, s.density.toRat, s.vertical⟩

def validLayer (s : LayerQ) : Bool :=
  qValid s.radius && qValid s.density && qLT qZero s.radius

theorem layersQ_valid : ∀ s ∈ layersQ, validLayer s = true := by
  decide +kernel

theorem layersQ_toLayer : layersQ.map LayerQ.toLayer = layerData := by
  norm_num [layersQ, layerData, LayerQ.toLayer, QPair.toRat]

private theorem real_qMul (a b : QPair) :
    ((qMul a b).toRat : ℝ) = (a.toRat : ℝ) * (b.toRat : ℝ) := by
  rw [toRat_qMul, Rat.cast_mul]

private theorem real_qNeg (a : QPair) :
    ((qNeg a).toRat : ℝ) = -(a.toRat : ℝ) := by
  rw [toRat_qNeg, Rat.cast_neg]

private theorem real_qDiv (a b : QPair) (hb : qLT qZero b = true) :
    ((qDiv a b).toRat : ℝ) = (a.toRat : ℝ) / (b.toRat : ℝ) := by
  rw [toRat_qDiv_pos a b hb, Rat.cast_div]

private theorem real_half (a : QPair) :
    ((qDiv a ⟨2,1⟩).toRat : ℝ) = (a.toRat : ℝ) / 2 := by
  rw [real_qDiv a ⟨2,1⟩ (by decide)]
  norm_num [QPair.toRat]

private theorem real_quarter (a : QPair) :
    ((qDiv a ⟨4,1⟩).toRat : ℝ) = (a.toRat : ℝ) / 4 := by
  rw [real_qDiv a ⟨4,1⟩ (by decide)]
  norm_num [QPair.toRat]

private theorem real_two : ((⟨2,1⟩ : QPair).toRat : ℝ) = 2 := by
  norm_num [QPair.toRat]

theorem logSecondExpr_denote (x : QPair) (hx : qValid x = true) :
    (logSecondExpr x).denote 0 = logSecondPrimitive (x.toRat : ℝ) := by
  by_cases hz : qEq x qZero = true
  · have hx0 : x.toRat = 0 := by
      simpa only [qZero_toRat] using! qEq_sound hx qValid_qZero hz
    simp [logSecondExpr, hz, Expr.denote, qZero_toRat, hx0, logSecondPrimitive]
  · have habs : ((qAbs x).toRat : ℝ) = |(x.toRat : ℝ)| := by
      rw [qAbs_toRat x hx, Rat.cast_abs]
    rw [logSecondExpr, if_neg hz]
    simp only [Expr.denote, real_qNeg, real_quarter,
      real_half, real_qMul, habs, Real.log_abs, logSecondPrimitive]
    norm_num [QPair.toRat]
    ring

theorem perpExpr_denote (b x : QPair) (hb : qValid b = true)
    (hbpos : qLT qZero b = true) (hx : qValid x = true) :
    (perpExpr b x).denote 0 =
      perpendicularPrimitive (b.toRat : ℝ) (x.toRat : ℝ) := by
  have hxx := qValid_qMul hx hx
  have hbb := qValid_qMul hb hb
  have hadd : ((qAdd (qMul x x) (qMul b b)).toRat : ℝ) =
      (x.toRat : ℝ)^2 + (b.toRat : ℝ)^2 := by
    rw [toRat_qAdd _ _ hxx hbb, Rat.cast_add, real_qMul, real_qMul]
    ring
  have hsub : ((qSub (qMul b b) (qMul x x)).toRat : ℝ) =
      (b.toRat : ℝ)^2 - (x.toRat : ℝ)^2 := by
    rw [toRat_qSub _ _ hbb hxx, Rat.cast_sub, real_qMul, real_qMul]
    ring
  simp only [perpExpr, Expr.denote, real_qNeg, real_half, real_quarter,
    hadd, hsub, real_qMul, real_qDiv x b hbpos, perpendicularPrimitive]
  norm_num [QPair.toRat]
  ring

theorem pairExprQ_denote (s t : LayerQ)
    (hs : validLayer s = true) (ht : validLayer t = true) :
    (pairExprQ s t).denote 0 = pairFormula s.toLayer t.toLayer := by
  simp only [validLayer, Bool.and_eq_true] at hs ht
  obtain ⟨⟨hsr, _⟩, hspos⟩ := hs
  obtain ⟨⟨htr, _⟩, htpos⟩ := ht
  have hs0 : s.radius.toRat ≠ 0 :=
    ne_of_gt (by simpa only [qZero_toRat] using! qLT_sound qValid_qZero hsr hspos)
  have ht0 : t.radius.toRat ≠ 0 :=
    ne_of_gt (by simpa only [qZero_toRat] using! qLT_sound qValid_qZero htr htpos)
  have hsub := toRat_qSub _ _ hsr htr
  have hadd := toRat_qAdd _ _ hsr htr
  cases hsv : s.vertical <;> cases htv : t.vertical <;>
    simp [pairExprQ, pairFormula, LayerQ.toLayer, hsv, htv, hs0, ht0, Expr.denote,
      logSecondExpr_denote _ hsr, logSecondExpr_denote _ htr,
      logSecondExpr_denote _ (qValid_qSub hsr htr),
      logSecondExpr_denote _ (qValid_qAdd hsr htr),
      perpExpr_denote _ _ hsr hspos htr, perpExpr_denote _ _ htr htpos hsr,
      hsub, hadd, real_two, Rat.cast_add, Rat.cast_sub, sub_eq_add_neg]

theorem row_fold_denote (s : LayerQ) (hs : validLayer s = true)
    (ls : List LayerQ) (hl : ∀ t ∈ ls, validLayer t = true) :
    ((ls.map (fun t => Expr.mul (.rat (qMul s.density t.density))
        (pairExprQ s t))).foldr Expr.add (.rat qZero)).denote 0 =
      (ls.map (fun t => (s.toLayer.density : ℝ) * (t.toLayer.density : ℝ) *
        pairFormula s.toLayer t.toLayer)).sum := by
  induction ls with
  | nil => simp [Expr.denote, qZero_toRat]
  | cons t ts ih =>
      have ht := hl t (by simp)
      have hi := ih (fun u hu => hl u (by simp [hu]))
      simp only [List.map_cons, List.foldr_cons, Expr.denote, real_qMul,
        pairExprQ_denote s t hs ht, hi, List.sum_cons, LayerQ.toLayer]

end
end Li2Unified.Proofs.Energy.CompactEnergy

end

end
