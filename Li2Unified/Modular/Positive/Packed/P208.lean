module
public import Li2Unified.Modular.Positive.Packed.P204
public import Li2Unified.Modular.Positive.Packed.P205
public import Li2Unified.Modular.Positive.Packed.P207

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Energy.CompactEnergy
open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.ReflectionProgram
open Li2Unified.Proofs.Potential.CompactAffine
open Li2Unified.Instances.PosHalf.LayerComparison
noncomputable section

theorem triSum_map {α β : Type} (f : β → β → ℝ) (g : α → β) (ls : List α) :
    triSum f (ls.map g) = triSum (fun s t => f (g s) (g t)) ls := by
  induction ls with
  | nil => simp [triSum]
  | cons s ss ih => simp only [List.map_cons, triSum, List.map_map, ih, Function.comp_def]

theorem triangleRowExpr_denote (s : LayerQ) (tail : List LayerQ)
    (hs : validLayer s = true) (ht : ∀ t ∈ tail, validLayer t = true) :
    (triangleRowExpr s tail).denote 0 =
      (s.toLayer.density : ℝ) * (s.toLayer.density : ℝ) * pairFormula s.toLayer s.toLayer +
      2 * (tail.map (fun t => (s.toLayer.density : ℝ) * (t.toLayer.density : ℝ) *
        pairFormula s.toLayer t.toLayer)).sum := by
  have hrow := row_fold_denote s hs tail ht
  have htwo : ((⟨2,1⟩ : QPair).toRat : ℝ) = 2 := by norm_num [QPair.toRat]
  simp only [triangleRowExpr, Expr.denote, toRat_qMul, Rat.cast_mul,
    pairExprQ_denote s s hs hs, hrow, htwo, LayerQ.toLayer]

theorem triangleValue_eq_triSum (ls : List LayerQ)
    (hv : ∀ s ∈ ls, validLayer s = true) :
    triangleValue ls = triSum (fun s t =>
      (s.toLayer.density : ℝ) * (t.toLayer.density : ℝ) * pairFormula s.toLayer t.toLayer) ls := by
  induction ls with
  | nil => simp [triangleValue, triSum]
  | cons s ss ih =>
      have hs := hv s (by simp)
      have ht : ∀ t ∈ ss, validLayer t = true := fun t h => hv t (by simp [h])
      rw [triangleValue, triangleRowExpr_denote s ss hs ht, triSum, ih ht]

theorem comparisonEnergy_eq_triangleValue : comparisonEnergy = triangleValue layersQ := by
  rw [comparisonEnergy_eq_triSum, ← layersQ_toLayer, triSum_map]
  exact (triangleValue_eq_triSum layersQ layersQ_valid).symm

theorem energy_triangle_lower_of_certs (ds : List RowData)
    (hc : checkTriangleRows layersQ ds = true)
    (ht : qLE ⟨589,1000⟩ (ds.foldl (fun acc d => qAdd acc d.bound.lo) qZero) = true) :
    (589/1000 : ℝ) ≤ comparisonEnergy := by
  rw [comparisonEnergy_eq_triangleValue]
  have h := checked_triangle_total_lower hc (show qValid ⟨589,1000⟩ = true by decide) ht
  norm_num [QPair.toRat] at h
  exact h

end
end Li2Unified.Proofs.Energy.CompactEnergy

#print axioms Li2Unified.Proofs.Energy.CompactEnergy.energy_triangle_lower_of_certs

end


end
