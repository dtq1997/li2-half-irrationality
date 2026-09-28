module
public import Li2Unified.Modular.Positive.Packed.P204

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Energy.CompactEnergy

open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison
open Li2Unified.Proofs.Energy

noncomputable section

/-- logSecondPrimitive is even: Real.log (-x) = Real.log x. -/
theorem logSecondPrimitive_neg (x : ℝ) : logSecondPrimitive (-x) = logSecondPrimitive x := by
  simp only [logSecondPrimitive, Real.log_neg_eq_log]
  ring

/-- Holds for every pair of layers, no validity needed: the two mixed branches
are literally the same expression, and the other two use evenness. -/
theorem pairFormula_symm (s t : StarLayer) : pairFormula s t = pairFormula t s := by
  have hsub : ((s.radius : ℝ) - (t.radius : ℝ)) = -((t.radius : ℝ) - (s.radius : ℝ)) := by ring
  cases hs : s.vertical <;> cases ht : t.vertical <;>
    simp only [pairFormula, hs, ht, if_true, if_false, Bool.false_eq_true]
  · -- horizontal / horizontal
    rw [hsub, logSecondPrimitive_neg]; ring
  · -- vertical / vertical
    rw [hsub, logSecondPrimitive_neg, add_comm (s.radius : ℝ)]

/-- Triangular form: diagonal once, strictly later entries twice. -/
def triSum {α : Type} (f : α → α → ℝ) : List α → ℝ
  | [] => 0
  | s :: ss => f s s + 2 * (ss.map (f s)).sum + triSum f ss

theorem square_eq_triSum {α : Type} (f : α → α → ℝ) (hf : ∀ a b, f a b = f b a) :
    ∀ l : List α, (l.map (fun s => (l.map (f s)).sum)).sum = triSum f l
  | [] => by simp [triSum]
  | s :: ss => by
      have ih := square_eq_triSum f hf ss
      have hcol : (ss.map (fun u => f u s)).sum = (ss.map (f s)).sum := by
        congr 1; exact List.map_congr_left (fun u _ => hf u s)
      -- LHS = (f s s + Σ_t f s t) + Σ_u (f u s + Σ_t f u t)
      simp only [List.map_cons, List.sum_cons, List.sum_map_add, triSum]
      rw [hcol, ih]
      ring

theorem comparisonEnergy_eq_triSum :
    comparisonEnergy =
      triSum (fun s t => (s.density : ℝ) * (t.density : ℝ) * pairFormula s t) layerData := by
  rw [comparisonEnergy_eq_pairFormula_sum]
  exact square_eq_triSum _ (fun a b => by rw [pairFormula_symm a b]; ring) layerData

end
end Li2Unified.Proofs.Energy.CompactEnergy

end


end
