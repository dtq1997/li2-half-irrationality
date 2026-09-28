module
public import Li2Unified.Modular.Positive.Packed.P206
public import Li2Unified.Modular.Positive.Packed.P200

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Energy.CompactEnergy
open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.ReflectionProgram
open Li2Unified.Proofs.Potential.CompactAffine
noncomputable section

def triangleValue : List LayerQ → ℝ
  | [] => 0
  | s :: ss => (triangleRowExpr s ss).denote 0 + triangleValue ss

theorem checkTriangleRow_lower {s : LayerQ} {tail : List LayerQ} {data : RowData}
    (hc : checkTriangleRow s tail data = true) :
    (data.bound.lo.toRat : ℝ) ≤ (triangleRowExpr s tail).denote 0 := by
  cases hp : prepareTrace data.steps with
  | none => simp [checkTriangleRow, hp] at hc
  | some p =>
      have hcheck : checkExprPoint p (triangleRowExpr s tail) data.node data.bound = true := by
        simpa only [checkTriangleRow, hp] using hc
      exact (checkExprPoint_sound hp hcheck).1

theorem checkTriangleRow_lower_valid {s : LayerQ} {tail : List LayerQ} {data : RowData}
    (hc : checkTriangleRow s tail data = true) : qValid data.bound.lo = true := by
  cases hp : prepareTrace data.steps with
  | none => simp [checkTriangleRow, hp] at hc
  | some p =>
      have hcheck : checkExprPoint p (triangleRowExpr s tail) data.node data.bound = true := by
        simpa only [checkTriangleRow, hp] using hc
      exact (validI_parts (checkExprPoint_valid hcheck)).1

theorem checkTriangleRows_lower {ss : List LayerQ} {ds : List RowData}
    (hc : checkTriangleRows ss ds = true) :
    (ds.map (fun d => (d.bound.lo.toRat : ℝ))).sum ≤ triangleValue ss := by
  induction ss generalizing ds with
  | nil =>
      cases ds with
      | nil => simp [triangleValue]
      | cons d ds => simp [checkTriangleRows] at hc
  | cons s ss ih =>
      cases ds with
      | nil => simp [checkTriangleRows] at hc
      | cons d ds =>
          have hp : checkTriangleRow s ss d = true ∧ checkTriangleRows ss ds = true := by
            simpa only [checkTriangleRows, Bool.and_eq_true] using hc
          simpa only [List.map_cons, List.sum_cons, triangleValue] using
            add_le_add (checkTriangleRow_lower hp.1) (ih hp.2)

theorem checkTriangleRows_lower_valid {ss : List LayerQ} {ds : List RowData}
    (hc : checkTriangleRows ss ds = true) : ∀ d ∈ ds, qValid d.bound.lo = true := by
  induction ss generalizing ds with
  | nil =>
      cases ds with
      | nil => simp
      | cons d ds => simp [checkTriangleRows] at hc
  | cons s ss ih =>
      cases ds with
      | nil => simp [checkTriangleRows] at hc
      | cons d ds =>
          have hp : checkTriangleRow s ss d = true ∧ checkTriangleRows ss ds = true := by
            simpa only [checkTriangleRows, Bool.and_eq_true] using hc
          intro d' hd'
          rcases List.mem_cons.mp hd' with rfl | hmem
          · exact checkTriangleRow_lower_valid hp.1
          · exact ih hp.2 d' hmem

private theorem triangle_mapped_rat_sum_real {α : Type} (f : α → ℚ) (xs : List α) :
    (((xs.map f).sum : ℚ) : ℝ) = (xs.map (fun x => (f x : ℝ))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem checked_triangle_total_lower {ss : List LayerQ} {ds : List RowData} {lower : QPair}
    (hc : checkTriangleRows ss ds = true) (hl : qValid lower = true)
    (ht : qLE lower (ds.foldl (fun acc d => qAdd acc d.bound.lo) qZero) = true) :
    (lower.toRat : ℝ) ≤ triangleValue ss := by
  have hv := checkTriangleRows_lower_valid hc
  have hs := fold_qAdd_valid (fun d : RowData => d.bound.lo) ds qZero qValid_qZero hv
  have hq := qLE_sound hl hs ht
  have heq : ((ds.foldl (fun acc d => qAdd acc d.bound.lo) qZero).toRat : ℝ) =
      (ds.map (fun d => (d.bound.lo.toRat : ℝ))).sum := by
    rw [fold_qAdd_toRat (fun d : RowData => d.bound.lo) ds qZero qValid_qZero hv]
    simp only [qZero_toRat, zero_add, triangle_mapped_rat_sum_real]
  have hr : (lower.toRat : ℝ) ≤
      ((ds.foldl (fun acc d => qAdd acc d.bound.lo) qZero).toRat : ℝ) := by
    exact_mod_cast hq
  rw [heq] at hr
  exact hr.trans (checkTriangleRows_lower hc)

end
end Li2Unified.Proofs.Energy.CompactEnergy

end


end
