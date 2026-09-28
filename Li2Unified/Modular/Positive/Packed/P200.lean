module
public import Li2Unified.Modular.Positive.Packed.P199
public import Li2Unified.Modular.Positive.Packed.P173
public import Li2Unified.Modular.Positive.Packed.P175

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Energy.CompactEnergy
open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.ReflectionProgram
open Li2Unified.Proofs.Potential.CompactAffine
noncomputable section

theorem checkRow_lower {s : LayerQ} {data : RowData}
    (hc : checkRow s data = true) :
    (data.bound.lo.toRat : ℝ) ≤ (rowExpr s).denote 0 := by
  cases hp : prepareTrace data.steps with
  | none => simp [checkRow, hp] at hc
  | some p =>
      have hcheck : checkExprPoint p (rowExpr s) data.node data.bound = true := by
        simpa only [checkRow, hp] using! hc
      exact (checkExprPoint_sound hp hcheck).1

theorem checkRow_lower_valid {s : LayerQ} {data : RowData}
    (hc : checkRow s data = true) : qValid data.bound.lo = true := by
  cases hp : prepareTrace data.steps with
  | none => simp [checkRow, hp] at hc
  | some p =>
      have hcheck : checkExprPoint p (rowExpr s) data.node data.bound = true := by
        simpa only [checkRow, hp] using! hc
      have hv := checkExprPoint_valid hcheck
      simp only [validI, Bool.and_eq_true] at hv
      exact hv.1.1

theorem checkRows_lower {ss : List LayerQ} {ds : List RowData}
    (hc : checkRows ss ds = true) :
    (ds.map (fun d => (d.bound.lo.toRat : ℝ))).sum ≤
      (ss.map (fun s => (rowExpr s).denote 0)).sum := by
  induction ss generalizing ds with
  | nil =>
      cases ds with
      | nil => simp
      | cons d ds => simp [checkRows] at hc
  | cons s ss ih =>
      cases ds with
      | nil => simp [checkRows] at hc
      | cons d ds =>
          have hp : checkRow s d = true ∧ checkRows ss ds = true := by
            simpa only [checkRows, Bool.and_eq_true] using! hc
          simpa only [List.map_cons, List.sum_cons] using!
            add_le_add (checkRow_lower hp.1) (ih hp.2)

theorem checkRows_lower_valid {ss : List LayerQ} {ds : List RowData}
    (hc : checkRows ss ds = true) : ∀ d ∈ ds, qValid d.bound.lo = true := by
  induction ss generalizing ds with
  | nil =>
      cases ds with
      | nil => simp
      | cons d ds => simp [checkRows] at hc
  | cons s ss ih =>
      cases ds with
      | nil => simp [checkRows] at hc
      | cons d ds =>
          have hp : checkRow s d = true ∧ checkRows ss ds = true := by
            simpa only [checkRows, Bool.and_eq_true] using! hc
          intro d' hd'
          rcases List.mem_cons.mp hd' with rfl | hmem
          · exact checkRow_lower_valid hp.1
          · exact ih hp.2 d' hmem

private theorem mapped_rat_sum_real {α : Type} (f : α → ℚ) (xs : List α) :
    (((xs.map f).sum : ℚ) : ℝ) = (xs.map (fun x => (f x : ℝ))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem checked_total_lower {ss : List LayerQ} {ds : List RowData} {lower : QPair}
    (hc : checkRows ss ds = true) (hl : qValid lower = true)
    (ht : qLE lower (ds.foldl (fun acc d => qAdd acc d.bound.lo) qZero) = true) :
    (lower.toRat : ℝ) ≤ (ss.map (fun s => (rowExpr s).denote 0)).sum := by
  have hv := checkRows_lower_valid hc
  have hs := fold_qAdd_valid (fun d : RowData => d.bound.lo) ds qZero qValid_qZero hv
  have hq := qLE_sound hl hs ht
  have heq : ((ds.foldl (fun acc d => qAdd acc d.bound.lo) qZero).toRat : ℝ) =
      (ds.map (fun d => (d.bound.lo.toRat : ℝ))).sum := by
    rw [fold_qAdd_toRat (fun d : RowData => d.bound.lo) ds qZero qValid_qZero hv]
    simp only [qZero_toRat, zero_add, mapped_rat_sum_real]
  have hr : (lower.toRat : ℝ) ≤
      ((ds.foldl (fun acc d => qAdd acc d.bound.lo) qZero).toRat : ℝ) := by
    exact_mod_cast hq
  rw [heq] at hr
  exact hr.trans (checkRows_lower hc)

end
end Li2Unified.Proofs.Energy.CompactEnergy

end


end
