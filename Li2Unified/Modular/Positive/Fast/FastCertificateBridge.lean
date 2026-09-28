module
public import Li2Unified.Modular.Positive.Fast.ReifyTrie

set_option backward.privateInPublic true

/-!
Each certificate is checked by two kernel computations: the interval trace alone, and the
remaining comparisons on the trie-backed reification. Together they give the original check.
-/

@[expose] public section
namespace Li2Unified.Proofs.Potential.CompactAffine
open Li2Unified.Proofs.Potential.KernelReflectionSelf

/-- `checkOne` without the interval trace check, on the trie-backed reification. -/
def checkOneBoxFast (terms : List Term) (upper : QPair) (data : BoxData) : Bool :=
  qValid upper &&
  match reifyFast 10 .nil data.steps with
  | none => false
  | some t =>
      checkBoxWith (trieExpr 10 t) (trieOut 10 t) terms data.box &&
      qLE (qAdd data.box.alpha
        (qMul (qAbs data.box.beta) (radius data.box.left data.box.right))) upper

theorem checkOne_of_fast {terms : List Term} {upper : QPair} {data : BoxData}
    (htrace : Domain.fastCheckTrace 10 (point qZero) data.steps = true)
    (hbox : checkOneBoxFast terms upper data = true) : checkOne terms upper data = true := by
  unfold checkOneBoxFast at hbox
  cases hr : reifyFast 10 .nil data.steps with
  | none => simp [hr] at hbox
  | some t =>
      obtain ⟨p, hp, hE, hO⟩ := prepareTrace_of_fast htrace hr
      simp only [hr] at hbox
      simpa [checkOne, hp, checkBox_eq_with, ← hE, ← hO] using hbox

end Li2Unified.Proofs.Potential.CompactAffine

namespace Li2Unified.Proofs.Energy.CompactEnergy
open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.CompactAffine

/-- `checkTriangleRow` without the interval trace check, on the trie-backed reification. -/
def checkTriangleRowExprFast (s : LayerQ) (tail : List LayerQ) (data : RowData) : Bool :=
  match reifyFast 10 .nil data.steps with
  | none => false
  | some t => checkExprPointWith (trieExpr 10 t) (trieOut 10 t)
      (triangleRowExpr s tail) data.node data.bound

theorem checkTriangleRow_of_fast {s : LayerQ} {tail : List LayerQ} {data : RowData}
    (htrace : Domain.fastCheckTrace 10 (point qZero) data.steps = true)
    (hrow : checkTriangleRowExprFast s tail data = true) :
    checkTriangleRow s tail data = true := by
  unfold checkTriangleRowExprFast at hrow
  cases hr : reifyFast 10 .nil data.steps with
  | none => simp [hr] at hrow
  | some t =>
      obtain ⟨p, hp, hE, hO⟩ := prepareTrace_of_fast htrace hr
      simp only [hr] at hrow
      simpa [checkTriangleRow, hp, checkExprPoint_eq_with, ← hE, ← hO] using hrow

end Li2Unified.Proofs.Energy.CompactEnergy

end
