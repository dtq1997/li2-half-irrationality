module
public import Li2Unified.Modular.Positive.Fast.PrepareTraceFast
public import Li2Unified.Modular.Positive.Packed.P110
public import Li2Unified.Modular.Positive.Packed.P206

set_option backward.privateInPublic true

@[expose] public section
namespace Li2Unified.Proofs.Potential.CompactAffine
open Li2Unified.Proofs.Potential.KernelReflectionSelf

def checkOneFast (terms : List Term) (upper : QPair) (data : BoxData) : Bool :=
  qValid upper &&
  match prepareTraceFast data.steps with
  | none => false
  | some prepared =>
      checkBox prepared terms data.box &&
      qLE (qAdd data.box.alpha
        (qMul (qAbs data.box.beta) (radius data.box.left data.box.right))) upper

theorem checkOneFast_sound {terms : List Term} {upper : QPair} {data : BoxData}
    (h : checkOneFast terms upper data = true) : checkOne terms upper data = true := by
  unfold checkOneFast at h
  cases hp : prepareTraceFast data.steps with
  | none => simp [hp] at h
  | some p =>
      have old := prepareTraceFast_sound hp
      simpa [checkOne, old, hp] using h

end Li2Unified.Proofs.Potential.CompactAffine

namespace Li2Unified.Proofs.Energy.CompactEnergy
open Li2Unified.Proofs.Potential.CompactAffine

def checkTriangleRowFast (s : LayerQ) (tail : List LayerQ) (data : RowData) : Bool :=
  match prepareTraceFast data.steps with
  | none => false
  | some p => checkExprPoint p (triangleRowExpr s tail) data.node data.bound

theorem checkTriangleRowFast_sound {s : LayerQ} {tail : List LayerQ} {data : RowData}
    (h : checkTriangleRowFast s tail data = true) : checkTriangleRow s tail data = true := by
  unfold checkTriangleRowFast at h
  cases hp : prepareTraceFast data.steps with
  | none => simp [hp] at h
  | some p =>
      have old := prepareTraceFast_sound hp
      simpa [checkTriangleRow, old, hp] using h

end Li2Unified.Proofs.Energy.CompactEnergy

end
