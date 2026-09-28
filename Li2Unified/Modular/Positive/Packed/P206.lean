module
public import Li2Unified.Modular.Positive.Packed.P199

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Energy.CompactEnergy
open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.ReflectionProgram
open Li2Unified.Proofs.Potential.CompactAffine

def triangleRowExpr (s : LayerQ) (tail : List LayerQ) : Expr :=
  .add (.mul (.rat (qMul s.density s.density)) (pairExprQ s s))
    (.mul (.rat ⟨2,1⟩)
      ((tail.map (fun t => .mul (.rat (qMul s.density t.density)) (pairExprQ s t))).foldr
        Expr.add (.rat qZero)))

def checkTriangleRow (s : LayerQ) (tail : List LayerQ) (data : RowData) : Bool :=
  match prepareTrace data.steps with
  | none => false
  | some p => checkExprPoint p (triangleRowExpr s tail) data.node data.bound

def checkTriangleRows : List LayerQ → List RowData → Bool
  | [], [] => true
  | s :: ss, d :: ds => checkTriangleRow s ss d && checkTriangleRows ss ds
  | _, _ => false

end Li2Unified.Proofs.Energy.CompactEnergy

end


end
