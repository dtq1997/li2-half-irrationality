module
public import Li2Unified.Modular.Positive.Packed.P110

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Energy.CompactEnergy
open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.ReflectionProgram
open Li2Unified.Proofs.Potential.CompactAffine

structure LayerQ where
  radius : QPair
  density : QPair
  vertical : Bool

def layersQ : List LayerQ := [
  ⟨⟨7, 100⟩, ⟨5486000, 100000027⟩, false⟩,
  ⟨⟨7, 50⟩, ⟨3870700, 100000027⟩, false⟩,
  ⟨⟨21, 100⟩, ⟨2913000, 100000027⟩, false⟩,
  ⟨⟨7, 25⟩, ⟨2327000, 100000027⟩, false⟩,
  ⟨⟨7, 20⟩, ⟨1932800, 100000027⟩, false⟩,
  ⟨⟨21, 50⟩, ⟨1648500, 100000027⟩, false⟩,
  ⟨⟨49, 100⟩, ⟨1433000, 100000027⟩, false⟩,
  ⟨⟨14, 25⟩, ⟨1263800, 100000027⟩, false⟩,
  ⟨⟨63, 100⟩, ⟨1127200, 100000027⟩, false⟩,
  ⟨⟨7, 10⟩, ⟨1014700, 100000027⟩, false⟩,
  ⟨⟨77, 100⟩, ⟨920500, 100000027⟩, false⟩,
  ⟨⟨21, 25⟩, ⟨840300, 100000027⟩, false⟩,
  ⟨⟨91, 100⟩, ⟨771500, 100000027⟩, false⟩,
  ⟨⟨49, 50⟩, ⟨711800, 100000027⟩, false⟩,
  ⟨⟨21, 20⟩, ⟨659400, 100000027⟩, false⟩,
  ⟨⟨28, 25⟩, ⟨613300, 100000027⟩, false⟩,
  ⟨⟨119, 100⟩, ⟨572300, 100000027⟩, false⟩,
  ⟨⟨63, 50⟩, ⟨535800, 100000027⟩, false⟩,
  ⟨⟨133, 100⟩, ⟨503000, 100000027⟩, false⟩,
  ⟨⟨7, 5⟩, ⟨2230420, 100000027⟩, false⟩,
  ⟨⟨21, 10⟩, ⟨2947820, 100000027⟩, false⟩,
  ⟨⟨14, 5⟩, ⟨2013740, 100000027⟩, false⟩,
  ⟨⟨7, 2⟩, ⟨1498080, 100000027⟩, false⟩,
  ⟨⟨21, 5⟩, ⟨1181890, 100000027⟩, false⟩,
  ⟨⟨49, 10⟩, ⟨974840, 100000027⟩, false⟩,
  ⟨⟨28, 5⟩, ⟨833640, 100000027⟩, false⟩,
  ⟨⟨63, 10⟩, ⟨735770, 100000027⟩, false⟩,
  ⟨⟨7, 1⟩, ⟨668860, 100000027⟩, false⟩,
  ⟨⟨77, 10⟩, ⟨626710, 100000027⟩, false⟩,
  ⟨⟨42, 5⟩, ⟨607930, 100000027⟩, false⟩,
  ⟨⟨91, 10⟩, ⟨617440, 100000027⟩, false⟩,
  ⟨⟨49, 5⟩, ⟨677410, 100000027⟩, false⟩,
  ⟨⟨21, 2⟩, ⟨958380, 100000027⟩, false⟩,
  ⟨⟨56, 5⟩, ⟨929970, 100000027⟩, false⟩,
  ⟨⟨1, 25⟩, ⟨3687200, 100000027⟩, true⟩,
  ⟨⟨2, 25⟩, ⟨3178600, 100000027⟩, true⟩
]

def logSecondExpr (x : QPair) : Expr :=
  if qEq x qZero then .rat qZero else
    .add (.mul (.rat (qDiv (qMul x x) ⟨2,1⟩)) (.log (.rat (qAbs x))))
      (.rat (qNeg (qDiv (qMul ⟨3,1⟩ (qMul x x)) ⟨4,1⟩)))

def perpExpr (b x : QPair) : Expr :=
  .add (.add (.add
    (.mul (.rat (qDiv (qMul b x) ⟨2,1⟩)) (.log (.rat (qAdd (qMul x x) (qMul b b)))))
    (.rat (qNeg (qDiv (qMul ⟨3,1⟩ (qMul b x)) ⟨2,1⟩))))
    (.mul .pi (.rat (qDiv (qMul x x) ⟨4,1⟩))))
    (.mul (.rat (qDiv (qSub (qMul b b) (qMul x x)) ⟨2,1⟩))
      (.atan (.rat (qDiv x b))))

def pairExprQ (s t : LayerQ) : Expr :=
  if s.vertical then
    if t.vertical then
      .mul (.rat ⟨2,1⟩) (.add (logSecondExpr (qAdd s.radius t.radius))
        (.neg (logSecondExpr (qSub s.radius t.radius))))
    else .mul (.rat ⟨2,1⟩) (perpExpr s.radius t.radius)
  else
    if t.vertical then .mul (.rat ⟨2,1⟩) (perpExpr t.radius s.radius)
    else .add (.add (logSecondExpr s.radius) (logSecondExpr t.radius))
      (.neg (logSecondExpr (qSub s.radius t.radius)))

structure RowData where
  steps : List Step
  node : Nat
  bound : I

end Li2Unified.Proofs.Energy.CompactEnergy

end

end
