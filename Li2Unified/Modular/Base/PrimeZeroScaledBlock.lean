module
public import Li2Unified.Modular.Base.PrimeZeroRationalLeading
public import Li2Unified.Modular.Base.PrimeCrossValuation

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def primeZeroEdgeSlot (i : Fin 2) : Fin 6 := ⟨3+i.val,by have h := i.isLt; omega⟩

lemma primeZeroEdgeSlot_encode (hp4 : 3 < p) (i : Fin 2) :
    primeBlockToJet hp4 (Sum.inr (primeZeroEdgeSlot i)) =
      some (primeZeroBlockJet hp4 i) := by
  fin_cases i <;> rfl

lemma primeBlockWeight_zeroSlot (i : Fin 2) :
    primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) = (i.val:ℚ)-3/2 := by
  fin_cases i <;> norm_num [primeBlockWeight,primeZeroEdgeSlot]

lemma primeEdgeIntegerWeight_zeroSlot (i : Fin 2) :
    primeEdgeIntegerWeight (primeZeroEdgeSlot i) = (i.val:ℤ)-2 := by
  fin_cases i <;> norm_num [primeEdgeIntegerWeight,primeZeroEdgeSlot]

lemma primeZeroSlot_basis (hp4 : 3 < p) (i : Fin 2) :
    primeOriginalBasis p (by omega)
      ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeZeroEdgeSlot i))) =
      primeZeroBlockPoly hp4 i.castSucc := by
  rw [primeZeroBlockPoly_jet]
  exact primeBlock_original_basis_jet hp4 _ (primeZeroBlockJet hp4 i)
    (primeZeroEdgeSlot_encode hp4 i)

lemma primeZeroSlot_unit (hp4 : 3 < p) (i : Fin 2) :
    primeBlockUnitScale hp4 (Sum.inr (primeZeroEdgeSlot i)) =
      (primeLocalUnit p ⟨0,by omega⟩:ℚ)⁻¹ :=
  primeBlockUnitScale_jet hp4 _ (primeZeroBlockJet hp4 i) (primeZeroEdgeSlot_encode hp4 i)

end
end Li2

end
