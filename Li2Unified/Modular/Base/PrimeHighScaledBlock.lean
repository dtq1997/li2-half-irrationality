module
public import Li2Unified.Modular.Base.PrimeHighRationalLeading
public import Li2Unified.Modular.Base.PrimeNormalizedMatrix

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def primeHighEdgeSlot (ell : Fin 3) : Fin 6 :=
  ⟨ell.val,by have h := ell.isLt; omega⟩

lemma primeHighEdgeSlot_encode (hp4 : 3 < p) (ell : Fin 3) :
    primeBlockToJet hp4 (Sum.inr (primeHighEdgeSlot ell)) =
      some (primeHighBlockJet hp4 ell) := by
  fin_cases ell <;> rfl

lemma primeBlockWeight_highSlot (ell : Fin 3) :
    primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) = -1/2 := by
  fin_cases ell <;> norm_num [primeBlockWeight,primeHighEdgeSlot]

lemma primeEdgeIntegerWeight_highSlot (ell : Fin 3) :
    primeEdgeIntegerWeight (primeHighEdgeSlot ell) = -1 := by
  fin_cases ell <;> norm_num [primeEdgeIntegerWeight,primeHighEdgeSlot]

lemma primeHighSlot_basis (hp4 : 3 < p) (ell : Fin 3) :
    primeOriginalBasis p (by omega)
      ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot ell))) =
      primeHighBlockPoly hp4 ell 0 := by
  rw [primeHighBlockPoly_jet]
  exact primeBlock_original_basis_jet hp4 _ (primeHighBlockJet hp4 ell)
    (primeHighEdgeSlot_encode hp4 ell)

lemma primeHighSlot_unit (hp4 : 3 < p) (ell : Fin 3) :
    primeBlockUnitScale hp4 (Sum.inr (primeHighEdgeSlot ell)) =
      (primeLocalUnit p (primeHighBlockJet hp4 ell).1:ℚ)⁻¹ :=
  primeBlockUnitScale_jet hp4 _ (primeHighBlockJet hp4 ell)
    (primeHighEdgeSlot_encode hp4 ell)

end
end Li2

end
