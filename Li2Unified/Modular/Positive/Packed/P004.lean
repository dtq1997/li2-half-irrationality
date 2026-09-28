module
public import Li2Unified.Modular.Positive.Packed.P003
public import Li2Unified.Modular.Base.PrimeBasisChange
public import Li2Unified.Modular.Base.ClassBasisDegree

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section

private abbrev L (n p : ℕ) (a : Fin p) : ℕ :=
  Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a

def generalJet (n p : ℕ) := Σ a : Fin p, Fin (L n p a)

noncomputable instance (n p : ℕ) : Fintype (generalJet n p) := by
  unfold generalJet
  infer_instance

def generalJetSize (n p : ℕ) : ℕ := ∑ a : Fin p, L n p a

noncomputable def generalJetEquiv (n p : ℕ) :
    Fin (generalJetSize n p) ≃ generalJet n p :=
  Fintype.equivOfCardEq (by
    change Fintype.card (Fin (∑ a : Fin p, L n p a)) =
      Fintype.card (Σ a : Fin p, Fin (L n p a))
    rw [Fintype.card_fin, Fintype.card_sigma]
    simp only [Fintype.card_fin])

def generalJetPoly (n p : ℕ) (a : generalJet n p) : ℤ[X] :=
  Li2.classBasisPoly (Li2.primeCenter p) (L n p) a.1 a.2.val

def generalIndexedJetPoly (n p : ℕ) (i : Fin (generalJetSize n p)) : ℤ[X] :=
  generalJetPoly n p (generalJetEquiv n p i)

private theorem generalJet_coordinates_injective (n p : ℕ) :
    Function.Injective (fun a : generalJet n p => (a.1, a.2.val)) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ hab
  simp only [Prod.mk.injEq] at hab
  rcases hab with ⟨rfl, hij⟩
  cases Fin.ext hij
  rfl

theorem generalIndexedJetPoly_natDegree_lt (n p : ℕ)
    (i : Fin (generalJetSize n p)) :
    (generalIndexedJetPoly n p i).natDegree < generalJetSize n p := by
  simpa only [generalIndexedJetPoly, generalJetPoly, generalJetSize] using
    Li2.classBasisPoly_natDegree_lt (Li2.primeCenter p) (L n p)
      (generalJetEquiv n p i).1 (generalJetEquiv n p i).2.val
      (generalJetEquiv n p i).2.isLt

theorem generalIndexedJetPoly_independent (n p : ℕ) [Fact p.Prime]
    (v : Fin (generalJetSize n p) → ZMod p)
    (hv : (∑ i, C (v i) *
      (generalIndexedJetPoly n p i).map (Int.castRingHom (ZMod p))) = 0) :
    v = 0 := by
  refine Li2.classBasis_independent
    (fun a => (Li2.primeCenter p a : ZMod p))
    (Li2.primeCenter_mod_injective p) (L n p)
    (fun i => (generalJetEquiv n p i).1)
    (fun i => (generalJetEquiv n p i).2.val)
    (fun i => (generalJetEquiv n p i).2.isLt) ?_ v ?_
  · intro i j hcls hidx
    apply (generalJetEquiv n p).injective
    apply generalJet_coordinates_injective n p
    exact Prod.ext hcls hidx
  · simp only [generalIndexedJetPoly, generalJetPoly,
      Li2.classBasisPoly_map] at hv
    simpa only [Li2.classBasisPoly, Li2.classProduct, Int.coe_castRingHom] using hv

theorem generalIndexedJetPoly_det_unit (n p : ℕ) [Fact p.Prime] :
    (Li2.coeffMat fun i =>
      (generalIndexedJetPoly n p i).map (Int.castRingHom ℚ)).det ≠ 0 ∧
    padicValRat p (Li2.coeffMat fun i =>
      (generalIndexedJetPoly n p i).map (Int.castRingHom ℚ)).det = 0 :=
  Li2.coeffMat_det_unit_of_independent _
    (generalIndexedJetPoly_natDegree_lt n p)
    (generalIndexedJetPoly_independent n p)

#print axioms generalIndexedJetPoly_natDegree_lt
#print axioms generalIndexedJetPoly_independent
#print axioms generalIndexedJetPoly_det_unit

end
end Li2Unified.Proofs.Hermite

end


end
