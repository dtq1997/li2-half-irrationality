module
public import Li2Unified.Modular.Positive.Packed.P004
public import Li2Unified.Modular.Base.PrimeJets

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section

def generalIndexedJetLocalOrder (n p : ℕ)
    (i : Fin (generalJetSize n p)) (a : Fin p) : ℕ :=
  if a = (generalJetEquiv n p i).1 then (generalJetEquiv n p i).2.val
  else Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a

theorem generalIndexedJet_disc_factor (n p : ℕ)
    (i : Fin (generalJetSize n p)) (a : Fin p) :
    ∃ A : ℤ[X], (generalIndexedJetPoly n p i).comp
      (Li2.primeDiscSubstitution p a) =
        C ((p : ℤ) ^ (generalIndexedJetLocalOrder n p i a)) *
          X ^ (generalIndexedJetLocalOrder n p i a) * A := by
  by_cases he : a = (generalJetEquiv n p i).1
  · subst a
    obtain ⟨A, hA⟩ := Li2.classBasisPoly_own_expansion
      (Li2.primeCenter p)
      (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p)
      (generalJetEquiv n p i).1 (generalJetEquiv n p i).2.val (p : ℤ)
    refine ⟨C ((Li2.classProduct (Li2.primeCenter p)
      (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p)
      (generalJetEquiv n p i).1).eval (Li2.primeCenter p (generalJetEquiv n p i).1)) +
      C (p : ℤ) * A, ?_⟩
    simpa only [generalIndexedJetPoly, generalJetPoly,
      generalIndexedJetLocalOrder, if_pos rfl, Li2.primeDiscSubstitution] using hA
  · obtain ⟨A, hA⟩ := Li2.classBasisPoly_other_expansion
      (Li2.primeCenter p)
      (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p)
      (generalJetEquiv n p i).1 a (generalJetEquiv n p i).2.val (p : ℤ) he
    refine ⟨A, ?_⟩
    simpa only [generalIndexedJetPoly, generalJetPoly,
      generalIndexedJetLocalOrder, if_neg he, Li2.primeDiscSubstitution] using hA

#print axioms generalIndexedJet_disc_factor

end
end Li2Unified.Proofs.Hermite

end


end
