module
public import Li2Unified.Modular.Base.PrimeBasis

set_option backward.privateInPublic true

@[expose] public section

/-! The integer product basis, including its top-degree vector, is a p-unit basis.
The top-degree vector is stored FIRST. This order is used consistently below. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def primeJetEquiv (p : ℕ) (hp : 3 ≤ p) : Fin (2*p-3) ≃ PrimeJet p :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, primeJet_card p hp])

def primeIndexedPoly (p : ℕ) (hp : 3 ≤ p) (i : Fin (2*p-3)) : ℤ[X] :=
  primeJetPoly p (primeJetEquiv p hp i)

lemma primeJet_coordinates_injective (p : ℕ) :
    Function.Injective (fun a : PrimeJet p => (a.1, a.2.val)) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ hab
  simp only [Prod.mk.injEq] at hab
  rcases hab with ⟨rfl, hij⟩
  have h : i = j := Fin.ext hij
  cases h
  rfl

theorem primeIndexedPoly_independent (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (v : Fin (2*p-3) → ZMod p)
    (hv : (∑ a, C (v a) * (primeIndexedPoly p hp a).map (Int.castRingHom (ZMod p))) = 0) :
    v = 0 := by
  refine classBasis_independent (fun a => (primeCenter p a : ZMod p))
    (primeCenter_mod_injective p) (primeMultiplicity p)
    (fun a => (primeJetEquiv p hp a).1) (fun a => (primeJetEquiv p hp a).2.val)
    (fun a => (primeJetEquiv p hp a).2.isLt) ?_ v ?_
  · intro a b hcls hidx
    apply (primeJetEquiv p hp).injective
    apply primeJet_coordinates_injective p
    exact Prod.ext hcls hidx
  · simp only [primeIndexedPoly, primeJetPoly, classBasisPoly_map] at hv
    simpa only [classBasisPoly, classProduct, Int.coe_castRingHom] using hv

lemma primeIndexedPoly_natDegree_lt (p : ℕ) (hp : 3 ≤ p) (i : Fin (2*p-3)) :
    (primeIndexedPoly p hp i).natDegree < 2*p-3 :=
  primeJetPoly_natDegree_lt p hp _

def primeFullBasis (p : ℕ) (hp : 3 ≤ p) : Fin ((2*p-3)+1) → ℤ[X] :=
  Fin.cases (primeProduct p) (primeIndexedPoly p hp)

lemma primeFullBasis_natDegree_lt (p : ℕ) (hp : 3 ≤ p) (i : Fin ((2*p-3)+1)) :
    (primeFullBasis p hp i).natDegree < (2*p-3)+1 := by
  refine Fin.cases ?_ ?_ i
  · simpa only [primeFullBasis, Fin.cases_zero, primeProduct_natDegree p hp]
      using Nat.lt_succ_self (2*p-3)
  · intro j
    exact (primeIndexedPoly_natDegree_lt p hp j).trans (Nat.lt_succ_self _)

theorem primeFullBasis_independent (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (v : Fin ((2*p-3)+1) → ZMod p)
    (hv : (∑ a, C (v a) * (primeFullBasis p hp a).map (Int.castRingHom (ZMod p))) = 0) :
    v = 0 := by
  refine polynomial_family_independent_append
    (fun a => (primeIndexedPoly p hp a).map (Int.castRingHom (ZMod p)))
    (fun a => (natDegree_map_le).trans_lt (primeIndexedPoly_natDegree_lt p hp a))
    (primeIndexedPoly_independent p hp)
    ((primeProduct p).map (Int.castRingHom (ZMod p)))
    ((primeProduct_monic p).map _) ?_ v ?_
  · rw [(primeProduct_monic p).natDegree_map, primeProduct_natDegree p hp]
  · convert hv using 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    refine Fin.cases ?_ ?_ a
    · rfl
    · intro i; rfl

theorem primeFullBasis_det_unit (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (coeffMat fun a => (primeFullBasis p hp a).map (Int.castRingHom ℚ)).det ≠ 0 ∧
    padicValRat p (coeffMat fun a => (primeFullBasis p hp a).map (Int.castRingHom ℚ)).det = 0 :=
  coeffMat_det_unit_of_independent _ (primeFullBasis_natDegree_lt p hp)
    (primeFullBasis_independent p hp)

end
end Li2

end
