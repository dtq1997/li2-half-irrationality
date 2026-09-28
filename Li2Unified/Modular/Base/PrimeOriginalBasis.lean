module
public import Li2Unified.Modular.Base.PrimeBasisChange

set_option backward.privateInPublic true

@[expose] public section

/-! Reindex the p-unit product basis to the literal matrix order 2(p-1). -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

theorem polynomial_family_independent_reindex {F : Type*} [Field F] {m n : ℕ}
    (e : Fin m ≃ Fin n) (E : Fin n → F[X])
    (hind : ∀ v : Fin n → F, (∑ a, C (v a) * E a) = 0 → v = 0)
    (v : Fin m → F) (hv : (∑ a, C (v a) * E (e a)) = 0) : v = 0 := by
  have ht : (∑ b, C (v (e.symm b)) * E b) = 0 := by
    rw [← Equiv.sum_comp e (fun b => C (v (e.symm b)) * E b)]
    simpa only [Equiv.symm_apply_apply] using hv
  have hz := hind (fun b => v (e.symm b)) ht
  funext a
  simpa only [Equiv.symm_apply_apply, Pi.zero_apply] using congrFun hz (e a)

lemma primeBasisSize (p : ℕ) (hp : 3 ≤ p) : 2*(p-1) = (2*p-3)+1 := by omega

def primeOriginalBasis (p : ℕ) (hp : 3 ≤ p) (a : Fin (2*(p-1))) : ℤ[X] :=
  primeFullBasis p hp (finCongr (primeBasisSize p hp) a)

lemma primeOriginalBasis_natDegree_lt (p : ℕ) (hp : 3 ≤ p) (a : Fin (2*(p-1))) :
    (primeOriginalBasis p hp a).natDegree < 2*(p-1) := by
  rw [primeBasisSize p hp]
  exact primeFullBasis_natDegree_lt p hp _

theorem primeOriginalBasis_independent (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (v : Fin (2*(p-1)) → ZMod p)
    (hv : (∑ a, C (v a) * (primeOriginalBasis p hp a).map (Int.castRingHom (ZMod p))) = 0) :
    v = 0 :=
  polynomial_family_independent_reindex (finCongr (primeBasisSize p hp))
    (fun a => (primeFullBasis p hp a).map (Int.castRingHom (ZMod p)))
    (primeFullBasis_independent p hp) v hv

theorem primeOriginalBasis_det_unit (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (coeffMat fun a => (primeOriginalBasis p hp a).map (Int.castRingHom ℚ)).det ≠ 0 ∧
    padicValRat p (coeffMat fun a => (primeOriginalBasis p hp a).map (Int.castRingHom ℚ)).det = 0 :=
  coeffMat_det_unit_of_independent _ (primeOriginalBasis_natDegree_lt p hp)
    (primeOriginalBasis_independent p hp)

end
end Li2

end
