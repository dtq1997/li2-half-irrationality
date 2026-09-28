module
public import Li2Unified.Modular.Base.PrimeBlockIndex
public import Li2Unified.Modular.Base.PrimeCrossValuation

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ}

lemma rational_prime_unit_finset_prod [Fact p.Prime] {ι : Type*}
    (S : Finset ι) (u : ι → ℚ)
    (hu : ∀ i ∈ S, u i ≠ 0 ∧ padicValRat p (u i) = 0) :
    (∏ i ∈ S, u i) ≠ 0 ∧ padicValRat p (∏ i ∈ S, u i) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      have hA := hu a (Finset.mem_insert_self a S)
      have hS := ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_insert ha]
      exact ⟨mul_ne_zero hA.1 hS.1, by rw [padicValRat.mul hA.1 hS.1, hA.2, hS.2, add_zero]⟩

def primeNormalizedDetScale (hp4 : 3 < p) : ℚ :=
  ((∏ x : PrimeBlockIndex p, primeBlockUnitScale hp4 x) *
    (coeffMat fun a => (primeOriginalBasis p (by omega) a).map (Int.castRingHom ℚ)).det)^2

theorem primeNormalizedDetScale_unit [Fact p.Prime] (hp4 : 3 < p) :
    primeNormalizedDetScale hp4 ≠ 0 ∧ padicValRat p (primeNormalizedDetScale hp4) = 0 := by
  have hs := rational_prime_unit_finset_prod (p := p) Finset.univ
    (primeBlockUnitScale hp4) (fun x _ => primeBlockUnitScale_unit hp4 x)
  have hb := primeOriginalBasis_det_unit p (by omega)
  have hne := mul_ne_zero hs.1 hb.1
  unfold primeNormalizedDetScale
  refine ⟨pow_ne_zero 2 hne, ?_⟩
  rw [padicValRat.pow, padicValRat.mul hs.1 hb.1, hs.2, hb.2]
  norm_num

end
end Li2

end
