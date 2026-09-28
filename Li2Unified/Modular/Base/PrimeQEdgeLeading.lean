module
public import Li2Unified.Modular.Base.PrimeReferenceDeterminant
public import Li2Unified.Modular.Base.PrimeReferenceBounds
public import Li2Unified.Modular.Base.DetCongruence
public import Li2Unified.Modular.Base.PrimitiveReduction

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeQ_positive_zpow :
    (p:ℚ)^(2*((p-1:ℕ):ℤ)) = (p:ℚ)^(2*(p-1)) := by
  rw [show (2:ℤ)*((p-1:ℕ):ℤ) = ((2*(p-1):ℕ):ℤ) by push_cast <;> ring]
  rw [zpow_natCast]

def primeQEdgeScale (hp4 : 3 < p) : ℚ :=
  (p:ℚ)^(2*(p-1))*primeNormalizedDetScale hp4

lemma primeQEdgeScale_spec (hp4 : 3 < p) :
    primeQEdgeScale hp4 ≠ 0 ∧
      padicValRat p (primeQEdgeScale hp4) = 2*((p-1:ℕ):ℤ) := by
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hu := primeNormalizedDetScale_unit hp4
  unfold primeQEdgeScale
  refine ⟨mul_ne_zero (pow_ne_zero _ hpq) hu.1, ?_⟩
  rw [padicValRat.mul (pow_ne_zero _ hpq) hu.1,
    padicValRat.pow,padicValRat.self hp.out.one_lt,hu.2]
  push_cast
  ring

end
end Li2

end
