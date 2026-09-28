module
public import Li2Unified.Modular.Base.PrimeActualLowLeading

set_option backward.privateInPublic true

@[expose] public section

/-! The actual original numerator is the sum of all disc polynomials. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeDiscScale_ne_zero (hp4 : 3 < p) (a : Fin p) : primeDiscScale a ≠ 0 := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold primeDiscScale
  split_ifs <;> simp_all only [ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true, one_ne_zero]

end
end Li2

end
