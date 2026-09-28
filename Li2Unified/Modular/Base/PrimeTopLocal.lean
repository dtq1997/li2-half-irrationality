module
public import Li2Unified.Modular.Base.PrimeAugmentedOther

set_option backward.privateInPublic true

@[expose] public section

/-! All local contributions to the original highest-degree self-pairing.
The zero disc and all three high discs contribute at the same order. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem fieldPolynomial_prime_power_bound (F : (ℚ_[p])[X]) (k m : ℕ)
    (hF : ∀ n, ‖F.coeff n‖ ≤ ‖(p:ℚ_[p])‖^m) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^k)*F).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(k+m) := by
  rw [coeff_C_mul,norm_mul,norm_pow,pow_add]
  exact mul_le_mul_of_nonneg_left (hF n) (by positivity)

end
end Li2

end
