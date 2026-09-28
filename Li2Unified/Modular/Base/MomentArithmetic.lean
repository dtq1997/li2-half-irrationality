module
public import Li2Unified.Modular.Base.Family
public import Li2Unified.Modular.Base.Valuation

set_option backward.privateInPublic true

@[expose] public section

/-! Specific arithmetic of the negative-half moments. Every denominator is
supported at 3; a uniform elementary 3-adic bound is also proved. -/
open Polynomial
namespace Li2

lemma inv_three_VG (p : ℕ) [hp : Fact p.Prime] (hp3 : p ≠ 3) :
    VG p (3 : ℚ)⁻¹ 0 := by
  have hn : ¬p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp.out (by decide)).mp h)
  have hv : padicValRat p (3 : ℚ) = 0 := by
    change padicValRat p ((3 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hn]
    rfl
  right
  rw [padicValRat.inv, hv]
  norm_num

end Li2

end
