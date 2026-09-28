module
public import Li2Unified.Modular.Base.PrimeFieldProducts

set_option backward.privateInPublic true

@[expose] public section

/-! First local unit constants, derived from the literal finite-field rising
product and its derivative. Denominator constants are not asserted here. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeField_pred_cast : ((p-1:ℕ):ZMod p) = -1 := by
  have he : ((p-1:ℕ):ZMod p)+1 = 0 := by
    have he' : ((p-1+1:ℕ):ZMod p) = 0 := by
      rw [Nat.sub_add_cancel hp.out.pos]
      simp
    simpa only [Nat.cast_add, Nat.cast_one] using he'
  exact eq_neg_of_add_eq_zero_left he

theorem primeFieldD_derivative_eval (x : ZMod p) (hx : x ≠ 0) :
    (primeFieldD (p := p) (p-1)).derivative.eval x = -x⁻¹ := by
  have hpow : x^(p-2)*x = 1 := by
    rw [← pow_succ, show p-2+1 = p-1 by have := hp.out.two_le; omega,
      ZMod.pow_card_sub_one_eq_one hx]
  have hi : x^(p-2) = x⁻¹ := eq_inv_of_mul_eq_one_left hpow
  rw [primeFieldD_identity]
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero,
    eval_mul, eval_C, eval_pow, eval_X, primeField_pred_cast,
    Nat.sub_sub, hi]
  norm_num

theorem prime_numerator_unit_nonzero (a : ℕ) (ha0 : 0 < a) (ha : a < p) :
    (∏ j ∈ (Finset.Icc 1 (p-1)).erase a, ((j:ZMod p)-(a:ZMod p))) = (a:ZMod p)⁻¹ := by
  have haS : a ∈ Finset.Icc 1 (p-1) := Finset.mem_Icc.mpr ⟨ha0, by omega⟩
  have hf : primeFieldD (p := p) (p-1) =
      (X+C (a:ZMod p))*∏ j ∈ (Finset.Icc 1 (p-1)).erase a, (X+C (j:ZMod p)) := by
    rw [primeFieldD_product]
    exact (Finset.mul_prod_erase _ _ haS).symm
  have ha' : (a:ZMod p) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    simp only [ZMod.val_natCast_of_lt ha, ZMod.val_zero] at hv
    omega
  have he := primeFieldD_derivative_eval (-(a:ZMod p)) (neg_ne_zero.mpr ha')
  rw [hf, derivative_mul] at he
  simpa only [eval_add, eval_mul, eval_prod, derivative_add, derivative_X,
    derivative_C, add_zero, eval_one, eval_X, eval_C, neg_add_cancel, zero_mul,
    one_mul, neg_inv, neg_neg, neg_add_eq_sub] using he

end
end Li2

end
