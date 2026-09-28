module
public import Li2Unified.Modular.Base.IntegerFamily
public import Mathlib.NumberTheory.Wilson
public import Mathlib.FieldTheory.Finite.Basic

set_option backward.privateInPublic true

@[expose] public section

/-! The exact finite-field polynomial identity for the ORIGINAL rising
product D_(p-1), reusing Mathlib's Wilson and Fermat theorems. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

lemma integerD_natDegree (m : ℕ) : (integerD m).natDegree = m := by
  unfold integerD
  rw [natDegree_prod_of_monic (Finset.Icc 1 m) (fun j : ℕ => X+C (j:ℤ))
    (fun j _ => monic_X_add_C (j:ℤ))]
  simp only [natDegree_X_add_C]
  simp

variable {p : ℕ} [hp : Fact p.Prime]

def primeFieldD (m : ℕ) : (ZMod p)[X] := (integerD m).map (Int.castRingHom (ZMod p))

lemma primeFieldD_product (m : ℕ) :
    primeFieldD (p := p) m = ∏ j ∈ Finset.Icc 1 m, (X+C (j:ZMod p)) := by
  simp only [primeFieldD, integerD, Polynomial.map_prod, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C, Int.coe_castRingHom, Int.cast_natCast]

lemma primeFieldD_natDegree (m : ℕ) : (primeFieldD (p := p) m).natDegree = m := by
  rw [primeFieldD, (integerD_monic m).natDegree_map, integerD_natDegree]

theorem primeFieldD_at_zero : (primeFieldD (p := p) (p-1)).eval 0 = -1 := by
  rw [primeFieldD_product]
  simp only [eval_prod, eval_add, eval_X, eval_C, zero_add]
  have he : Finset.Icc 1 (p-1) = Finset.Ico 1 p := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    have hpp := hp.out.pos
    omega
  rw [he, ZMod.prod_Ico_one_prime]

theorem primeFieldD_eval_nonzero (x : ZMod p) (hx : x ≠ 0) :
    (primeFieldD (p := p) (p-1)).eval x = 0 := by
  rw [primeFieldD_product, eval_prod]
  have hi : (-x).val ∈ Finset.Icc 1 (p-1) := by
    apply Finset.mem_Icc.mpr
    exact ⟨ZMod.val_pos.mpr (neg_ne_zero.mpr hx), by have := ZMod.val_lt (-x); omega⟩
  apply Finset.prod_eq_zero hi
  simp

theorem primeFieldD_identity : primeFieldD (p := p) (p-1) = X^(p-1)-1 := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (Function.injective_id)
  · intro x
    change (primeFieldD (p := p) (p-1)).eval x = (X^(p-1)-1 : (ZMod p)[X]).eval x
    by_cases hx : x = 0
    · subst x
      rw [primeFieldD_at_zero]
      simp [Nat.ne_of_gt (show 0 < p-1 by have := hp.out.two_le; omega)]
    · rw [primeFieldD_eval_nonzero x hx]
      simp [ZMod.pow_card_sub_one_eq_one hx]
  · rw [primeFieldD_natDegree, ZMod.card p]
    have hpp := hp.out.two_le
    apply max_lt (by omega)
    apply (natDegree_sub_le _ _).trans_lt
    simp only [natDegree_X_pow, natDegree_one]
    omega

end
end Li2

end
