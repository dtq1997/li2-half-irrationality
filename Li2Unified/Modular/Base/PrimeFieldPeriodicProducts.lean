module
public import Li2Unified.Modular.Base.PrimeFieldUnitConstants
public import Mathlib.Algebra.BigOperators.Intervals

set_option backward.privateInPublic true

@[expose] public section

/-! Complete period products of the actual nonmatching factors, not a
derivative proxy for their product. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def primeFieldUnitFactor (a j : ℕ) : ZMod p :=
  if j%p ≠ a then (j:ZMod p)-(a:ZMod p) else 1

def primeFieldUnitProduct (a m : ℕ) : ZMod p :=
  ∏ j ∈ Finset.Icc 1 m, primeFieldUnitFactor (p := p) a j

lemma primeFieldUnitProduct_filter (a m : ℕ) :
    primeFieldUnitProduct (p := p) a m =
      ∏ j ∈ (Finset.Icc 1 m).filter (fun j => j%p ≠ a),
        ((j:ZMod p)-(a:ZMod p)) := by
  simp only [primeFieldUnitProduct, primeFieldUnitFactor, Finset.prod_filter]

lemma primeFieldUnitProduct_succ (a m : ℕ) :
    primeFieldUnitProduct (p := p) a (m+1) =
      primeFieldUnitProduct a m * primeFieldUnitFactor a (m+1) := by
  exact Finset.prod_Icc_succ_top (by omega) _

lemma primeFieldUnitFactor_period (a j : ℕ) :
    primeFieldUnitFactor (p := p) a (j+p) = primeFieldUnitFactor a j := by
  simp [primeFieldUnitFactor, Nat.add_mod]

theorem primeFieldUnitProduct_add_period (a m : ℕ) :
    primeFieldUnitProduct (p := p) a (p+m) =
      primeFieldUnitProduct a p * primeFieldUnitProduct a m := by
  induction m with
  | zero => simp [primeFieldUnitProduct]
  | succ m ih =>
    rw [show p+(m+1) = (p+m)+1 by omega, primeFieldUnitProduct_succ, ih,
      primeFieldUnitProduct_succ,
      show p+m+1 = (m+1)+p by omega, primeFieldUnitFactor_period]
    ring

theorem primeFieldUnitProduct_periods (a k m : ℕ) :
    primeFieldUnitProduct (p := p) a (k*p+m) =
      primeFieldUnitProduct a p ^ k * primeFieldUnitProduct a m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k+1)*p+m = p+(k*p+m) by ring, primeFieldUnitProduct_add_period, ih,
      pow_succ]
    ring

theorem primeFieldUnitProduct_numerator_zero :
    primeFieldUnitProduct (p := p) 0 (p-1) = -1 := by
  rw [← primeFieldD_at_zero, primeFieldD_product, eval_prod]
  unfold primeFieldUnitProduct
  apply Finset.prod_congr rfl
  intro j hj
  obtain ⟨hj0,hjp⟩ := Finset.mem_Icc.mp hj
  have hjp' : j < p := by have := hp.out.pos; omega
  simp [primeFieldUnitFactor, Nat.mod_eq_of_lt hjp', Nat.ne_of_gt hj0]

theorem primeFieldUnitProduct_numerator_nonzero (a : ℕ) (ha0 : 0 < a) (ha : a < p) :
    primeFieldUnitProduct (p := p) a (p-1) = (a:ZMod p)⁻¹ := by
  rw [primeFieldUnitProduct_filter]
  have hs : (Finset.Icc 1 (p-1)).filter (fun j => j%p ≠ a) =
      (Finset.Icc 1 (p-1)).erase a := by
    ext j
    by_cases hj : j ∈ Finset.Icc 1 (p-1)
    · have hjp : j < p := by have := (Finset.mem_Icc.mp hj).2; omega
      simp [hj, Nat.mod_eq_of_lt hjp, ne_comm]
    · simp [hj]
  rw [hs, prime_numerator_unit_nonzero a ha0 ha]

theorem primeFieldUnitProduct_full_period (a : ℕ) (ha : a < p) :
    primeFieldUnitProduct (p := p) a p = -1 := by
  have hrec := primeFieldUnitProduct_succ (p := p) a (p-1)
  rw [Nat.sub_add_cancel hp.out.pos] at hrec
  rw [hrec]
  by_cases ha0 : a = 0
  · subst a
    rw [primeFieldUnitProduct_numerator_zero]
    simp [primeFieldUnitFactor]
  · rw [primeFieldUnitProduct_numerator_nonzero a (Nat.pos_of_ne_zero ha0) ha]
    have ha' : (a:ZMod p) ≠ 0 := by
      intro h
      have hv := congrArg ZMod.val h
      simp only [ZMod.val_natCast_of_lt ha, ZMod.val_zero] at hv
      exact ha0 hv
    simp [primeFieldUnitFactor, ha0, Ne.symm ha0, ha']

theorem primeFieldUnitProduct_denominator (hp4 : 3 < p) (a : ℕ) (ha : a < p) :
    primeFieldUnitProduct (p := p) a (4*(p-1)) =
      -primeFieldUnitProduct a (p-4) := by
  rw [show 4*(p-1) = 3*p+(p-4) by omega, primeFieldUnitProduct_periods,
    primeFieldUnitProduct_full_period a ha]
  ring

end
end Li2

end
