module
public import Li2Unified.Modular.Base.PrimeFieldPeriodicProducts

set_option backward.privateInPublic true

@[expose] public section

/-! Leading constants computed from the literal finite products of all
nonmatching numerator and denominator factors. -/
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeField_cast_sub (s : ℕ) (hs : s ≤ p) :
    ((p-s:ℕ):ZMod p) = -(s:ZMod p) := by
  rw [Nat.cast_sub hs]
  simp

theorem primeFieldUnitProduct_ne_zero (a m : ℕ) (ha : a < p) :
    primeFieldUnitProduct (p := p) a m ≠ 0 := by
  unfold primeFieldUnitProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  unfold primeFieldUnitFactor
  split_ifs with hj
  · apply sub_ne_zero.mpr
    intro he
    have h := (ZMod.natCast_eq_natCast_iff' j a p).mp he
    exact hj (h.trans (Nat.mod_eq_of_lt ha))
  · exact one_ne_zero

theorem primeFieldUnitProduct_last_three (hp4 : 3 < p) (a : ℕ) :
    primeFieldUnitProduct (p := p) a (p-1) =
      primeFieldUnitProduct a (p-4) * primeFieldUnitFactor a (p-3) *
        primeFieldUnitFactor a (p-2) * primeFieldUnitFactor a (p-1) := by
  rw [show p-1 = (p-2)+1 by omega, primeFieldUnitProduct_succ,
    show p-2 = (p-3)+1 by omega, primeFieldUnitProduct_succ,
    show p-3 = (p-4)+1 by omega, primeFieldUnitProduct_succ]

lemma primeFieldUnitFactor_tail (hp4 : 3 < p) (a s : ℕ)
    (hs : 1 ≤ s) (hs3 : s ≤ 3) :
    primeFieldUnitFactor (p := p) a (p-s) =
      if p-s ≠ a then -(s:ZMod p)-(a:ZMod p) else 1 := by
  have hsp : p-s < p := by omega
  simp only [primeFieldUnitFactor, Nat.mod_eq_of_lt hsp,
    primeField_cast_sub (p := p) s (by omega)]

def primeFieldLeadingUnit (a : ℕ) : ZMod p :=
  primeFieldUnitProduct (p := p) a (p-1)^3 /
    primeFieldUnitProduct a (4*(p-1))

theorem primeFieldLeadingUnit_low (hp4 : 3 < p) (a : ℕ)
    (ha0 : 0 < a) (ha : a ≤ p-4) :
    primeFieldLeadingUnit (p := p) a =
      ((a:ZMod p)+1)*((a:ZMod p)+2)*((a:ZMod p)+3)/(a:ZMod p)^2 := by
  have hap : a < p := by omega
  have he := primeFieldUnitProduct_last_three (p := p) hp4 a
  rw [primeFieldUnitProduct_numerator_nonzero a ha0 hap,
    primeFieldUnitFactor_tail hp4 a 3 (by omega) (by omega),
    primeFieldUnitFactor_tail hp4 a 2 (by omega) (by omega),
    primeFieldUnitFactor_tail hp4 a 1 (by omega) (by omega),
    if_pos (by omega), if_pos (by omega), if_pos (by omega)] at he
  have hc : primeFieldUnitProduct (p := p) a (4*(p-1)) *
      (((a:ZMod p)+1)*((a:ZMod p)+2)*((a:ZMod p)+3)) = (a:ZMod p)⁻¹ := by
    rw [primeFieldUnitProduct_denominator hp4 a hap, he]
    push_cast
    ring
  unfold primeFieldLeadingUnit
  rw [primeFieldUnitProduct_numerator_nonzero a ha0 hap]
  apply (div_eq_iff (primeFieldUnitProduct_ne_zero a _ hap)).mpr
  simp only [div_eq_mul_inv, ← inv_pow]
  calc
    (a:ZMod p)⁻¹^3 = (a:ZMod p)⁻¹^2 *
        (primeFieldUnitProduct a (4*(p-1)) *
          (((a:ZMod p)+1)*((a:ZMod p)+2)*((a:ZMod p)+3))) := by rw [hc]; ring
    _ = _ := by ring

theorem primeFieldLeadingUnit_zero (hp4 : 3 < p) :
    primeFieldLeadingUnit (p := p) 0 = 6 := by
  have he := primeFieldUnitProduct_last_three (p := p) hp4 0
  rw [primeFieldUnitProduct_numerator_zero,
    primeFieldUnitFactor_tail hp4 0 3 (by omega) (by omega),
    primeFieldUnitFactor_tail hp4 0 2 (by omega) (by omega),
    primeFieldUnitFactor_tail hp4 0 1 (by omega) (by omega),
    if_pos (by omega), if_pos (by omega), if_pos (by omega)] at he
  unfold primeFieldLeadingUnit
  rw [primeFieldUnitProduct_numerator_zero]
  apply (div_eq_iff (primeFieldUnitProduct_ne_zero 0 _ hp.out.pos)).mpr
  rw [primeFieldUnitProduct_denominator hp4 0 hp.out.pos]
  norm_num at he ⊢
  linear_combination he

end
end Li2

end
