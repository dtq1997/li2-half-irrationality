module
public import Li2Unified.Modular.Base.PrimeFieldHighConstants
public import Li2Unified.Modular.Base.PrimeParameter

set_option backward.privateInPublic true

@[expose] public section

/-! Reduction of the three complete high-disc weights, including (-2)^a and -a. -/
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeField_two_ne_zero (hp4 : 3 < p) : (2:ZMod p) ≠ 0 := by
  intro he
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp he
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

lemma primeField_three_ne_zero (hp4 : 3 < p) : (3:ZMod p) ≠ 0 := by
  intro he
  have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp he
  have := Nat.le_of_dvd (by decide : 0 < 3) hd
  omega

lemma primeField_negativeTwo_pow_sub (hp4 : 3 < p) (ell : ℕ) (hl : ell ≤ p) :
    (-2:ZMod p)^(p-ell) = -2/(-2:ZMod p)^ell := by
  have hn : (-2:ZMod p) ≠ 0 := neg_ne_zero.mpr (primeField_two_ne_zero hp4)
  apply (eq_div_iff (pow_ne_zero ell hn)).mpr
  rw [← pow_add,Nat.sub_add_cancel hl,ZMod.pow_card]

theorem primeHighWeight_one (hp4 : 3 < p) :
    (-2:ZMod p)^(p-1)*(-((p-1:ℕ):ZMod p))*primeFieldLeadingUnit (p-1) = -2 := by
  rw [primeField_negativeTwo_pow_sub hp4 1 (by omega),
    primeField_cast_sub 1 (by omega),primeFieldLeadingUnit_high hp4 1 (by omega) (by omega)]
  have h2 := primeField_two_ne_zero hp4
  norm_num

theorem primeHighWeight_two (hp4 : 3 < p) :
    (-2:ZMod p)^(p-2)*(-((p-2:ℕ):ZMod p))*primeFieldLeadingUnit (p-2) = -1/4 := by
  rw [primeField_negativeTwo_pow_sub hp4 2 (by omega),
    primeField_cast_sub 2 (by omega),primeFieldLeadingUnit_high hp4 2 (by omega) (by omega)]
  have h2 := primeField_two_ne_zero hp4
  have h4 : (4:ZMod p) ≠ 0 := by convert pow_ne_zero 2 h2 using 1 <;> ring
  have h16 : (16:ZMod p) ≠ 0 := by convert pow_ne_zero 4 h2 using 1 <;> ring
  norm_num <;> field_simp <;> ring

theorem primeHighWeight_three (hp4 : 3 < p) :
    (-2:ZMod p)^(p-3)*(-((p-3:ℕ):ZMod p))*primeFieldLeadingUnit (p-3) = -1/6 := by
  rw [primeField_negativeTwo_pow_sub hp4 3 (by omega),
    primeField_cast_sub 3 (by omega),primeFieldLeadingUnit_high hp4 3 (by omega) (by omega)]
  have h2 := primeField_two_ne_zero hp4
  have h3 := primeField_three_ne_zero hp4
  have h6 : (6:ZMod p) ≠ 0 := by convert mul_ne_zero h2 h3 using 1 <;> ring
  have h72 : (72:ZMod p) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 3 h2) (pow_ne_zero 2 h3) using 1 <;> ring
  norm_num
  field_simp
  ring_nf
  simp [inv_mul_cancel₀ h72]

end
end Li2

end
