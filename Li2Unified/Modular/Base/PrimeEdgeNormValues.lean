module
public import Li2Unified.Modular.Base.PrimeLocalUnitValues
public import Li2Unified.Modular.Base.PrimeRationalNormReduction

set_option backward.privateInPublic true

@[expose] public section

/-! The actual integral high-disc weights and product-basis units are
coefficientwise congruent to the specified rational constants. -/
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def primeHighDiscWeight (a : Fin p) : ℤ_[p] :=
  (-2:ℤ_[p])^a.val * (-(a.val:ℤ_[p])) * primeDiscUnitConstant a.val a.isLt

lemma primeHighDiscWeight_reduction (a : Fin p) :
    PadicInt.toZMod (primeHighDiscWeight a) =
      (-2:ZMod p)^a.val * (-(a.val:ZMod p)) * primeFieldLeadingUnit a.val := by
  simp only [primeHighDiscWeight,map_mul,map_pow,map_neg,map_ofNat,map_natCast,
    primeDiscUnitConstant_reduction]

theorem primeHighDiscWeight_one_norm (hp4 : 3 < p) :
    ‖(primeHighDiscWeight (p := p) ⟨p-1,by omega⟩:ℚ_[p])-(-2:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  have h := integral_norm_sub_rational_of_cleared_reduction
    (primeHighDiscWeight (p := p) ⟨p-1,by omega⟩) (-2) 1 (by decide) (by norm_num)
    (by simpa only [primeHighDiscWeight_reduction,Fin.val_mk,Int.cast_one,mul_one,Int.cast_neg,Int.cast_ofNat] using primeHighWeight_one hp4)
  simpa using h

theorem primeHighDiscWeight_two_norm (hp4 : 3 < p) :
    ‖(primeHighDiscWeight (p := p) ⟨p-2,by omega⟩:ℚ_[p])-(-1/4:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  have hd : (4:ZMod p) ≠ 0 := by convert pow_ne_zero 2 (primeField_two_ne_zero hp4) using 1 <;> ring
  have hr : PadicInt.toZMod (primeHighDiscWeight (p := p) ⟨p-2,by omega⟩)*4 = -1 := by
    rw [primeHighDiscWeight_reduction,primeHighWeight_two hp4]
    exact div_mul_cancel₀ _ hd
  simpa using integral_norm_sub_rational_of_cleared_reduction
    (primeHighDiscWeight (p := p) ⟨p-2,by omega⟩) (-1) 4 (by decide) (prime_four_valuation_zero hp4) (by simpa using hr)

theorem primeHighDiscWeight_three_norm (hp4 : 3 < p) :
    ‖(primeHighDiscWeight (p := p) ⟨p-3,by omega⟩:ℚ_[p])-(-1/6:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  have hd : (6:ZMod p) ≠ 0 := by
    convert mul_ne_zero (primeField_two_ne_zero hp4) (primeField_three_ne_zero hp4) using 1 <;> ring
  have hr : PadicInt.toZMod (primeHighDiscWeight (p := p) ⟨p-3,by omega⟩)*6 = -1 := by
    rw [primeHighDiscWeight_reduction,primeHighWeight_three hp4]
    exact div_mul_cancel₀ _ hd
  simpa using integral_norm_sub_rational_of_cleared_reduction
    (primeHighDiscWeight (p := p) ⟨p-3,by omega⟩) (-1) 6 (by decide) (prime_six_valuation_zero hp4) (by simpa using hr)

theorem primeLocalUnit_norm_from_field (a : Fin p) (u d : ℤ)
    (hd : d ≠ 0) (hv : padicValRat p (d:ℚ) = 0)
    (h : (primeLocalUnit p a:ZMod p)*(d:ZMod p) = (u:ZMod p)) :
    ‖(primeLocalUnit p a:ℚ_[p])-(u:ℚ_[p])/(d:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  have hh := integral_norm_sub_rational_of_cleared_reduction (p := p)
    (primeLocalUnit p a:ℤ_[p]) u d hd hv (by simpa only [map_intCast] using h)
  simpa only [PadicInt.coe_intCast] using hh

theorem primeLocalUnit_zero_norm (hp4 : 3 < p) :
    ‖(primeLocalUnit p ⟨0,by omega⟩:ℚ_[p])-(-1/6:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  have hd : (6:ZMod p) ≠ 0 := by
    convert mul_ne_zero (primeField_two_ne_zero hp4) (primeField_three_ne_zero hp4) using 1 <;> ring
  apply primeLocalUnit_norm_from_field _ (-1) 6 (by decide) (prime_six_valuation_zero hp4)
  rw [primeLocalUnit_zero_value hp4]
  simpa using (div_mul_cancel₀ (-1:ZMod p) hd)

theorem primeLocalUnit_high_one_norm (hp4 : 3 < p) :
    ‖(primeLocalUnit p ⟨p-1,by omega⟩:ℚ_[p])-(1/2:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  apply primeLocalUnit_norm_from_field _ 1 2 (by decide) (two_valuation_zero (by omega))
  rw [primeLocalUnit_high_one_value hp4]
  simpa using (div_mul_cancel₀ (1:ZMod p) (primeField_two_ne_zero hp4))

theorem primeLocalUnit_high_two_norm (hp4 : 3 < p) :
    ‖(primeLocalUnit p ⟨p-2,by omega⟩:ℚ_[p])-(-1:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  have h := primeLocalUnit_norm_from_field (p := p) ⟨p-2,by omega⟩ (-1) 1 (by decide) (by norm_num)
    (by simpa using primeLocalUnit_high_two_value hp4)
  simpa using h

theorem primeLocalUnit_high_three_norm (hp4 : 3 < p) :
    ‖(primeLocalUnit p ⟨p-3,by omega⟩:ℚ_[p])-(1/2:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  apply primeLocalUnit_norm_from_field _ 1 2 (by decide) (two_valuation_zero (by omega))
  rw [primeLocalUnit_high_three_value hp4]
  simpa using (div_mul_cancel₀ (1:ZMod p) (primeField_two_ne_zero hp4))

end
end Li2

end
