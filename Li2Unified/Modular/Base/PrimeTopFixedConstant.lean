module
public import Li2Unified.Modular.Base.PrimeTopSupport

set_option backward.privateInPublic true

@[expose] public section

/-! The actual four-disc top-top sum has the specified rational value modulo p.
A single common p-unit denominator keeps every residue reduction integral. -/
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def primeTopIntegralNumerator (hp4 : 3 < p) : ℤ_[p] :=
  -35546*(primeLocalUnit p ⟨0,by omega⟩:ℤ_[p])^2*primeDiscUnitConstant 0 (by omega) +
    2128*(primeHighDiscWeight (p := p) ⟨p-1,by omega⟩*(primeLocalUnit p ⟨p-1,by omega⟩:ℤ_[p])^2 +
      primeHighDiscWeight (p := p) ⟨p-2,by omega⟩*(primeLocalUnit p ⟨p-2,by omega⟩:ℤ_[p])^2 +
      primeHighDiscWeight (p := p) ⟨p-3,by omega⟩*(primeLocalUnit p ⟨p-3,by omega⟩:ℤ_[p])^2)

theorem primeTopIntegralNumerator_reduction (hp4 : 3 < p) :
    PadicInt.toZMod (primeTopIntegralNumerator (p := p) hp4) = -7609 := by
  simp only [primeTopIntegralNumerator,map_add,map_mul,map_neg,map_pow,map_ofNat,map_intCast,
    primeDiscUnitConstant_reduction,primeHighDiscWeight_reduction,Fin.val_mk]
  rw [primeLocalUnit_zero_value hp4,primeLocalUnit_high_one_value hp4,
    primeLocalUnit_high_two_value hp4,primeLocalUnit_high_three_value hp4,
    primeFieldLeadingUnit_zero hp4,primeHighWeight_one hp4,primeHighWeight_two hp4,
    primeHighWeight_three hp4]
  have h2 := primeField_two_ne_zero hp4
  have h4 : (4:ZMod p) ≠ 0 := by convert pow_ne_zero 2 h2 using 1 <;> ring
  have h6 : (6:ZMod p) ≠ 0 := by convert mul_ne_zero h2 (primeField_three_ne_zero hp4) using 1 <;> ring
  field_simp
  <;> ring

theorem primeTopLeadingSum_eq_integral (hp4 : 3 < p) :
    primeTopLeadingSum (p := p) = (primeTopIntegralNumerator (p := p) hp4:ℚ_[p])/72 := by
  rw [primeTopLeadingSum_weighted hp4]
  simp only [primeTopIntegralNumerator,PadicInt.coe_add,PadicInt.coe_mul,PadicInt.coe_neg,
    PadicInt.coe_pow,PadicInt.coe_intCast,PadicInt.coe_natCast]
  have h35546 : ((35546 : ℤ_[p]) : ℚ_[p]) = 35546 := rfl
  have h2128 : ((2128 : ℤ_[p]) : ℚ_[p]) = 2128 := rfl
  simp only [h35546,h2128]
  field_simp
  <;> ring

lemma prime_seventytwo_valuation_zero (hp4 : 3 < p) : padicValRat p (72:ℚ) = 0 := by
  rw [show (72:ℚ)=2^3*3^2 by norm_num,padicValRat.mul (by norm_num) (by norm_num),
    padicValRat.pow (by norm_num : (2:ℚ) ≠ 0),padicValRat.pow (by norm_num : (3:ℚ) ≠ 0),
    two_valuation_zero (by omega),three_valuation_zero (by omega)]
  norm_num

theorem primeTopLeadingSum_norm (hp4 : 3 < p) :
    ‖primeTopLeadingSum (p := p)-(-7609/72:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  have h := integral_norm_sub_rational_of_cleared_reduction
    (primeTopIntegralNumerator (p := p) hp4) (-7609) 1 (by decide) (by norm_num)
    (by simpa using primeTopIntegralNumerator_reduction (p := p) hp4)
  have hn : ‖(72:ℚ_[p])‖ = 1 := by
    have hu := PadicInt.norm_units (integralRationalUnit (p := p) (72:ℚ) (by norm_num)
      (prime_seventytwo_valuation_zero hp4))
    change ‖(((integralRationalUnit (p := p) (72:ℚ) (by norm_num)
      (prime_seventytwo_valuation_zero hp4):ℤ_[p]ˣ):ℤ_[p]):ℚ_[p])‖ = 1 at hu
    simpa only [integralRationalUnit_coe,Rat.cast_ofNat] using hu
  rw [primeTopLeadingSum_eq_integral hp4,← sub_div,norm_div,hn,div_one]
  simpa using h

end
end Li2

end
