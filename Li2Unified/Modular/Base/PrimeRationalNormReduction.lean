module
public import Li2Unified.Modular.Base.PrimeNormReduction
public import Li2Unified.Modular.Base.PrimeHighWeights

set_option backward.privateInPublic true

@[expose] public section

/-! Clear a rational denominator that is a p-unit before reducing an
integral quantity, then recover the coefficient norm estimate. -/
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem integral_norm_sub_rational_of_cleared_reduction (x : ℤ_[p]) (a d : ℤ)
    (hd : d ≠ 0) (hv : padicValRat p (d:ℚ) = 0)
    (h : PadicInt.toZMod x*(d:ZMod p) = (a:ZMod p)) :
    ‖(x:ℚ_[p])-(a:ℚ_[p])/(d:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  have hr : PadicInt.toZMod (x*(d:ℤ_[p])) = PadicInt.toZMod (a:ℤ_[p]) := by
    simpa only [map_mul,map_intCast] using h
  have hb := integral_norm_sub_le_prime_of_reduction _ _ hr
  have hn : ‖(d:ℚ_[p])‖ = 1 := by
    have hu := PadicInt.norm_units (integralRationalUnit (p := p) (d:ℚ) (by exact_mod_cast hd) hv)
    change ‖(((integralRationalUnit (p := p) (d:ℚ) (by exact_mod_cast hd) hv:ℤ_[p]ˣ):ℤ_[p]):ℚ_[p])‖ = 1 at hu
    simpa only [integralRationalUnit_coe,Rat.cast_intCast] using hu
  have hdq : (d:ℚ_[p]) ≠ 0 := by exact_mod_cast hd
  have he : (x:ℚ_[p])-(a:ℚ_[p])/(d:ℚ_[p]) =
      ((x:ℚ_[p])*(d:ℚ_[p])-(a:ℚ_[p]))/(d:ℚ_[p]) := by field_simp
  rw [he,norm_div,hn,div_one]
  change ‖((x*(d:ℤ_[p])-(a:ℤ_[p]):ℤ_[p]):ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ at hb
  simpa only [PadicInt.coe_sub,PadicInt.coe_mul,PadicInt.coe_intCast,
    PadicInt.coe_natCast] using hb

lemma prime_six_valuation_zero (hp4 : 3 < p) : padicValRat p (6:ℚ) = 0 := by
  rw [show (6:ℚ)=2*3 by norm_num,padicValRat.mul (by norm_num) (by norm_num),
    two_valuation_zero (by omega),three_valuation_zero (by omega)]
  ring

end
end Li2

end
