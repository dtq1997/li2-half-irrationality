module
public import Li2Unified.Modular.Base.PrimeLowRationalLeading

set_option backward.privateInPublic true

@[expose] public section

namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem primeLowRationalWeight_unit (hp4 : 3 < p) (a : ℕ)
    (ha0 : 0 < a) (ha : a ≤ p-4) :
    primeLowRationalWeight a ≠ 0 ∧ padicValRat p (primeLowRationalWeight a) = 0 := by
  have hnat (k : ℕ) (hk0 : 0 < k) (hkp : k < p) :
      (k:ℚ) ≠ 0 ∧ padicValRat p (k:ℚ) = 0 := by
    refine ⟨by exact_mod_cast hk0.ne', ?_⟩
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd
      (Nat.not_dvd_of_pos_of_lt hk0 hkp)]
    rfl
  have hmul (x y : ℚ) (hx : x ≠ 0 ∧ padicValRat p x = 0)
      (hy : y ≠ 0 ∧ padicValRat p y = 0) :
      x*y ≠ 0 ∧ padicValRat p (x*y) = 0 :=
    ⟨mul_ne_zero hx.1 hy.1, by rw [padicValRat.mul hx.1 hy.1, hx.2, hy.2, add_zero]⟩
  have hpow (x : ℚ) (hx : x ≠ 0 ∧ padicValRat p x = 0) (k : ℕ) :
      x^k ≠ 0 ∧ padicValRat p (x^k) = 0 :=
    ⟨pow_ne_zero k hx.1, by rw [padicValRat.pow, hx.2, mul_zero]⟩
  have hdiv (x y : ℚ) (hx : x ≠ 0 ∧ padicValRat p x = 0)
      (hy : y ≠ 0 ∧ padicValRat p y = 0) :
      x/y ≠ 0 ∧ padicValRat p (x/y) = 0 :=
    ⟨div_ne_zero hx.1 hy.1, by rw [padicValRat.div hx.1 hy.1, hx.2, hy.2, sub_self]⟩
  have hA := hnat a ha0 (by omega)
  have h1 : (a:ℚ)+1 ≠ 0 ∧ padicValRat p ((a:ℚ)+1) = 0 := by
    simpa only [Nat.cast_add,Nat.cast_one] using! hnat (a+1) (by omega) (by omega)
  have h2 : (a:ℚ)+2 ≠ 0 ∧ padicValRat p ((a:ℚ)+2) = 0 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using! hnat (a+2) (by omega) (by omega)
  have h3 : (a:ℚ)+3 ≠ 0 ∧ padicValRat p ((a:ℚ)+3) = 0 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using! hnat (a+3) (by omega) (by omega)
  have hK := hdiv _ _ (hmul _ _ (hmul _ _ h1 h2) h3) (hpow _ hA 2)
  have hm2 : (-2:ℚ) ≠ 0 ∧ padicValRat p (-2:ℚ) = 0 :=
    ⟨by norm_num, by rw [padicValRat.neg, two_valuation_zero (by omega)]⟩
  have hmA : -(a:ℚ) ≠ 0 ∧ padicValRat p (-(a:ℚ)) = 0 :=
    ⟨neg_ne_zero.mpr hA.1, by rw [padicValRat.neg,hA.2]⟩
  exact hmul _ _ (hmul _ _ (hpow _ hm2 a) hmA) hK

end
end Li2

end
