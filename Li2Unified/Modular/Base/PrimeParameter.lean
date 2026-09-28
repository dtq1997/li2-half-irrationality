module
public import Li2Unified.Modular.Base.ParameterMoments
public import Li2Unified.Modular.Base.PrimitiveReduction
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.FieldSimp

set_option backward.privateInPublic true

@[expose] public section

/-! Fermat congruence and the p-integral moment parameter z=(-1/2)^p. -/
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma VG.intCast_of_dvd {a : ℤ} (ha : (p:ℤ) ∣ a) : VG p (a:ℚ) 1 := by
  obtain ⟨b, rfl⟩ := ha
  rw [Int.cast_mul, Int.cast_natCast]
  have ht := (VG.primePow (p := p) (1:ℤ)).mul (VG.intCast (p := p) b)
  simpa using ht

lemma prime_nat_valuation_zero {l : ℕ} (hl : l.Prime) (hpl : p ≠ l) :
    padicValRat p (l:ℚ) = 0 := by
  have hnd : ¬p ∣ l := fun h => hpl ((Nat.prime_dvd_prime_iff_eq hp.out hl).mp h)
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
  rfl

lemma negative_two_valuation_zero (hp2 : p ≠ 2) : padicValRat p (-2:ℚ) = 0 := by
  rw [padicValRat.neg]
  exact prime_nat_valuation_zero (by decide) hp2

lemma two_valuation_zero (hp2 : p ≠ 2) : padicValRat p (2:ℚ) = 0 :=
  prime_nat_valuation_zero (by decide) hp2

lemma three_valuation_zero (hp3 : p ≠ 3) : padicValRat p (3:ℚ) = 0 :=
  prime_nat_valuation_zero (by decide) hp3

theorem negativeHalf_prime_pow_congr (hp2 : p ≠ 2) :
    VG p ((-1/2:ℚ)^p-(-1/2:ℚ)) 1 := by
  have hmod : (((-2:ℤ)-(-2:ℤ)^p : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.pow_card, sub_self]
  have hdiv : (p:ℤ) ∣ (-2:ℤ)-(-2:ℤ)^p :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
  have hnum : VG p ((-2:ℚ)-(-2:ℚ)^p) 1 := by
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_neg, Int.cast_ofNat] using VG.intCast_of_dvd hdiv
  have hb : (-2:ℚ) ≠ 0 := by norm_num
  have hval : padicValRat p ((-2:ℚ)^p) = 0 := by
    rw [padicValRat.pow, negative_two_valuation_zero hp2]
    simp
  have hi : VG p ((-2:ℚ)^p)⁻¹ 0 := by
    simpa using VG.inv (p := p) (pow_ne_zero _ hb) (show (padicValRat p ((-2:ℚ)^p):ℚ) ≤ 0 by rw [hval]; norm_num)
  have hi2 : VG p (-2:ℚ)⁻¹ 0 := by
    simpa using VG.inv (p := p) hb (show (padicValRat p (-2:ℚ):ℚ) ≤ 0 by rw [negative_two_valuation_zero hp2]; norm_num)
  have he : (-1/2:ℚ)^p-(-1/2:ℚ) =
      ((-2:ℚ)-(-2:ℚ)^p)*((-2:ℚ)^p)⁻¹*(-2:ℚ)⁻¹ := by
    rw [show (-1/2:ℚ) = (-2:ℚ)⁻¹ by norm_num, inv_pow]
    field_simp
    <;> ring
  rw [he]
  simpa only [add_zero] using (hnum.mul hi).mul hi2

def primeParameter (p : ℕ) : ℚ := (-1/2:ℚ)^p

theorem primeParameter_unit (hp2 : p ≠ 2) :
    primeParameter p ≠ 0 ∧ padicValRat p (primeParameter p) = 0 := by
  have hhalf : (-1/2:ℚ) ≠ 0 := by norm_num
  refine ⟨pow_ne_zero _ hhalf, ?_⟩
  unfold primeParameter
  rw [padicValRat.pow]
  have hval : padicValRat p (-1/2:ℚ) = 0 := by
    rw [show (-1/2:ℚ) = (-2:ℚ)⁻¹ by norm_num, padicValRat.inv, negative_two_valuation_zero hp2]
    rfl
  rw [hval]
  simp

theorem primeParameter_one_sub_unit (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    1-primeParameter p ≠ 0 ∧ padicValRat p (1-primeParameter p) = 0 := by
  apply unit_of_VG_sub (c := 3/2) (by norm_num)
  · rw [padicValRat.div (by norm_num) (by norm_num),
      three_valuation_zero hp3, two_valuation_zero hp2]
    rfl
  · have h := (negativeHalf_prime_pow_congr hp2).neg
    have he : (1-primeParameter p)-(3/2:ℚ) = -((-1/2:ℚ)^p-(-1/2:ℚ)) := by
      unfold primeParameter
      ring
    rw [he]
    exact h

theorem primeParameter_moment_integral (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    VG p (primeParameter p/(1-primeParameter p)) 0 := by
  have hu := primeParameter_unit hp2
  have hv := primeParameter_one_sub_unit hp2 hp3
  have hz : VG p (primeParameter p) 0 := Or.inr (by rw [hu.2]; norm_num)
  have hi : VG p (1-primeParameter p)⁻¹ 0 := by
    simpa using VG.inv (p := p) hv.1 (show (padicValRat p (1-primeParameter p):ℚ) ≤ 0 by rw [hv.2]; norm_num)
  simpa only [div_eq_mul_inv, add_zero] using hz.mul hi

theorem primeParameter_moment_initial_congr (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    VG p (primeParameter p/(1-primeParameter p)-(-1/3:ℚ)) 1 := by
  have hu := primeParameter_one_sub_unit hp2 hp3
  have hi : VG p (1-primeParameter p)⁻¹ 0 := by
    simpa using VG.inv (p := p) hu.1 (show (padicValRat p (1-primeParameter p):ℚ) ≤ 0 by rw [hu.2]; norm_num)
  have h3 : VG p (3:ℚ)⁻¹ 0 := by
    simpa using VG.inv (p := p) (by norm_num : (3:ℚ) ≠ 0)
      (show (padicValRat p (3:ℚ):ℚ) ≤ 0 by rw [three_valuation_zero hp3]; norm_num)
  have h23 : VG p (2/3:ℚ) 0 := by
    simpa only [div_eq_mul_inv, add_zero] using! (VG.natCast (p := p) 2).mul h3
  have he : primeParameter p/(1-primeParameter p)-(-1/3:ℚ) =
      (primeParameter p-(-1/2:ℚ))*(1-primeParameter p)⁻¹*(2/3) := by
    field_simp [hu.1]
    <;> ring
  rw [he]
  simpa only [add_zero, primeParameter] using ((negativeHalf_prime_pow_congr hp2).mul hi).mul h23

theorem primeParameter_all_moments_congr (hp2 : p ≠ 2) (hp3 : p ≠ 3) (k : ℕ) :
    VG p (parameterMoment (primeParameter p) k-parameterMoment (-1/2) k) 1 := by
  apply parameterMoment_congr p _ _ _ (primeParameter_moment_integral hp2 hp3)
  · have h3 : VG p (3:ℚ)⁻¹ 0 := by
      simpa using VG.inv (p := p) (by norm_num : (3:ℚ) ≠ 0)
        (show (padicValRat p (3:ℚ):ℚ) ≤ 0 by rw [three_valuation_zero hp3]; norm_num)
    convert h3.neg using 1 <;> norm_num
  · convert primeParameter_moment_initial_congr hp2 hp3 using 1 <;> norm_num

end
end Li2

end
