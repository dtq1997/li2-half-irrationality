module
public import Li2Unified.Modular.Base.RationalBaseEvaluation

set_option backward.privateInPublic true

@[expose] public section

/-! Congruence of the actual prime parameter and the rational base parameter.
The pole range is literal j < p; no denominator crossing p is allowed. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma VG.mul_congr {a b c d s : ℚ} (hc : VG p c 0) (hb : VG p b 0)
    (hab : VG p (a-b) s) (hcd : VG p (c-d) s) : VG p (a*c-b*d) s := by
  have he : a*c-b*d = (a-b)*c+b*(c-d) := by ring
  rw [he]
  have hleft : VG p ((a-b)*c) s := by simpa using hab.mul hc
  have hright : VG p (b*(c-d)) s := by simpa using hb.mul hcd
  exact hleft.add hright

lemma VG.pow_congr {a b s : ℚ} (ha : VG p a 0) (hb : VG p b 0)
    (hab : VG p (a-b) s) (k : ℕ) : VG p (a^k-b^k) s := by
  induction k with
  | zero => simpa using VG.zero (p := p) s
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact VG.mul_congr ha (by simpa using hb.pow k) ih hab

lemma VG.inv_congr {a b s : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hia : VG p a⁻¹ 0) (hib : VG p b⁻¹ 0) (hab : VG p (a-b) s) :
    VG p (a⁻¹-b⁻¹) s := by
  have he : a⁻¹-b⁻¹ = -(a-b)*a⁻¹*b⁻¹ := by field_simp [ha, hb]; ring
  rw [he]
  simpa using (hab.neg.mul hia).mul hib

lemma negativeHalf_integral (hp2 : p ≠ 2) : VG p (-1/2:ℚ) 0 := by
  have h := rational_unit_inverse_VG (-2:ℚ) (by norm_num) (negative_two_valuation_zero hp2)
  convert h using 1 <;> norm_num

lemma primeParameter_integral (hp2 : p ≠ 2) : VG p (primeParameter p) 0 := by
  exact Or.inr (by rw [(primeParameter_unit hp2).2]; norm_num)

theorem primeParameter_inverse_congr (hp2 : p ≠ 2) :
    VG p ((primeParameter p)⁻¹-(-1/2:ℚ)⁻¹) 1 := by
  apply VG.inv_congr (primeParameter_unit hp2).1 (by norm_num)
  · exact rational_unit_inverse_VG _ (primeParameter_unit hp2).1 (primeParameter_unit hp2).2
  · convert (VG.intCast (p := p) (-2)) using 1 <;> norm_num
  · exact negativeHalf_prime_pow_congr hp2

theorem primeParameter_inverse_pow_congr (hp2 : p ≠ 2) (j : ℕ) :
    VG p ((primeParameter p)⁻¹^j-(-1/2:ℚ)⁻¹^j) 1 := by
  apply VG.pow_congr _ _ (primeParameter_inverse_congr hp2)
  · exact rational_unit_inverse_VG _ (primeParameter_unit hp2).1 (primeParameter_unit hp2).2
  · convert (VG.intCast (p := p) (-2)) using 1 <;> norm_num

theorem primeParameter_tau_congr (hp2 : p ≠ 2) (j : ℕ) (hj : j < p) :
    VG p (parameterTau (primeParameter p) j-parameterTau (-1/2) j) 1 := by
  unfold parameterTau
  rw [← Finset.sum_sub_distrib]
  apply VG.sum
  intro b hb
  have hb0 := (Finset.mem_Icc.mp hb).1
  have hbp : b < p := lt_of_le_of_lt (Finset.mem_Icc.mp hb).2 hj
  have hv : padicValRat p (b:ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd
      (Nat.not_dvd_of_pos_of_lt (by omega) hbp)]
    rfl
  have hi : VG p ((b:ℚ)⁻¹^2) 0 := by
    simpa using (rational_unit_inverse_VG (b:ℚ) (by exact_mod_cast (by omega : b ≠ 0)) hv).pow 2
  rw [← sub_div, div_eq_mul_inv, ← inv_pow]
  simpa using (VG.pow_congr (primeParameter_integral hp2)
    (negativeHalf_integral hp2) (negativeHalf_prime_pow_congr hp2) b).mul hi

lemma GV.derivative {f : ℚ[X]} {s : ℚ} (hf : GV p f s) : GV p f.derivative s := by
  intro k
  rw [coeff_derivative]
  simpa [mul_comm] using (hf (k+1)).mul (VG.natCast (p := p) (k+1))

theorem parameterG_prime_congr (hp4 : 3 < p) (f : ℚ[X]) (hf : GV p f 0) :
    VG p (parameterG (primeParameter p) f-parameterG (-1/2) f) 1 := by
  unfold parameterG Polynomial.sum
  rw [← Finset.sum_sub_distrib]
  apply VG.sum
  intro k _
  rw [← mul_sub]
  simpa using (hf k).mul (primeParameter_all_moments_congr (by omega) (by omega) k)

theorem parameterU_prime_congr (hp4 : 3 < p) (f : ℚ[X]) (hf : GV p f 0) :
    VG p (parameterU (primeParameter p) f-parameterU (-1/2) f) 1 := by
  apply parameterG_prime_congr hp4
  have hprod : GV p (X*f) 0 := by simpa using (GV.X (p := p)).mul hf
  exact hprod.derivative

theorem parameterV_prime_congr (hp4 : 3 < p) (f : ℚ[X]) (hf : GV p f 0) :
    VG p (parameterV (primeParameter p) f-parameterV (-1/2) f) 1 :=
  parameterG_prime_congr hp4 _ hf.derivative

end
end Li2

end
