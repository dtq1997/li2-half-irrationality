module
public import Li2Unified.Modular.Base.PadicParameterFunctional
public import Li2Unified.Modular.Base.PrimeParameter
public import Li2Unified.Modular.Base.Family

set_option backward.privateInPublic true

@[expose] public section

/-! The literal simple-pole values, including the pole at zero. All denominators
in tau_j are integral when j < p. The actual prime parameter has valuation zero. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def parameterTau (z : ℚ) (j : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 j, z^b/(b:ℚ)^2

lemma parameterTau_negHalf (j : ℕ) : parameterTau (-1/2) j = tau j := rfl

lemma rational_unit_inverse_VG (z : ℚ) (hz : z ≠ 0) (hv : padicValRat p z = 0) :
    VG p z⁻¹ 0 := by
  simpa using VG.inv (p := p) hz (show (padicValRat p z:ℚ) ≤ 0 by rw [hv]; norm_num)

lemma parameterTau_VG (z : ℚ) (hz : VG p z 0) (j : ℕ) (hj : j < p) :
    VG p (parameterTau z j) 0 := by
  apply VG.sum
  intro b hb
  have hb0 : 0 < b := (Finset.mem_Icc.mp hb).1
  have hbp : b < p := lt_of_le_of_lt (Finset.mem_Icc.mp hb).2 hj
  have hbne : (b:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb0)
  have hv : padicValRat p (b:ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd
      (Nat.not_dvd_of_pos_of_lt hb0 hbp)]
    rfl
  have hi : VG p ((b:ℚ)⁻¹^2) 0 := by
    simpa using (rational_unit_inverse_VG (b:ℚ) hbne hv).pow 2
  have hzpow : VG p (z^b) 0 := by simpa using hz.pow b
  simpa only [div_eq_mul_inv, inv_pow, add_zero] using hzpow.mul hi

def integralParameterTau (z : ℚ) (hz : VG p z 0) (j : ℕ) (hj : j < p) : ℤ_[p] :=
  integralRational (parameterTau z j) (parameterTau_VG z hz j hj)

def integralParameterInvPow (z : ℚ) (hz : z ≠ 0) (hv : padicValRat p z = 0) (j : ℕ) : ℤ_[p] :=
  integralRational (z⁻¹^j) (by simpa using (rational_unit_inverse_VG z hz hv).pow j)

def integralUPole (z : ℚ) (hz : z ≠ 0) (hv : padicValRat p z = 0)
    (j : ℕ) (hj : j < p) : (ℤ_[p])[X] :=
  C ((j:ℤ_[p])*integralParameterInvPow z hz hv j)*
    (X-C (integralParameterTau z (Or.inr (by rw [hv]; norm_num)) j hj))

def integralVPole (z : ℚ) (hz : z ≠ 0) (hv : padicValRat p z = 0)
    (j : ℕ) (hj : j < p) : (ℤ_[p])[X] :=
  C (-integralParameterInvPow z hz hv j)*
    (X-C (integralParameterTau z (Or.inr (by rw [hv]; norm_num)) j hj))

theorem integralUPole_eval (z : ℚ) (hz : z ≠ 0) (hv : padicValRat p z = 0)
    (j : ℕ) (hj : j < p) (y : ℤ_[p]) :
    (((integralUPole z hz hv j hj).eval y : ℤ_[p]) : ℚ_[p]) =
      (j:ℚ_[p])*(z:ℚ_[p])⁻¹^j*((y:ℚ_[p])-(parameterTau z j:ℚ_[p])) := by
  unfold integralUPole
  rw [eval_mul, eval_C, eval_sub, eval_X, eval_C,
    PadicInt.coe_mul, PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_sub]
  simp [integralParameterInvPow, integralParameterTau, integralRational]

theorem integralVPole_eval (z : ℚ) (hz : z ≠ 0) (hv : padicValRat p z = 0)
    (j : ℕ) (hj : j < p) (y : ℤ_[p]) :
    (((integralVPole z hz hv j hj).eval y : ℤ_[p]) : ℚ_[p]) =
      -(z:ℚ_[p])⁻¹^j*((y:ℚ_[p])-(parameterTau z j:ℚ_[p])) := by
  unfold integralVPole
  rw [eval_mul, eval_C, eval_sub, eval_X, eval_C,
    PadicInt.coe_mul, PadicInt.coe_neg, PadicInt.coe_sub]
  simp [integralParameterInvPow, integralParameterTau, integralRational]

theorem integralUPole_zero (z : ℚ) (hz : z ≠ 0) (hv : padicValRat p z = 0)
    (h0 : 0 < p) : integralUPole z hz hv 0 h0 = 0 := by
  simp [integralUPole]

theorem integralVPole_zero (z : ℚ) (hz : z ≠ 0) (hv : padicValRat p z = 0)
    (h0 : 0 < p) : integralVPole z hz hv 0 h0 = -X := by
  have ht : integralParameterTau z (Or.inr (by rw [hv]; norm_num)) 0 h0 = 0 := by
    apply PadicInt.ext
    simp [integralParameterTau, integralRational, parameterTau]
  have hi : integralParameterInvPow z hz hv 0 = 1 := by
    apply PadicInt.ext
    simp [integralParameterInvPow, integralRational]
  simp [integralVPole, ht, hi]

def primeUPole (hp2 : p ≠ 2) (j : ℕ) (hj : j < p) : (ℤ_[p])[X] :=
  integralUPole (primeParameter p) (primeParameter_unit hp2).1 (primeParameter_unit hp2).2 j hj

def primeVPole (hp2 : p ≠ 2) (j : ℕ) (hj : j < p) : (ℤ_[p])[X] :=
  integralVPole (primeParameter p) (primeParameter_unit hp2).1 (primeParameter_unit hp2).2 j hj

end
end Li2

end
