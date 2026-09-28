module
public import Li2Unified.Modular.Base.PadicReciprocalSeries
public import Li2Unified.Modular.Base.PrimeRestrictedShift
public import Li2Unified.Modular.Base.AffineInverseDifferential

set_option backward.privateInPublic true

@[expose] public section

/-! Finite-tail translation for the nonmatching reciprocal factors,
and the exact -a/p differential correction. -/
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem padicReciprocalSeries_eval_inv (d : ℚ) (hd : d ≠ 0)
    (hv : padicValRat p d = 0) (e : ℕ) (x : ℤ_[p]) :
    (restrictedEval x (padicReciprocalSeries d hd hv e) : ℚ_[p]) =
      (((d:ℚ_[p])+(p:ℚ_[p])*(x:ℚ_[p]))^e)⁻¹ :=
  eq_inv_of_mul_eq_one_left (padicReciprocalSeries_eval d hd hv e x)

theorem reciprocal_differential_correction (μ : ℕ → ℤ_[p])
    (d : ℚ) (hd : d ≠ 0) (hv : padicValRat p d = 0) (a : ℚ_[p]) :
    (restrictedU μ (padicReciprocalSeries d hd hv 1) : ℚ_[p])-
      (a/(p:ℚ_[p]))*(restrictedV μ (padicReciprocalSeries d hd hv 1) : ℚ_[p]) =
      ((d:ℚ_[p])+a)*(restrictedMoment μ (padicReciprocalSeries d hd hv 2) : ℚ_[p]) := by
  unfold padicReciprocalSeries
  rw [restrictedU_affine_inverse _ _ _ padicInt_prime_norm_lt_one,
    restrictedV_affine_inverse _ _ _ padicInt_prime_norm_lt_one]
  simp only [PadicInt.coe_mul, PadicInt.coe_neg, PadicInt.coe_natCast,
    integralRationalUnit_coe]
  have hpne : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  field_simp
  <;> ring

end
end Li2

end
