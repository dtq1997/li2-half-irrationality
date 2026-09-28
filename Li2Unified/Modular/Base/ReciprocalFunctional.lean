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

theorem primeReciprocalG_shift (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (d : ℚ) (hd : d ≠ 0) (hv : padicValRat p d = 0) (e k : ℕ) :
    (padicParameterG (primeParameter p) (primeParameter_moment_integral hp2 hp3)
      (padicReciprocalSeries (d+(p:ℚ)*(k:ℚ))
        (rational_unit_add_prime_mul d hd hv k).1
        (rational_unit_add_prime_mul d hd hv k).2 e) : ℚ_[p]) =
      ((padicParameterG (primeParameter p) (primeParameter_moment_integral hp2 hp3)
        (padicReciprocalSeries d hd hv e) : ℚ_[p])-
        ∑ j ∈ Finset.range k, (primeParameter p:ℚ_[p])^(j+1)*
          (((d:ℚ_[p])+(p:ℚ_[p])*((j:ℚ_[p])+1))^e)⁻¹)/
        (primeParameter p:ℚ_[p])^k := by
  rw [← padicReciprocalSeries_shift d hd hv e k,
    primeRestrictedShift hp2 hp3 _ (padicReciprocalSeries_isRestricted d hd hv e) k]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [padicReciprocalSeries_eval_inv]
  simp only [PadicInt.coe_add, PadicInt.coe_natCast, PadicInt.coe_one]

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
