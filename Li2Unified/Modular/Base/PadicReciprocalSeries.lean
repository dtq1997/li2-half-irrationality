module
public import Li2Unified.Modular.Base.RestrictedAffineInverse
public import Li2Unified.Modular.Base.ParameterPoleValues

set_option backward.privateInPublic true

@[expose] public section

/-! Literal inverse powers of p*u+d for rational p-units d. Translation is
identified by a common cleared denominator, using the actual constructed units. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def integralRationalUnit (d : ℚ) (hd : d ≠ 0) (hv : padicValRat p d = 0) : ℤ_[p]ˣ :=
  Units.mkOfMulEqOne
    (integralRational d (Or.inr (by rw [hv]; norm_num)))
    (integralRational d⁻¹ (rational_unit_inverse_VG d hd hv))
    (by
      apply PadicInt.ext
      rw [PadicInt.coe_mul, PadicInt.coe_one]
      simp [integralRational, hd])

@[simp] lemma integralRationalUnit_coe (d : ℚ) (hd : d ≠ 0) (hv : padicValRat p d = 0) :
    (((integralRationalUnit d hd hv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = (d:ℚ_[p]) := rfl

lemma padicInt_prime_norm_lt_one : ‖(p:ℤ_[p])‖ < 1 :=
  PadicInt.norm_natCast_lt_one_iff.mpr (dvd_refl p)

def padicReciprocalSeries (d : ℚ) (hd : d ≠ 0) (hv : padicValRat p d = 0) (e : ℕ) :
    PowerSeries ℤ_[p] := affineInverseSeries (integralRationalUnit d hd hv) (p:ℤ_[p]) e

theorem padicReciprocalSeries_isRestricted (d : ℚ) (hd : d ≠ 0)
    (hv : padicValRat p d = 0) (e : ℕ) :
    PowerSeries.IsRestricted 1 (padicReciprocalSeries d hd hv e) :=
  affineInverseSeries_isRestricted _ _ padicInt_prime_norm_lt_one e

theorem padicReciprocalSeries_eval (d : ℚ) (hd : d ≠ 0)
    (hv : padicValRat p d = 0) (e : ℕ) (x : ℤ_[p]) :
    (restrictedEval x (padicReciprocalSeries d hd hv e) : ℚ_[p])*
      ((d:ℚ_[p])+(p:ℚ_[p])*(x:ℚ_[p]))^e = 1 := by
  have h := congrArg (fun t : ℤ_[p] => (t:ℚ_[p]))
    (affineInverseSeries_eval (integralRationalUnit d hd hv) (p:ℤ_[p])
      padicInt_prime_norm_lt_one e x)
  simpa only [padicReciprocalSeries, PadicInt.coe_mul, PadicInt.coe_pow,
    PadicInt.coe_add, PadicInt.coe_natCast, PadicInt.coe_one, integralRationalUnit_coe] using h

lemma rational_unit_add_prime_mul (d : ℚ) (hd : d ≠ 0)
    (hv : padicValRat p d = 0) (k : ℕ) :
    d+(p:ℚ)*(k:ℚ) ≠ 0 ∧ padicValRat p (d+(p:ℚ)*(k:ℚ)) = 0 := by
  apply unit_of_VG_sub hd hv
  have h : VG p ((p:ℚ)*(k:ℚ)) 1 := by
    simpa using (VG.primePow (p := p) (1:ℤ)).mul (VG.natCast (p := p) k)
  convert h using 1 <;> ring

theorem padicReciprocalSeries_shift (d : ℚ) (hd : d ≠ 0)
    (hv : padicValRat p d = 0) (e k : ℕ) :
    restrictedTranslate (k:ℤ_[p]) (padicReciprocalSeries d hd hv e) =
      padicReciprocalSeries (d+(p:ℚ)*(k:ℚ))
        (rational_unit_add_prime_mul d hd hv k).1 (rational_unit_add_prime_mul d hd hv k).2 e := by
  let a := integralRationalUnit d hd hv
  let a' := integralRationalUnit (d+(p:ℚ)*(k:ℚ))
    (rational_unit_add_prime_mul d hd hv k).1 (rational_unit_add_prime_mul d hd hv k).2
  have ha : (a':ℤ_[p]) = (a:ℤ_[p])+(p:ℤ_[p])*(k:ℤ_[p]) := by
    apply PadicInt.ext
    simp [a, a', Rat.cast_add, Rat.cast_mul]
  have ht := affineInverseSeries_translate_identity a (p:ℤ_[p]) padicInt_prime_norm_lt_one e (k:ℤ_[p])
  rw [← ha] at ht
  have hi := affineInverseSeries_identity a' (p:ℤ_[p]) e
  change restrictedTranslate (k:ℤ_[p]) (affineInverseSeries a (p:ℤ_[p]) e) =
    affineInverseSeries a' (p:ℤ_[p]) e
  calc
    _ = restrictedTranslate (k:ℤ_[p]) (affineInverseSeries a (p:ℤ_[p]) e)*
        (affineInverseSeries a' (p:ℤ_[p]) e*
          (PowerSeries.C (a':ℤ_[p])+PowerSeries.C (p:ℤ_[p])*PowerSeries.X)^e) := by rw [hi, mul_one]
    _ = affineInverseSeries a' (p:ℤ_[p]) e*
        ((PowerSeries.C (a':ℤ_[p])+PowerSeries.C (p:ℤ_[p])*PowerSeries.X)^e*
          restrictedTranslate (k:ℤ_[p]) (affineInverseSeries a (p:ℤ_[p]) e)) := by ring
    _ = _ := by rw [ht, mul_one]

end
end Li2

end
