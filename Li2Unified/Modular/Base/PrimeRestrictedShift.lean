module
public import Li2Unified.Modular.Base.RestrictedShift
public import Li2Unified.Modular.Base.PadicParameterFunctional
public import Li2Unified.Modular.Base.PrimeParameter

set_option backward.privateInPublic true

@[expose] public section

/-! The restricted-series shift identity for the actual parameter (-1/2)^p. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma integralParameterMoment_recurrence (z : ℚ) (hz0 : VG p z 0)
    (hz : VG p (z/(1-z)) 0) (hz1 : z ≠ 1) (k : ℕ) :
    integralParameterMoment z hz k = integralRational z hz0+integralRational z hz0*
      ∑ j ∈ Finset.range (k+1), (Nat.choose k j : ℤ_[p])*integralParameterMoment z hz j := by
  apply PadicInt.ext
  simp only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_sum, PadicInt.coe_natCast]
  change (parameterMoment z k : ℚ_[p]) = (z : ℚ_[p]) + (z : ℚ_[p]) *
    ∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℚ_[p]) * (parameterMoment z j : ℚ_[p])
  exact_mod_cast parameterMoment_full_recurrence z hz1 k

theorem padicParameterG_shift_scaled (z : ℚ) (hz0 : VG p z 0)
    (hz : VG p (z/(1-z)) 0) (hz1 : z ≠ 1)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f) (k : ℕ) :
    (integralRational z hz0)^k*padicParameterG z hz (restrictedTranslate (k:ℤ_[p]) f) =
      padicParameterG z hz f-
      ∑ j ∈ Finset.range k, (integralRational z hz0)^(j+1)*restrictedEval ((j:ℤ_[p])+1) f :=
  restrictedMoment_shift_scaled (integralParameterMoment z hz) (integralRational z hz0)
    (integralParameterMoment_recurrence z hz0 hz hz1) f hf k

theorem padicParameterG_shift (z : ℚ) (hz0 : VG p z 0)
    (hz : VG p (z/(1-z)) 0) (hz1 : z ≠ 1) (hzne : z ≠ 0)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f) (k : ℕ) :
    (padicParameterG z hz (restrictedTranslate (k:ℤ_[p]) f) : ℚ_[p]) =
      ((padicParameterG z hz f : ℚ_[p])-
        ∑ j ∈ Finset.range k, (z:ℚ_[p])^(j+1)*(restrictedEval ((j:ℤ_[p])+1) f : ℚ_[p]))/
        (z:ℚ_[p])^k := by
  have hzne' : (z:ℚ_[p]) ≠ 0 := by exact_mod_cast hzne
  apply (eq_div_iff (pow_ne_zero k hzne')).mpr
  have h := congrArg (fun a : ℤ_[p] => (a:ℚ_[p])) (padicParameterG_shift_scaled z hz0 hz hz1 f hf k)
  dsimp only [integralRational] at h
  simpa only [PadicInt.coe_mul, PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_sum,
    integralRational, mul_comm] using! h

end
end Li2

end
