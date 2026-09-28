module
public import Li2Unified.Modular.Base.OriginalPartialFractions
public import Li2Unified.Modular.Base.FieldPoleSums

set_option backward.privateInPublic true

@[expose] public section

/-! Each actual pulled simple pole has its actual affine denominator. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def pulledAffineFactor (j a : ℕ) : PowerSeries ℚ_[p] :=
  PowerSeries.C (p:ℚ_[p])*PowerSeries.X+PowerSeries.C ((j:ℚ_[p])-(a:ℚ_[p]))

lemma pulledAffineFactor_eq (j a : ℕ) :
    rationalPolynomialSeries (p := p) ((X+C (j:ℚ)).comp (C (p:ℚ)*X-C (a:ℚ))) =
      pulledAffineFactor j a := by
  simp only [add_comp, X_comp, C_comp, map_add, map_sub, map_mul,
    rationalPolynomialSeries_C, rationalPolynomialSeries_X, Rat.cast_natCast]
  unfold pulledAffineFactor
  rw [map_sub]
  ring

lemma fieldPoleNumerator_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℤ_[p]) (i : ι) (b : ℚ_[p]) :
    fieldPoleNumerator c 0 (Pi.single i b) =
      PowerSeries.C b*(fieldPoleCofactor c i : PowerSeries ℚ_[p]) := by
  have he : (∑ j, C ((Pi.single i b : ι → ℚ_[p]) j)*fieldPoleCofactor c j : (ℚ_[p])[X]) =
      C b*fieldPoleCofactor c i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_apply, hji]
    · simp
  simp only [fieldPoleNumerator, mul_zero, zero_add, he, Polynomial.coe_mul, Polynomial.coe_C]

theorem pulledPoleRegular_inverse (j a : ℕ) (ha : a < p)
    (hm : ¬p ∣ j+(p-1-a)+1) :
    pulledAffineFactor (p := p) j a * pulledPoleRegular j a = 1 := by
  let d : ℚ := ((j+(p-1-a)+1:ℕ):ℚ)-(p:ℚ)
  have hd := rational_nonmultiple_sub_prime (p := p) (j+(p-1-a)+1) hm
  have he := congrArg (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]))
    (affineInverseSeries_identity (integralRationalUnit d hd.1 hd.2) (p:ℤ_[p]) 1)
  simp only [map_mul, map_pow, map_add, PowerSeries.map_C, PowerSeries.map_X,
    pow_one, map_one, PadicInt.algebraMap_apply, integralRationalUnit_coe,
    PadicInt.coe_natCast] at he
  have hdval : (d:ℚ_[p]) = (j:ℚ_[p])-(a:ℚ_[p]) := by
    have hdq : d = (j:ℚ)-(a:ℚ) :=
      eq_sub_of_add_eq (polePullback_denominator (p := p) j a ha)
    exact_mod_cast hdq
  rw [hdval] at he
  unfold pulledPoleRegular
  rw [dif_neg hm]
  change pulledAffineFactor j a * PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
    (affineInverseSeries (integralRationalUnit d hd.1 hd.2) (p:ℤ_[p]) 1) = 1
  simpa only [pulledAffineFactor, add_comm, mul_comm] using he

theorem pulledPole_cleared (j a : ℕ) (hj : j ≤ 4*p-4) (ha : a < p) :
    pulledAffineFactor (p := p) j a *
      fieldPoleNumerator (primePoleCenters p) (pulledPoleRegular j a)
        (pulledPoleResidue j a hj ha) =
      (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) := by
  classical
  by_cases hm : p ∣ j+(p-1-a)+1
  · rw [pulledPoleRegular, pulledPoleResidue, dif_pos hm, dif_pos hm,
      fieldPoleNumerator_single]
    let k := primeMatchingPoleIndex j a hj ha hm
    have hA : pulledAffineFactor (p := p) j a =
        PowerSeries.C (p:ℚ_[p]) *
          ((X-C (primePoleCenters p k : ℚ_[p]) : (ℚ_[p])[X]) : PowerSeries ℚ_[p]) := by
      rw [pulledAffineFactor, primeMatchingPole_denominator j a hj ha hm]
      simp only [primePoleCenters, PadicInt.coe_neg, PadicInt.coe_natCast,
        Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C, map_neg, map_mul,
        Polynomial.coe_neg, k]
      ring
    have hpne : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hc : PowerSeries.C (p:ℚ_[p])*PowerSeries.C (p:ℚ_[p])⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hpne, map_one]
    rw [hA, fieldPoleDenominator_factor _ k, Polynomial.coe_mul]
    change (PowerSeries.C (p:ℚ_[p])*_) * (PowerSeries.C (p:ℚ_[p])⁻¹ * _) = _
    calc
      _ = (PowerSeries.C (p:ℚ_[p])*PowerSeries.C (p:ℚ_[p])⁻¹) *
        (((X-C (primePoleCenters p k : ℚ_[p]) : (ℚ_[p])[X]) : PowerSeries ℚ_[p]) *
          (fieldPoleCofactor (primePoleCenters p) k : PowerSeries ℚ_[p])) := by ring
      _ = _ := by rw [hc, one_mul]
  · have hi := pulledPoleRegular_inverse (p := p) j a ha hm
    rw [pulledPoleResidue, dif_neg hm]
    simp only [fieldPoleNumerator, Pi.zero_apply, map_zero, zero_mul,
      Finset.sum_const_zero, Polynomial.coe_zero, add_zero]
    calc
      _ = (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
        (pulledAffineFactor j a * pulledPoleRegular j a) := by ring
      _ = _ := by rw [hi, mul_one]

end
end Li2

end
