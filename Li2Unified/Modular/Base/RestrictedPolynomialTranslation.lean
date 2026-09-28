module
public import Li2Unified.Modular.Base.RestrictedPoleBounds

set_option backward.privateInPublic true

@[expose] public section

/-! Translation respects multiplication by any integral polynomial. Uniform
coefficient bounds let polynomial truncation pass through both operations. -/
open Filter Polynomial
open scoped Topology BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma restrictedMoment_coeff (f : PowerSeries ℤ_[p]) (n : ℕ) :
    restrictedMoment (fun k => if k = n then 1 else 0) f = PowerSeries.coeff n f := by
  simp [restrictedMoment]

lemma translated_coeff_trunc_tendsto (a : ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (n : ℕ) :
    Tendsto (fun N => PowerSeries.coeff n
      (restrictedTranslate a (PowerSeries.trunc N f : PowerSeries ℤ_[p])))
      atTop (𝓝 (PowerSeries.coeff n (restrictedTranslate a f))) := by
  simpa only [restrictedMoment_coeff] using
    translatedMoment_trunc_tendsto (fun k => if k = n then 1 else 0) a f hf

lemma translated_polynomial_mul_trunc_tendsto (a : ℤ_[p]) (P : (ℤ_[p])[X])
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f) (n : ℕ) :
    Tendsto (fun N => PowerSeries.coeff n
      (restrictedTranslate a ((P : PowerSeries ℤ_[p])*(PowerSeries.trunc N f : PowerSeries ℤ_[p]))))
      atTop (𝓝 (PowerSeries.coeff n (restrictedTranslate a ((P : PowerSeries ℤ_[p])*f)))) := by
  apply tendsto_of_trunc_error_bound
    (fun g => PowerSeries.coeff n (restrictedTranslate a ((P : PowerSeries ℤ_[p])*g))) f hf
  intro N B hB htail
  rw [← map_sub, ← restrictedTranslate_sub a _ _
    (PowerSeries.IsRestricted.mul 1 (polynomial_isRestricted P) hf)
    (PowerSeries.IsRestricted.mul 1 (polynomial_isRestricted P) (polynomial_isRestricted _)),
    ← mul_sub]
  apply restrictedTranslate_coeff_bound
  intro k
  exact restricted_mul_coeff_bound _ _ B hB (trunc_error_coeff_bound f N B hB htail) (n+k)

theorem restrictedTranslate_polynomial_mul (a : ℤ_[p]) (P : (ℤ_[p])[X])
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f) :
    restrictedTranslate a ((P : PowerSeries ℤ_[p])*f) =
      ((P.comp (X+C a) : (ℤ_[p])[X]) : PowerSeries ℤ_[p])*restrictedTranslate a f := by
  apply PowerSeries.ext
  intro n
  have hl := translated_polynomial_mul_trunc_tendsto a P f hf n
  have hr : Tendsto (fun N => PowerSeries.coeff n
      (((P.comp (X+C a) : (ℤ_[p])[X]) : PowerSeries ℤ_[p])*
        restrictedTranslate a (PowerSeries.trunc N f : PowerSeries ℤ_[p])))
      atTop (𝓝 (PowerSeries.coeff n
        (((P.comp (X+C a) : (ℤ_[p])[X]) : PowerSeries ℤ_[p])*restrictedTranslate a f))) := by
    simp only [PowerSeries.coeff_mul]
    apply tendsto_finset_sum
    intro ij _
    exact tendsto_const_nhds.mul (translated_coeff_trunc_tendsto a f hf ij.2)
  have he (N : ℕ) : restrictedTranslate a
      ((P : PowerSeries ℤ_[p])*(PowerSeries.trunc N f : PowerSeries ℤ_[p])) =
      ((P.comp (X+C a) : (ℤ_[p])[X]) : PowerSeries ℤ_[p])*
        restrictedTranslate a (PowerSeries.trunc N f : PowerSeries ℤ_[p]) := by
    rw [← Polynomial.coe_mul, restrictedTranslate_polynomial,
      restrictedTranslate_polynomial, mul_comp, Polynomial.coe_mul]
  exact tendsto_nhds_unique hl
    (hr.congr' (Filter.Eventually.of_forall fun N => congrArg (PowerSeries.coeff n) (he N).symm))

end
end Li2

end
