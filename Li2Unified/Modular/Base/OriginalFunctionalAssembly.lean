module
public import Li2Unified.Modular.Base.RestrictedSeriesCompat
public import Li2Unified.Modular.Base.OriginalPulledFunctional
public import Li2Unified.Modular.Base.FieldPoleSums

set_option backward.privateInPublic true

@[expose] public section

/-! Assemble the actual quotient and every actual residue into the field-valued
four-pole functional, retaining the literal -a/p differential correction. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma originalPulledRegular_subtype (m : ℕ) (F : ℚ[X]) (a : Fin p) :
    originalPulledRegular m F a =
      rationalPolynomialSeries ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ))) +
      ∑ j : ↥(Finset.Icc 1 m), (originalResidue m F j.val : ℚ_[p]) •
        pulledPoleRegular j.val a.val := by
  unfold originalPulledRegular
  congr 1
  simp only [PowerSeries.smul_eq_C_mul]
  change (∑ j ∈ Finset.Icc 1 m, PowerSeries.C (originalResidue m F j : ℚ_[p]) *
    pulledPoleRegular j a.val) = ∑ j : ↥(Finset.Icc 1 m),
      PowerSeries.C (originalResidue m F j.val : ℚ_[p]) * pulledPoleRegular j.val a.val
  exact (Finset.sum_coe_sort _ _).symm

theorem original_fieldPoleFunctional (μ : ℕ → ℤ_[p]) (w : Fin 4 → (ℚ_[p])[X])
    (m : ℕ) (hm : m ≤ 4*p-4) (F : ℚ[X]) (a : Fin p) :
    fieldPoleFunctional μ w (originalPulledRegular m F a) (originalPulledResidue m hm F a) =
      fieldPoleFunctional μ w
        (rationalPolynomialSeries ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ)))) 0 +
      ∑ j : ↥(Finset.Icc 1 m), C (originalResidue m F j.val : ℚ_[p]) *
        fieldPoleFunctional μ w (pulledPoleRegular j.val a.val)
          (pulledPoleResidue j.val a.val ((Finset.mem_Icc.mp j.property).2.trans hm) a.isLt) := by
  classical
  rw [originalPulledRegular_subtype]
  let f : ↥(Finset.Icc 1 m) → PowerSeries ℚ_[p] := fun j =>
    (originalResidue m F j.val : ℚ_[p]) • pulledPoleRegular j.val a.val
  have hf : ∀ j, PowerSeries.IsRestricted 1 (f j) := by
    intro j
    exact Li2.restrictedSeries_smul 1 (pulledPoleRegular_isRestricted (p := p) j.val a.val)
      (originalResidue m F j.val : ℚ_[p])
  have hq : PowerSeries.IsRestricted 1
      (rationalPolynomialSeries (p := p) ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ)))) :=
    field_polynomial_isRestricted (((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ))).map
      (Rat.castHom ℚ_[p]))
  have hr : originalPulledResidue m hm F a = 0 + originalPulledResidue m hm F a := by simp
  rw [hr, fieldPoleFunctional_add μ w _ _ hq
    (field_sum_isRestricted Finset.univ f (fun j _ => hf j))]
  congr 1
  unfold originalPulledResidue
  rw [fieldPoleFunctional_sum μ w Finset.univ f
    (fun j _ => hf j)]
  apply Finset.sum_congr rfl
  intro j _
  exact fieldPoleFunctional_smul μ w _ (pulledPoleRegular_isRestricted _ _) _ _

theorem numeratorPulledValue_field (hp4 : 3 < p) (Y : ℚ_[p])
    (m : ℕ) (hm : m ≤ 4*p-4) (F : ℚ[X]) (a : Fin p) :
    numeratorPulledValue (by omega : p ≠ 2) (by omega : p ≠ 3) Y m F a =
      (fieldPrimePoleU hp4 (originalPulledRegular m F a)
        (originalPulledResidue m hm F a)).eval Y - (a.val:ℚ_[p])/(p:ℚ_[p]) *
      (fieldPrimePoleV hp4 (originalPulledRegular m F a)
        (originalPulledResidue m hm F a)).eval Y := by
  have hu := original_fieldPoleFunctional
    (fun n : ℕ => ((n+1:ℕ):ℤ_[p])*integralParameterMoment (primeParameter p)
      (primeParameter_moment_integral (by omega) (by omega)) n)
    (fun j : Fin 4 => (primeUPole (by omega) j.val (by omega)).map (algebraMap ℤ_[p] ℚ_[p]))
    m hm F a
  have hv := original_fieldPoleFunctional
    (derivativeMoments (integralParameterMoment (primeParameter p)
      (primeParameter_moment_integral (by omega) (by omega))))
    (fun j : Fin 4 => (primeVPole (by omega) j.val (by omega)).map (algebraMap ℤ_[p] ℚ_[p]))
    m hm F a
  change _ = (fieldPoleFunctional _ _ _ _).eval Y - _*(fieldPoleFunctional _ _ _ _).eval Y
  rw [hu, hv]
  simp only [eval_add, eval_finset_sum, eval_mul, eval_C]
  rw [mul_add, add_sub_add_comm]
  unfold numeratorPulledValue
  rw [← original_pulled_polynomial_UV hp4 m F a Y]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro j _
  rw [original_pulled_simplePole_UV hp4 Y j.val a.val
    ((Finset.mem_Icc.mp j.property).2.trans hm) a.isLt]
  simp only [originalResidue, Rat.cast_div, fieldPrimePoleU, fieldPrimePoleV]
  ring

end
end Li2

end
