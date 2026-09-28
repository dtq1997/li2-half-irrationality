module
public import Li2Unified.Modular.Base.RestrictedSeriesCompat
public import Li2Unified.Modular.Base.OriginalPulledRepresentation
public import Li2Unified.Modular.Base.FieldPoleCompatibility
public import Li2Unified.Modular.Base.FieldParameterFunctional
public import Li2Unified.Modular.Base.PrimePoleExtension
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

end
end Li2

end
