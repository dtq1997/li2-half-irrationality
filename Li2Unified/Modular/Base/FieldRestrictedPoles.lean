module
public import Li2Unified.Modular.Base.FieldRestrictedEvaluation

set_option backward.privateInPublic true

@[expose] public section

/-! A finite simple-pole representation over restricted Q_p power series at integral centers.
The cleared numerator determines both the regular part and every residue. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fieldPoleDenominator (c : ι → ℤ_[p]) : (ℚ_[p])[X] :=
  ∏ i, (X-C (c i : ℚ_[p]))

def fieldPoleCofactor (c : ι → ℤ_[p]) (i : ι) : (ℚ_[p])[X] :=
  ∏ j ∈ univ.erase i, (X-C (c j : ℚ_[p]))

lemma fieldPoleDenominator_factor (c : ι → ℤ_[p]) (i : ι) :
    fieldPoleDenominator c = (X-C (c i : ℚ_[p]))*fieldPoleCofactor c i := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

lemma fieldPoleDenominator_ne_zero (c : ι → ℤ_[p]) :
    fieldPoleDenominator c ≠ 0 :=
  (Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _).ne_zero

lemma fieldPoleDenominator_eval (c : ι → ℤ_[p]) (i : ι) :
    (fieldPoleDenominator c).eval (c i : ℚ_[p]) = 0 := by
  rw [fieldPoleDenominator_factor c i]
  simp

lemma fieldPoleCofactor_eval_other (c : ι → ℤ_[p]) (i j : ι) (hij : i ≠ j) :
    (fieldPoleCofactor c j).eval (c i : ℚ_[p]) = 0 := by
  unfold fieldPoleCofactor
  rw [eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩) (by simp)

lemma fieldPoleCofactor_eval_self_ne_zero (c : ι → ℤ_[p])
    (hc : Function.Injective c) (i : ι) :
    (fieldPoleCofactor c i).eval (c i : ℚ_[p]) ≠ 0 := by
  unfold fieldPoleCofactor
  rw [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hj).1 (hc (PadicInt.ext he)).symm)

def fieldPoleNumerator (c : ι → ℤ_[p]) (f : PowerSeries ℚ_[p]) (r : ι → ℚ_[p]) :
    PowerSeries ℚ_[p] :=
  (fieldPoleDenominator c : PowerSeries ℚ_[p])*f +
    ((∑ i, C (r i)*fieldPoleCofactor c i : (ℚ_[p])[X]) : PowerSeries ℚ_[p])

theorem fieldPoleNumerator_eval (c : ι → ℤ_[p]) (f : PowerSeries ℚ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (r : ι → ℚ_[p]) (i : ι) :
    fieldRestrictedEval (c i) (fieldPoleNumerator c f r) =
      r i*(fieldPoleCofactor c i).eval (c i : ℚ_[p]) := by
  unfold fieldPoleNumerator fieldRestrictedEval
  rw [fieldRestrictedMoment_add _ _ _ (PowerSeries.isRestricted.mul 1 (field_polynomial_isRestricted _) hf)
    (field_polynomial_isRestricted _)]
  change fieldRestrictedEval (c i) ((fieldPoleDenominator c : PowerSeries ℚ_[p])*f) +
    fieldRestrictedEval (c i) ((∑ j, C (r j)*fieldPoleCofactor c j : (ℚ_[p])[X]) : PowerSeries ℚ_[p]) = _
  rw [fieldRestrictedEval_mul _ _ _ (field_polynomial_isRestricted _) hf,
    fieldRestrictedEval_polynomial, fieldPoleDenominator_eval, zero_mul, zero_add,
    fieldRestrictedEval_polynomial, eval_finset_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [fieldPoleCofactor_eval_other c i j hji.symm]
  · simp

theorem fieldPoleNumerator_injective (c : ι → ℤ_[p]) (hc : Function.Injective c)
    (f g : PowerSeries ℚ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (hg : PowerSeries.IsRestricted 1 g) (r s : ι → ℚ_[p])
    (he : fieldPoleNumerator c f r = fieldPoleNumerator c g s) :
    f = g ∧ r = s := by
  have hrs : r = s := by
    funext i
    have hv := congrArg (fieldRestrictedEval (c i)) he
    rw [fieldPoleNumerator_eval c f hf r i,
      fieldPoleNumerator_eval c g hg s i] at hv
    exact mul_right_cancel₀ (fieldPoleCofactor_eval_self_ne_zero c hc i) hv
  refine ⟨?_, hrs⟩
  rw [hrs] at he
  unfold fieldPoleNumerator at he
  have hD : (fieldPoleDenominator c : PowerSeries ℚ_[p]) ≠ 0 := by
    exact_mod_cast fieldPoleDenominator_ne_zero c
  exact mul_left_cancel₀ hD (add_right_cancel he)

end
end Li2

end
