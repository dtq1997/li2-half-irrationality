module
public import Li2Unified.Modular.Base.RestrictedEvaluation
public import Li2Unified.Modular.Base.RestrictedDividedDifference

set_option backward.privateInPublic true

@[expose] public section

/-! A finite simple-pole representation over restricted integral power series.
The cleared numerator determines both the regular part and every residue. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def integralPoleDenominator (c : ι → ℤ_[p]) : (ℤ_[p])[X] :=
  ∏ i, (X-C (c i))

def integralPoleCofactor (c : ι → ℤ_[p]) (i : ι) : (ℤ_[p])[X] :=
  ∏ j ∈ univ.erase i, (X-C (c j))

lemma integralPoleDenominator_factor (c : ι → ℤ_[p]) (i : ι) :
    integralPoleDenominator c = (X-C (c i))*integralPoleCofactor c i := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

lemma integralPoleDenominator_ne_zero (c : ι → ℤ_[p]) :
    integralPoleDenominator c ≠ 0 :=
  (Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _).ne_zero

lemma integralPoleDenominator_eval (c : ι → ℤ_[p]) (i : ι) :
    (integralPoleDenominator c).eval (c i) = 0 := by
  rw [integralPoleDenominator_factor c i]
  simp

lemma integralPoleCofactor_eval_other (c : ι → ℤ_[p]) (i j : ι) (hij : i ≠ j) :
    (integralPoleCofactor c j).eval (c i) = 0 := by
  unfold integralPoleCofactor
  rw [eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩) (by simp)

lemma integralPoleCofactor_eval_self_ne_zero (c : ι → ℤ_[p])
    (hc : Function.Injective c) (i : ι) :
    (integralPoleCofactor c i).eval (c i) ≠ 0 := by
  unfold integralPoleCofactor
  rw [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hj).1 (hc he).symm)

def integralPoleNumerator (c : ι → ℤ_[p]) (f : PowerSeries ℤ_[p]) (r : ι → ℤ_[p]) :
    PowerSeries ℤ_[p] :=
  (integralPoleDenominator c : PowerSeries ℤ_[p])*f +
    ((∑ i, C (r i)*integralPoleCofactor c i : (ℤ_[p])[X]) : PowerSeries ℤ_[p])

theorem integralPoleNumerator_isRestricted (c : ι → ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (r : ι → ℤ_[p]) :
    PowerSeries.IsRestricted 1 (integralPoleNumerator c f r) :=
  PowerSeries.IsRestricted.add 1
    (PowerSeries.IsRestricted.mul 1 (polynomial_isRestricted _) hf) (polynomial_isRestricted _)

theorem integralPoleNumerator_eval (c : ι → ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (r : ι → ℤ_[p]) (i : ι) :
    restrictedEval (c i) (integralPoleNumerator c f r) =
      r i*(integralPoleCofactor c i).eval (c i) := by
  unfold integralPoleNumerator restrictedEval
  rw [restrictedMoment_add _ _ _ (PowerSeries.IsRestricted.mul 1 (polynomial_isRestricted _) hf)
    (polynomial_isRestricted _)]
  change restrictedEval (c i) ((integralPoleDenominator c : PowerSeries ℤ_[p])*f) +
    restrictedEval (c i) ((∑ j, C (r j)*integralPoleCofactor c j : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) = _
  rw [restrictedEval_mul _ _ _ (polynomial_isRestricted _) hf,
    restrictedEval_polynomial, integralPoleDenominator_eval, zero_mul, zero_add,
    restrictedEval_polynomial, eval_finset_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [integralPoleCofactor_eval_other c i j hji.symm]
  · simp

theorem integralPoleNumerator_injective (c : ι → ℤ_[p]) (hc : Function.Injective c)
    (f g : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (hg : PowerSeries.IsRestricted 1 g) (r s : ι → ℤ_[p])
    (he : integralPoleNumerator c f r = integralPoleNumerator c g s) :
    f = g ∧ r = s := by
  have hrs : r = s := by
    funext i
    have hv := congrArg (restrictedEval (c i)) he
    rw [integralPoleNumerator_eval c f hf r i,
      integralPoleNumerator_eval c g hg s i] at hv
    exact mul_right_cancel₀ (integralPoleCofactor_eval_self_ne_zero c hc i) hv
  refine ⟨?_, hrs⟩
  rw [hrs] at he
  unfold integralPoleNumerator at he
  have hD : (integralPoleDenominator c : PowerSeries ℤ_[p]) ≠ 0 := by
    exact_mod_cast integralPoleDenominator_ne_zero c
  exact mul_left_cancel₀ hD (add_right_cancel he)

end
end Li2

end
