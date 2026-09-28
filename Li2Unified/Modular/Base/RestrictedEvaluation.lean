module
public import Li2Unified.Modular.Base.RestrictedShift
public import Li2Unified.Modular.Base.RestrictedRationalUnits

set_option backward.privateInPublic true

@[expose] public section

/-! Evaluation on the closed integral disc respects multiplication and translation.
This also identifies the constructed inverse series with the intended rational factors. -/
open Filter Polynomial
open scoped Topology BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem restrictedEval_summable (x : ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    Summable (fun n => PowerSeries.coeff n f*x^n) :=
  restrictedMoment_summable _ _ hf

lemma restrictedEval_one (x : ℤ_[p]) : restrictedEval x 1 = 1 := by
  simpa only [Polynomial.coe_one, eval_one] using restrictedEval_polynomial x (1 : (ℤ_[p])[X])

set_option backward.isDefEq.respectTransparency false in
theorem restrictedEval_mul (x : ℤ_[p]) (f g : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (hg : PowerSeries.IsRestricted 1 g) :
    restrictedEval x (f*g) = restrictedEval x f*restrictedEval x g := by
  have hs : Summable (fun n : ℕ => PowerSeries.coeff n f*x^n) := restrictedEval_summable x f hf
  have ht : Summable (fun n : ℕ => PowerSeries.coeff n g*x^n) := restrictedEval_summable x g hg
  have hfg : Summable (fun ij : ℕ × ℕ =>
      (PowerSeries.coeff ij.1 f*x^ij.1)*(PowerSeries.coeff ij.2 g*x^ij.2)) :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (tendsto_mul_cofinite_nhds_zero
        (f := fun n : ℕ => PowerSeries.coeff n f*x^n)
        (g := fun n : ℕ => PowerSeries.coeff n g*x^n)
        hs.tendsto_cofinite_zero ht.tendsto_cofinite_zero)
  have hm : ((∑' n : ℕ, PowerSeries.coeff n f*x^n) *
      ∑' n : ℕ, PowerSeries.coeff n g*x^n) =
      ∑' n : ℕ, ∑ ij ∈ Finset.antidiagonal n,
        (PowerSeries.coeff ij.1 f*x^ij.1)*(PowerSeries.coeff ij.2 g*x^ij.2) :=
    Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
      (α := ℤ_[p]) (A := ℕ)
      (f := fun n : ℕ => PowerSeries.coeff n f*x^n)
      (g := fun n : ℕ => PowerSeries.coeff n g*x^n) hs ht hfg
  unfold restrictedEval restrictedMoment
  refine Eq.trans ?_ hm.symm
  apply tsum_congr
  intro n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1+ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [← he]
  dsimp only
  rw [pow_add]
  exact mul_mul_mul_comm _ _ _ _

theorem restrictedTranslate_eval (a x : ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    restrictedEval x (restrictedTranslate a f) = restrictedEval (x+a) f := by
  have hl := translatedMoment_trunc_tendsto (fun n => x^n) a f hf
  have hr := restrictedMoment_trunc_tendsto (fun n => (x+a)^n) f hf
  have he (N : ℕ) : restrictedEval x
      (restrictedTranslate a (PowerSeries.trunc N f : PowerSeries ℤ_[p])) =
      restrictedEval (x+a) (PowerSeries.trunc N f : PowerSeries ℤ_[p]) := by
    rw [restrictedTranslate_polynomial, restrictedEval_polynomial, restrictedEval_polynomial,
      eval_comp, eval_add, eval_X, eval_C]
  exact tendsto_nhds_unique hl (hr.congr' (Filter.Eventually.of_forall fun N => (he N).symm))

theorem inverseOneSubSeries_eval (b : ℤ_[p]) (hb : ‖b‖ < 1) (x : ℤ_[p]) (d : ℕ) :
    restrictedEval x (inverseOneSubSeries b d)*(1-b*x)^d = 1 := by
  have hc : (((1-C b*X)^d : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) =
      (1-PowerSeries.C b*PowerSeries.X)^d := by simp
  have hpoly : PowerSeries.IsRestricted 1 ((1-PowerSeries.C b*PowerSeries.X)^d) := by
    rw [← hc]
    exact polynomial_isRestricted _
  have heval : restrictedEval x ((1-PowerSeries.C b*PowerSeries.X)^d) = (1-b*x)^d := by
    rw [← hc, restrictedEval_polynomial]
    simp
  have he := congrArg (restrictedEval x) (inverseOneSubSeries_identity b d)
  rw [restrictedEval_mul x _ _ (inverseOneSubSeries_isRestricted b hb d) hpoly,
    heval, restrictedEval_one] at he
  exact he

end
end Li2

end
