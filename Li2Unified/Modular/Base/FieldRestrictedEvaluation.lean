module
public import Li2Unified.Modular.Base.FieldRestrictedFunctional
public import Li2Unified.Modular.Base.RestrictedEvaluation

set_option backward.privateInPublic true

@[expose] public section

/-! Evaluation of restricted Q_p series at integral points. Coefficients may have
arbitrary p-adic denominators; convergence uses only their decay to zero. -/
open Filter Polynomial
open scoped Topology BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def fieldRestrictedEval (x : ℤ_[p]) (f : PowerSeries ℚ_[p]) : ℚ_[p] :=
  fieldRestrictedMoment (fun n => x^n) f

theorem field_polynomial_isRestricted (P : (ℚ_[p])[X]) :
    PowerSeries.IsRestricted 1 (P : PowerSeries ℚ_[p]) := by
  rw [PowerSeries.isRestricted_iff']
  simp only [one_pow, mul_one]
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (P.natDegree+1)] with n hn
  rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]

theorem field_map_isRestricted (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    PowerSeries.IsRestricted 1 (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) f) := by
  simpa only [PowerSeries.isRestricted_iff', PowerSeries.coeff_map, PadicInt.norm_def] using! hf

lemma fieldRestrictedEval_polynomial (x : ℤ_[p]) (P : (ℚ_[p])[X]) :
    fieldRestrictedEval x (P : PowerSeries ℚ_[p]) = P.eval (x:ℚ_[p]) := by
  rw [fieldRestrictedEval, fieldRestrictedMoment_polynomial, eval_eq_sum]
  simp only [PadicInt.coe_pow]

lemma fieldRestrictedEval_summable (x : ℤ_[p]) (f : PowerSeries ℚ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    Summable (fun n => PowerSeries.coeff n f*(x:ℚ_[p])^n) := by
  simpa only [PadicInt.coe_pow] using fieldRestrictedMoment_summable (fun n => x^n) f hf

set_option backward.isDefEq.respectTransparency false in
theorem fieldRestrictedEval_mul (x : ℤ_[p]) (f g : PowerSeries ℚ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (hg : PowerSeries.IsRestricted 1 g) :
    fieldRestrictedEval x (f*g) = fieldRestrictedEval x f*fieldRestrictedEval x g := by
  have hs := fieldRestrictedEval_summable x f hf
  have ht := fieldRestrictedEval_summable x g hg
  have hfg : Summable (fun ij : ℕ × ℕ =>
      (PowerSeries.coeff ij.1 f*(x:ℚ_[p])^ij.1)*(PowerSeries.coeff ij.2 g*(x:ℚ_[p])^ij.2)) :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (tendsto_mul_cofinite_nhds_zero
        (f := fun n : ℕ => PowerSeries.coeff n f*(x:ℚ_[p])^n)
        (g := fun n : ℕ => PowerSeries.coeff n g*(x:ℚ_[p])^n)
        hs.tendsto_cofinite_zero ht.tendsto_cofinite_zero)
  have hm : ((∑' n : ℕ, PowerSeries.coeff n f*(x:ℚ_[p])^n) *
      ∑' n : ℕ, PowerSeries.coeff n g*(x:ℚ_[p])^n) =
      ∑' n : ℕ, ∑ ij ∈ Finset.antidiagonal n,
        (PowerSeries.coeff ij.1 f*(x:ℚ_[p])^ij.1)*(PowerSeries.coeff ij.2 g*(x:ℚ_[p])^ij.2) :=
    Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
      (α := ℚ_[p]) (A := ℕ)
      (f := fun n : ℕ => PowerSeries.coeff n f*(x:ℚ_[p])^n)
      (g := fun n : ℕ => PowerSeries.coeff n g*(x:ℚ_[p])^n) hs ht hfg
  unfold fieldRestrictedEval fieldRestrictedMoment
  simp only [PadicInt.coe_pow]
  refine Eq.trans ?_ hm.symm
  apply tsum_congr
  intro n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1+ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [← he]
  rw [pow_add]
  exact mul_mul_mul_comm _ _ _ _

end
end Li2

end
