module
public import Li2Unified.Modular.Base.ParameterSeries
public import Li2Unified.Modular.Base.ParameterShift

set_option backward.privateInPublic true

@[expose] public section

/-! The convergent real series for the entire rational-parameter polynomial
functional. This permits a residue-class dissection without p-adic geometric sums. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

lemma parameterPolynomialTerm (z : ℚ) (P : ℚ[X]) (m : ℕ) :
    ((z^(m+1)*P.eval ((m:ℚ)+1) : ℚ) : ℝ) =
      ∑ k ∈ P.support, (P.coeff k:ℝ)*((z:ℝ)^(m+1)*((m:ℝ)+1)^k) := by
  rw [Polynomial.eval_eq_sum]
  unfold Polynomial.sum
  rw [Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun k _ => by ring

theorem summable_parameterPolynomial (z : ℚ) (hz : ‖(z:ℝ)‖ < 1) (P : ℚ[X]) :
    Summable (fun m : ℕ => ((z^(m+1)*P.eval ((m:ℚ)+1) : ℚ) : ℝ)) := by
  simp_rw [parameterPolynomialTerm]
  apply summable_sum
  intro k _
  exact (summable_parameterRealMoment z hz k).mul_left _

theorem parameterG_cast_eq_series (z : ℚ) (hz : ‖(z:ℝ)‖ < 1) (P : ℚ[X]) :
    (parameterG z P:ℝ) =
      ∑' m : ℕ, ((z^(m+1)*P.eval ((m:ℚ)+1) : ℚ) : ℝ) := by
  simp_rw [parameterPolynomialTerm]
  rw [Summable.tsum_finsetSum]
  · simp_rw [tsum_mul_left]
    unfold parameterG Polynomial.sum
    push_cast
    simp_rw [parameterMoment_cast_eq_series z hz]
    rfl
  · intro k _
    exact (summable_parameterRealMoment z hz k).mul_left _

end
end Li2

end
