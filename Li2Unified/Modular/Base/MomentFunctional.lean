module
public import Li2Unified.Modular.Base.MomentSeries
public import Mathlib.Algebra.Polynomial.Derivative

set_option backward.privateInPublic true

@[expose] public section

/-! The literal polynomial moment functional is the convergent derivative sum. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def polynomialIntegrand (f : ℚ[X]) (x : ℝ) : ℝ :=
  f.sum fun k a => (a:ℝ) * ((k:ℝ)+1) * x^k

lemma polynomialIntegrand_derivative (f : ℚ[X]) (x : ℝ) :
    polynomialIntegrand f x = ((f.map (Rat.castHom ℝ))*X).derivative.eval x := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [polynomialIntegrand, Polynomial.sum_add_index]
    · change polynomialIntegrand f x + polynomialIntegrand g x = _
      rw [hf, hg]
      simp only [Polynomial.map_add, add_mul, derivative_add, eval_add]
    · intro k
      simp
    · intro k a b
      push_cast
      ring
  | monomial n a =>
    simp [polynomialIntegrand, Polynomial.sum_monomial_index,
      map_monomial, monomial_mul_X, derivative_monomial_succ, eval_monomial]

lemma polynomialIntegrand_term (f : ℚ[X]) (m : ℕ) :
    (-1/2:ℝ)^(m+1) * polynomialIntegrand f ((m:ℝ)+1) =
      ∑ k ∈ f.support, ((f.coeff k:ℝ)*((k:ℝ)+1)) *
        ((-1/2:ℝ)^(m+1) * ((m:ℝ)+1)^k) := by
  unfold polynomialIntegrand Polynomial.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem summable_polynomialIntegrand (f : ℚ[X]) :
    Summable (fun m : ℕ => (-1/2:ℝ)^(m+1) * polynomialIntegrand f ((m:ℝ)+1)) := by
  simp_rw [polynomialIntegrand_term]
  apply summable_sum
  intro k _
  exact (summable_realMoment k).mul_left _

theorem polynomialMoment_series (f : ℚ[X]) : (polynomialMoment f:ℝ) =
    ∑' m : ℕ, (-1/2:ℝ)^(m+1) * polynomialIntegrand f ((m:ℝ)+1) := by
  simp_rw [polynomialIntegrand_term]
  rw [Summable.tsum_finsetSum]
  · simp_rw [tsum_mul_left]
    unfold polynomialMoment Polynomial.sum
    push_cast
    simp_rw [moment_cast_eq_realMoment]
    rfl
  · intro k _
    exact (summable_realMoment k).mul_left _

theorem polynomialMoment_derivative_series (f : ℚ[X]) : (polynomialMoment f:ℝ) =
    ∑' m : ℕ, (-1/2:ℝ)^(m+1) *
      ((f.map (Rat.castHom ℝ))*X).derivative.eval ((m:ℝ)+1) := by
  simpa only [polynomialIntegrand_derivative] using polynomialMoment_series f

end
end Li2

end
