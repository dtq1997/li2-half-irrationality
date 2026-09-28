module
public import Li2Unified.Modular.Base.ParameterDissection
public import Li2Unified.Modular.Base.NumeratorFunctional
public import Mathlib.Algebra.Polynomial.Derivative

set_option backward.privateInPublic true

@[expose] public section

/-! The original differential functional has the exact polynomial p-dissection,
including the a/p correction and its sign. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def parameterU (z : ℚ) (P : ℚ[X]) : ℚ := parameterG z (X*P).derivative

def parameterV (z : ℚ) (P : ℚ[X]) : ℚ := parameterG z P.derivative

lemma parameterG_sub (z : ℚ) (P Q : ℚ[X]) :
    parameterG z (P-Q) = parameterG z P-parameterG z Q := by
  rw [show P-Q = P+C (-1)*Q by simp [sub_eq_add_neg], parameterG_add, parameterG_C_mul]
  ring

lemma affine_differential_identity (q a : ℚ) (hq : q ≠ 0) (P : ℚ[X]) :
    (X*P).derivative.comp (C q*X-C a) =
      (X*(P.comp (C q*X-C a))).derivative -
        C (a/q)*(P.comp (C q*X-C a)).derivative := by
  simp only [derivative_mul, derivative_X, one_mul, add_comp, mul_comp, X_comp,
    derivative_comp, derivative_sub, derivative_C, zero_mul, add_zero, sub_zero]
  have hc : C (a/q)*C q = (C a : ℚ[X]) := by
    rw [← map_mul, div_mul_cancel₀ a hq]
  calc
    _ = P.comp (C q*X-C a) + X*(P.derivative.comp (C q*X-C a)*C q) -
        (C (a/q)*C q)*P.derivative.comp (C q*X-C a) := by rw [hc]; ring
    _ = _ := by ring

theorem parameterU_dissection (z : ℚ) (hz : ‖(z:ℝ)‖ < 1) (hzne : z ≠ 0)
    (q : ℕ) (hq : 0 < q) (P : ℚ[X]) :
    parameterU z P = ∑ a : Fin q, z⁻¹^a.val*
      (parameterU (z^q) (P.comp (C (q:ℚ)*X-C (a.val:ℚ))) -
        (a.val:ℚ)/(q:ℚ)*parameterV (z^q) (P.comp (C (q:ℚ)*X-C (a.val:ℚ)))) := by
  unfold parameterU parameterV
  rw [parameterG_dissection z hz hzne q hq]
  apply Finset.sum_congr rfl
  intro a _
  rw [affine_differential_identity _ _ (by exact_mod_cast (Nat.ne_of_gt hq)),
    parameterG_sub, parameterG_C_mul]

theorem parameterU_negHalf (P : ℚ[X]) : parameterU (-1/2) P = polynomialMoment P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [parameterU, mul_add, derivative_add, parameterG_add,
      polynomialMoment_add] at *
    rw [hP, hQ]
  | monomial n a =>
    simp [parameterU, X_mul_monomial, derivative_monomial_succ, parameterG_monomial,
      parameterMoment_negHalf, polynomialMoment, Polynomial.sum_monomial_index]

theorem original_polynomial_dissection (q : ℕ) (hq : 0 < q) (P : ℚ[X]) :
    polynomialMoment P = ∑ a : Fin q, (-2:ℚ)^a.val*
      (parameterU ((-1/2:ℚ)^q) (P.comp (C (q:ℚ)*X-C (a.val:ℚ))) -
        (a.val:ℚ)/(q:ℚ)*parameterV ((-1/2:ℚ)^q)
          (P.comp (C (q:ℚ)*X-C (a.val:ℚ)))) := by
  rw [← parameterU_negHalf]
  simpa only [show (-1/2:ℚ)⁻¹ = -2 by norm_num] using
    parameterU_dissection (-1/2) (by norm_num) (by norm_num) q hq P

end
end Li2

end
