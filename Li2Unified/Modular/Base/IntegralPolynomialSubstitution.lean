module
public import Li2Unified.Modular.Base.PrimeDiscPoleBounds
public import Mathlib.Algebra.Polynomial.Div

set_option backward.privateInPublic true

@[expose] public section

/-! Coefficient errors survive integral polynomial substitution. A substitution
divisible by s changes the constant specialization by coefficients bounded by ‖s‖. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem integralPolynomial_comp_coeff_bound (F G : (ℤ_[p])[X])
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ n, ‖F.coeff n‖ ≤ B) (n : ℕ) :
    ‖(F.comp G).coeff n‖ ≤ B := by
  rw [comp_eq_sum_left, Polynomial.sum, finset_sum_coeff]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB
  intro k _
  rw [coeff_C_mul]
  exact (integral_coeff_mul_norm_le _ _).trans (hF k)

theorem integralPolynomial_scaled_substitution (F : (ℤ_[p])[X])
    (s eta : ℤ_[p]) (n : ℕ) :
    ‖(F.comp (C s*(X-C eta))-C (F.eval 0)).coeff n‖ ≤ ‖s‖ := by
  have h := congrArg (fun P : (ℤ_[p])[X] => P.comp (C s*(X-C eta)))
    (X_mul_divX_add F)
  simp only [add_comp, mul_comp, X_comp, C_comp, coeff_zero_eq_eval_zero] at h
  have he : F.comp (C s*(X-C eta))-C (F.eval 0) =
      C s*((X-C eta)*(F.divX.comp (C s*(X-C eta)))) := by
    rw [← h]
    ring
  rw [he, coeff_C_mul]
  exact integral_coeff_mul_norm_le _ _

theorem integralPolynomial_leading_substitution (F H : (ℤ_[p])[X])
    (s eta : ℤ_[p]) (B : ℝ) (hB : 0 ≤ B) (hs : ‖s‖ ≤ B)
    (hFH : ∀ n, ‖(F-H).coeff n‖ ≤ B) (n : ℕ) :
    ‖(F.comp (C s*(X-C eta))-C (H.eval 0)).coeff n‖ ≤ B := by
  have he : F.comp (C s*(X-C eta))-C (H.eval 0) =
      (F-H).comp (C s*(X-C eta)) +
        (H.comp (C s*(X-C eta))-C (H.eval 0)) := by
    rw [sub_comp]
    ring
  rw [he, coeff_add]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  exact max_le (integralPolynomial_comp_coeff_bound (F-H) _ B hB hFH n)
    ((integralPolynomial_scaled_substitution H s eta n).trans hs)

end
end Li2

end
