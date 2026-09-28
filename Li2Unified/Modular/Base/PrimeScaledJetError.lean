module
public import Li2Unified.Modular.Base.PrimeProductJetError

set_option backward.privateInPublic true

@[expose] public section

/-! Keep the pU-aV scale explicit when transferring actual product-jet errors. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem integralPolynomial_UV_difference_bound
    (U V H K : (ℤ_[p])[X]) (a q : ℤ_[p]) (B : ℝ)
    (hU : ∀ n, ‖(U-C q*H).coeff n‖ ≤ B)
    (hV : ∀ n, ‖(V-C q*K).coeff n‖ ≤ B) (n : ℕ) :
    ‖((C (p:ℤ_[p])*U-C a*V)-C q*(C (p:ℤ_[p])*H-C a*K)).coeff n‖ ≤ B := by
  have he : (C (p:ℤ_[p])*U-C a*V)-C q*(C (p:ℤ_[p])*H-C a*K) =
      C (p:ℤ_[p])*(U-C q*H)-C a*(V-C q*K) := by ring
  rw [he,coeff_sub,coeff_C_mul,coeff_C_mul]
  have hsub (x y : ℤ_[p]) : ‖x-y‖ ≤ max ‖x‖ ‖y‖ := by
    simpa only [sub_eq_add_neg,norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)
  apply (hsub _ _).trans
  apply max_le
  · rw [mul_comm]
    exact (integral_coeff_mul_norm_le _ _).trans (hU n)
  · rw [mul_comm]
    exact (integral_coeff_mul_norm_le _ _).trans (hV n)

end
end Li2

end
