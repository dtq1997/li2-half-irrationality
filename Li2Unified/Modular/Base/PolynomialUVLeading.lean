module
public import Li2Unified.Modular.Base.PrimeLocalLeadingBounds

set_option backward.privateInPublic true

@[expose] public section

/-! Clearing the one factor p in U-a/p V preserves the leading V value. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem integralPolynomial_prime_UV_leading
    (U V : (ℤ_[p])[X]) (a : ℤ_[p]) (q : ℚ_[p])
    (hV : ∀ n, ‖(V.map (algebraMap ℤ_[p] ℚ_[p])-C q).coeff n‖ ≤ ‖(p:ℚ_[p])‖)
    (n : ℕ) :
    ‖(C (p:ℚ_[p])*U.map (algebraMap ℤ_[p] ℚ_[p]) -
      C (a:ℚ_[p])*V.map (algebraMap ℤ_[p] ℚ_[p]) -
      C (-(a:ℚ_[p])*q)).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  have he : C (p:ℚ_[p])*U.map (algebraMap ℤ_[p] ℚ_[p]) -
      C (a:ℚ_[p])*V.map (algebraMap ℤ_[p] ℚ_[p]) - C (-(a:ℚ_[p])*q) =
      C (p:ℚ_[p])*U.map (algebraMap ℤ_[p] ℚ_[p]) -
        C (a:ℚ_[p])*(V.map (algebraMap ℤ_[p] ℚ_[p])-C q) := by
    rw [C_mul, C_neg]
    ring
  rw [he, coeff_sub, coeff_C_mul, coeff_C_mul]
  have hsub (x y : ℚ_[p]) : ‖x-y‖ ≤ max ‖x‖ ‖y‖ := by
    simpa only [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)
  apply (hsub _ _).trans
  apply max_le
  · simpa only [coeff_map] using integral_coeff_mul_norm_le (p:ℤ_[p]) (U.coeff n)
  · rw [norm_mul]
    exact (mul_le_mul (PadicInt.norm_le_one a) (hV n) (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul _)

end
end Li2

end
