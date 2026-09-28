module
public import Li2Unified.Modular.Base.PrimeTopFixedConstant

set_option backward.privateInPublic true

@[expose] public section

/-! Replace the actual all-disc sum by the proved fixed rational leading value. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem primeTop_fixed_entry_leading (hp4 : 3 < p) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*
        (primeProduct p*primeProduct p).map (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p]) -
      C ((p:ℚ_[p])^4*(-7609/72:ℚ_[p]))).coeff n‖ ≤ ‖(p:ℚ_[p])‖^5 := by
  let F := C ((p:ℚ_[p])^3)*
    (numeratorFunctional (4*(p-1)) ((D (p-1))^3*
      (primeProduct p*primeProduct p).map (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p])
  have hc : ∀ k, ‖(C (primeTopLeadingSum (p := p)-(-7609/72:ℚ_[p]))).coeff k‖ ≤ ‖(p:ℚ_[p])‖^1 := by
    intro k
    by_cases hk : k=0
    · subst k
      simpa using! primeTopLeadingSum_norm (p := p) hp4
    · simp [coeff_C,hk]
  have hnew := fieldPolynomial_prime_power_bound
    (C (primeTopLeadingSum (p := p)-(-7609/72:ℚ_[p]))) 4 1 hc n
  have he : F-C ((p:ℚ_[p])^4*(-7609/72:ℚ_[p])) =
      (F-C ((p:ℚ_[p])^4*primeTopLeadingSum (p := p))) +
        C ((p:ℚ_[p])^4)*C (primeTopLeadingSum (p := p)-(-7609/72:ℚ_[p])) := by
    simp only [C_sub,C_mul]
    ring
  change ‖(F-C ((p:ℚ_[p])^4*(-7609/72:ℚ_[p]))).coeff n‖ ≤ _
  rw [he,coeff_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (primeTop_original_entry_leading hp4 n) hnew)

end
end Li2

end
