module
public import Li2Unified.Modular.Base.PrimeGlobalDissection

set_option backward.privateInPublic true

@[expose] public section

/-! Both jets vanish to the full local multiplicity on each other disc. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem primeJet_same_other_product_factor (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) (b : Fin p) (hb : b ≠ a) :
    ∃ E : ℤ[X], (primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩).comp
      (primeDiscSubstitution p b) = C ((p:ℤ)^(2*primeMultiplicity p b))*E := by
  obtain ⟨A,hA⟩ := primeJetPoly_other_expansion p ⟨a,i⟩ b hb
  obtain ⟨B,hB⟩ := primeJetPoly_other_expansion p ⟨a,j⟩ b hb
  refine ⟨X^(2*primeMultiplicity p b)*(A*B),?_⟩
  rw [mul_comp,hA,hB]
  simp only [two_mul,pow_add,C_mul]
  ring

theorem primeDiscTest_U_substituted_factor_bound (hp4 : 3 < p) (T : ℤ[X])
    (a : Fin p) (m : ℕ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) = C ((p:ℤ)^m)*E) (n : ℕ) :
    ‖((primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta))).coeff n‖ ≤ ‖(p:ℤ_[p])^m‖ := by
  apply integralPolynomial_comp_coeff_bound _ _ _ (norm_nonneg _)
  exact primeDiscTest_U_coeff_bound hp4 T a _ (norm_nonneg _)
    (integralDiscTestPolynomial_factor_bound T a m hT)

theorem primeDiscTest_V_substituted_factor_bound (hp4 : 3 < p) (T : ℤ[X])
    (a : Fin p) (m : ℕ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) = C ((p:ℤ)^m)*E) (n : ℕ) :
    ‖((primePoleV hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta))).coeff n‖ ≤ ‖(p:ℤ_[p])^m‖ := by
  apply integralPolynomial_comp_coeff_bound _ _ _ (norm_nonneg _)
  exact primeDiscTest_V_coeff_bound hp4 T a _ (norm_nonneg _)
    (integralDiscTestPolynomial_factor_bound T a m hT)

theorem primeDiscTestScaled_factor_bound (hp4 : 3 < p) (T : ℤ[X])
    (a : Fin p) (m : ℕ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) = C ((p:ℤ)^m)*E) (n : ℕ) :
    ‖(primeDiscTestScaled hp4 a T eta).coeff n‖ ≤ ‖(p:ℤ_[p])^m‖ := by
  have h := integralPolynomial_UV_difference_bound
    ((primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta)))
    ((primePoleV hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta))) 0 0 (a.val:ℤ_[p]) 0 _
    (by simpa only [C_0,zero_mul,sub_zero] using
      primeDiscTest_U_substituted_factor_bound hp4 T a m eta hT)
    (by simpa only [C_0,zero_mul,sub_zero] using
      primeDiscTest_V_substituted_factor_bound hp4 T a m eta hT) n
  simpa only [primeDiscTestScaled,C_0,zero_mul,mul_zero,sub_zero] using h

end
end Li2

end
