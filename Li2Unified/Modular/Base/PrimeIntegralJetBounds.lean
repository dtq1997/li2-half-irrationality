module
public import Li2Unified.Modular.Base.PrimeProductJets
public import Li2Unified.Modular.Base.PrimeOriginalLocalBasis
public import Li2Unified.Modular.Base.IntegralPolynomialSubstitution

set_option backward.privateInPublic true

@[expose] public section

/-! Divisibility of the original integer basis products transfers to the
bounded integral U/V functionals on every disc, before and after substitution. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma integralDiscTestPolynomial_eq_map (T : ℤ[X]) (a : Fin p) :
    integralDiscTestPolynomial T a =
      (T.comp (primeDiscSubstitution p a)).map (Int.castRingHom ℤ_[p]) := by
  simp only [integralDiscTestPolynomial, primeDiscSubstitution, primeCenter,
    Polynomial.map_comp, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_neg,
    Polynomial.map_X, Int.coe_castRingHom, Int.cast_neg, Int.cast_natCast, C_neg]
  congr 1
  ring

theorem integralDiscTestPolynomial_factor_bound (T : ℤ[X]) (a : Fin p) (m : ℕ)
    (hT : ∃ A : ℤ[X], T.comp (primeDiscSubstitution p a) = C ((p:ℤ)^m)*A) (n : ℕ) :
    ‖(integralDiscTestPolynomial T a).coeff n‖ ≤ ‖(p:ℤ_[p])^m‖ := by
  obtain ⟨A,hA⟩ := hT
  rw [integralDiscTestPolynomial_eq_map, hA]
  simp only [Polynomial.map_mul, Polynomial.map_C, Int.coe_castRingHom,
    Int.cast_pow, Int.cast_natCast, coeff_C_mul]
  exact integral_coeff_mul_norm_le _ _

theorem primeOriginalBasisProduct_integral_bound (hp3 : 3 ≤ p)
    (i j : Fin (2*(p-1))) (a : Fin p) (n : ℕ) :
    ‖(integralDiscTestPolynomial (primeOriginalBasis p hp3 i * primeOriginalBasis p hp3 j) a).coeff n‖ ≤
      ‖(p:ℤ_[p])^(primeOriginalBasisLocalOrder p hp3 i a+primeOriginalBasisLocalOrder p hp3 j a)‖ := by
  obtain ⟨A,hA⟩ := primeOriginalBasisProduct_disc_factor p hp3 i j a
  apply integralDiscTestPolynomial_factor_bound
  exact ⟨X^(primeOriginalBasisLocalOrder p hp3 i a+primeOriginalBasisLocalOrder p hp3 j a)*A,
    by rw [hA,mul_assoc]⟩

theorem primeDiscTest_U_coeff_bound (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (B : ℝ) (hB : 0 ≤ B) (hT : ∀ k, ‖(integralDiscTestPolynomial T a).coeff k‖ ≤ B) (n : ℕ) :
    ‖(primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).coeff n‖ ≤ B := by
  apply primePoleU_coeff_bound hp4 _ _ B hB
  · apply integralPoleMulRegular_bound_left _ _ _ _ B hB
    simpa only [Polynomial.coeff_coe] using hT
  · apply integralPoleMulResidue_bound_left _ _ _ B
    simpa only [Polynomial.coeff_coe] using hT

theorem primeDiscTest_V_coeff_bound (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (B : ℝ) (hB : 0 ≤ B) (hT : ∀ k, ‖(integralDiscTestPolynomial T a).coeff k‖ ≤ B) (n : ℕ) :
    ‖(primePoleV hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).coeff n‖ ≤ B := by
  apply primePoleV_coeff_bound hp4 _ _ B hB
  · apply integralPoleMulRegular_bound_left _ _ _ _ B hB
    simpa only [Polynomial.coeff_coe] using hT
  · apply integralPoleMulResidue_bound_left _ _ _ B
    simpa only [Polynomial.coeff_coe] using hT

theorem primeOriginalBasis_U_substituted_bound (hp4 : 3 < p)
    (i j : Fin (2*(p-1))) (a : Fin p) (eta : ℤ_[p]) (n : ℕ) :
    let T := primeOriginalBasis p (by omega) i * primeOriginalBasis p (by omega) j
    ‖((primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta))).coeff n‖ ≤
      ‖(p:ℤ_[p])^(primeOriginalBasisLocalOrder p (by omega) i a+
        primeOriginalBasisLocalOrder p (by omega) j a)‖ := by
  dsimp only
  apply integralPolynomial_comp_coeff_bound _ _ _ (norm_nonneg _)
  exact primeDiscTest_U_coeff_bound hp4 _ a _ (norm_nonneg _)
    (primeOriginalBasisProduct_integral_bound (by omega) i j a)

theorem primeOriginalBasis_V_substituted_bound (hp4 : 3 < p)
    (i j : Fin (2*(p-1))) (a : Fin p) (eta : ℤ_[p]) (n : ℕ) :
    let T := primeOriginalBasis p (by omega) i * primeOriginalBasis p (by omega) j
    ‖((primePoleV hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta))).coeff n‖ ≤
      ‖(p:ℤ_[p])^(primeOriginalBasisLocalOrder p (by omega) i a+
        primeOriginalBasisLocalOrder p (by omega) j a)‖ := by
  dsimp only
  apply integralPolynomial_comp_coeff_bound _ _ _ (norm_nonneg _)
  exact primeDiscTest_V_coeff_bound hp4 _ a _ (norm_nonneg _)
    (primeOriginalBasisProduct_integral_bound (by omega) i j a)

end
end Li2

end
