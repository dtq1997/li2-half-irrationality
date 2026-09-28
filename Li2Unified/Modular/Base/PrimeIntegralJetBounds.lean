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

end
end Li2

end
