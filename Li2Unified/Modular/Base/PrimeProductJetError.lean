module
public import Li2Unified.Modular.Base.PrimeDiscJetTransfer

set_option backward.privateInPublic true

@[expose] public section

/-! The exact integer product jets give a one-higher-order error in the
actual local U/V polynomials, including every coefficient after substitution. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem integralDiscTestPolynomial_jet_error (T : ℤ[X]) (a : Fin p)
    (m k : ℕ) (c : ℤ)
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^m)*X^k*(C c+C (p:ℤ)*E)) (n : ℕ) :
    ‖(integralDiscTestPolynomial T a-C ((p:ℤ_[p])^m*(c:ℤ_[p]))*X^k).coeff n‖ ≤
      ‖(p:ℤ_[p])^(m+1)‖ := by
  obtain ⟨E,hE⟩ := hT
  rw [integralDiscTestPolynomial_eq_map,hE]
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom, Int.cast_pow, Int.cast_natCast]
  have he : C ((p:ℤ_[p])^m)*X^k*(C (c:ℤ_[p])+C (p:ℤ_[p])*E.map (Int.castRingHom ℤ_[p])) -
      C ((p:ℤ_[p])^m*(c:ℤ_[p]))*X^k =
      C ((p:ℤ_[p])^(m+1))*(X^k*E.map (Int.castRingHom ℤ_[p])) := by
    simp only [pow_succ,C_mul]
    ring
  rw [he,coeff_C_mul]
  exact integral_coeff_mul_norm_le _ _

end
end Li2

end
