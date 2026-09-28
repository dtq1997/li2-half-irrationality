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

theorem primeJet_same_U_error (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) (n : ℕ) :
    let T := primeJetPoly p ⟨a,i⟩ * primeJetPoly p ⟨a,j⟩
    let q := (p:ℤ_[p])^(i.val+j.val)*((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p])
    ‖(primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T) -
      C q*primePoleU hp4 (primeDiscMonomialRegular hp4 a (i.val+j.val))
        (primeDiscMonomialResidue hp4 a (i.val+j.val))).coeff n‖ ≤ ‖(p:ℤ_[p])^(i.val+j.val+1)‖ := by
  dsimp only
  apply primeDiscTest_U_jet_error hp4 _ a _ _ _ (norm_nonneg _)
  exact integralDiscTestPolynomial_jet_error _ a _ _ _ (primeJet_same_product_expansion p a i j)

theorem primeJet_same_V_error (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) (n : ℕ) :
    let T := primeJetPoly p ⟨a,i⟩ * primeJetPoly p ⟨a,j⟩
    let q := (p:ℤ_[p])^(i.val+j.val)*((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p])
    ‖(primePoleV hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T) -
      C q*primePoleV hp4 (primeDiscMonomialRegular hp4 a (i.val+j.val))
        (primeDiscMonomialResidue hp4 a (i.val+j.val))).coeff n‖ ≤ ‖(p:ℤ_[p])^(i.val+j.val+1)‖ := by
  dsimp only
  apply primeDiscTest_V_jet_error hp4 _ a _ _ _ (norm_nonneg _)
  exact integralDiscTestPolynomial_jet_error _ a _ _ _ (primeJet_same_product_expansion p a i j)

theorem primeJet_same_U_substituted_error (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) (eta : ℤ_[p]) (n : ℕ) :
    let T := primeJetPoly p ⟨a,i⟩ * primeJetPoly p ⟨a,j⟩
    let q := (p:ℤ_[p])^(i.val+j.val)*((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p])
    let S := C ((p:ℤ_[p])^2)*(X-C eta)
    ‖((primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp S -
      C q*(primePoleU hp4 (primeDiscMonomialRegular hp4 a (i.val+j.val))
        (primeDiscMonomialResidue hp4 a (i.val+j.val))).comp S).coeff n‖ ≤
      ‖(p:ℤ_[p])^(i.val+j.val+1)‖ := by
  dsimp only
  have h := integralPolynomial_comp_coeff_bound _ (C ((p:ℤ_[p])^2)*(X-C eta)) _
    (norm_nonneg _) (primeJet_same_U_error hp4 a i j) n
  simpa only [sub_comp,mul_comp,C_comp] using h

theorem primeJet_same_V_substituted_error (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) (eta : ℤ_[p]) (n : ℕ) :
    let T := primeJetPoly p ⟨a,i⟩ * primeJetPoly p ⟨a,j⟩
    let q := (p:ℤ_[p])^(i.val+j.val)*((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p])
    let S := C ((p:ℤ_[p])^2)*(X-C eta)
    ‖((primePoleV hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp S -
      C q*(primePoleV hp4 (primeDiscMonomialRegular hp4 a (i.val+j.val))
        (primeDiscMonomialResidue hp4 a (i.val+j.val))).comp S).coeff n‖ ≤
      ‖(p:ℤ_[p])^(i.val+j.val+1)‖ := by
  dsimp only
  have h := integralPolynomial_comp_coeff_bound _ (C ((p:ℤ_[p])^2)*(X-C eta)) _
    (norm_nonneg _) (primeJet_same_V_error hp4 a i j) n
  simpa only [sub_comp,mul_comp,C_comp] using h

end
end Li2

end
