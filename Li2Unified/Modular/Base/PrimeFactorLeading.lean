module
public import Li2Unified.Modular.Base.PrimeActualLowLeading

set_option backward.privateInPublic true

@[expose] public section

/-! Product-jet leading transfer with an explicit integer factor certificate.
This includes the appended top-degree basis vector, whose order is the full multiplicity. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem primeDiscTest_U_substituted_jet_error (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (m k : ℕ) (c : ℤ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^m)*X^k*(C c+C (p:ℤ)*E)) (n : ℕ) :
    ‖((primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta)) - C ((p:ℤ_[p])^m*(c:ℤ_[p]))*
      (primePoleU hp4 (primeDiscMonomialRegular hp4 a k) (primeDiscMonomialResidue hp4 a k)).comp
        (C ((p:ℤ_[p])^2)*(X-C eta))).coeff n‖ ≤ ‖(p:ℤ_[p])^(m+1)‖ := by
  have h := integralPolynomial_comp_coeff_bound _ (C ((p:ℤ_[p])^2)*(X-C eta)) _ (norm_nonneg _)
    (primeDiscTest_U_jet_error hp4 T a _ k _ (norm_nonneg _)
      (integralDiscTestPolynomial_jet_error T a m k c hT)) n
  simpa only [sub_comp,mul_comp,C_comp] using h

theorem primeDiscTest_V_substituted_jet_error (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (m k : ℕ) (c : ℤ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^m)*X^k*(C c+C (p:ℤ)*E)) (n : ℕ) :
    ‖((primePoleV hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta)) - C ((p:ℤ_[p])^m*(c:ℤ_[p]))*
      (primePoleV hp4 (primeDiscMonomialRegular hp4 a k) (primeDiscMonomialResidue hp4 a k)).comp
        (C ((p:ℤ_[p])^2)*(X-C eta))).coeff n‖ ≤ ‖(p:ℤ_[p])^(m+1)‖ := by
  have h := integralPolynomial_comp_coeff_bound _ (C ((p:ℤ_[p])^2)*(X-C eta)) _ (norm_nonneg _)
    (primeDiscTest_V_jet_error hp4 T a _ k _ (norm_nonneg _)
      (integralDiscTestPolynomial_jet_error T a m k c hT)) n
  simpa only [sub_comp,mul_comp,C_comp] using h

theorem primeDiscTest_scaled_jet_error (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (m k : ℕ) (c : ℤ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^m)*X^k*(C c+C (p:ℤ)*E)) (n : ℕ) :
    ‖(primeDiscTestScaled hp4 a T eta - C ((p:ℤ_[p])^m*(c:ℤ_[p]))*
      primeDiscMonomialScaled hp4 a k eta).coeff n‖ ≤ ‖(p:ℤ_[p])^(m+1)‖ := by
  exact integralPolynomial_UV_difference_bound _ _ _ _ _ _ _
    (primeDiscTest_U_substituted_jet_error hp4 T a m k c eta hT)
    (primeDiscTest_V_substituted_jet_error hp4 T a m k c eta hT) n

theorem primeDiscTest_zero_U_leading (hp4 : 3 < p) (T : ℤ[X])
    (m : ℕ) (k : Fin 5) (c : ℤ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p ⟨0,by omega⟩) =
      C ((p:ℤ)^m)*X^k.val*(C c+C (p:ℤ)*E)) (n : ℕ) :
    let a : Fin p := ⟨0,by omega⟩
    ‖(((primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta))).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((((p:ℤ_[p])^m*(c:ℤ_[p]):ℤ_[p]):ℚ_[p])*
        ((primeDiscUnitConstant (p := p) 0 (by omega):ℚ_[p])*
          ((![-113/12,95/4,-253/4,2093/12,-17773/36] k:ℚ):ℚ_[p])))).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(m+1) := by
  dsimp only
  apply integralPolynomial_scaled_rational_leading _
    ((primePoleU hp4 (primeDiscMonomialRegular hp4 ⟨0,by omega⟩ k.val)
      (primeDiscMonomialResidue hp4 ⟨0,by omega⟩ k.val)).comp (C ((p:ℤ_[p])^2)*(X-C eta)))
  · exact primeDiscTest_U_substituted_jet_error hp4 T ⟨0,by omega⟩ m k.val c eta hT
  · exact primeDiscMonomial_zero_U_leading hp4 k eta

theorem primeDiscTest_high_scaled_leading (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (ha : p-4 < a.val) (m : ℕ) (k : Fin 3) (c : ℤ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^m)*X^k.val*(C c+C (p:ℤ)*E)) (n : ℕ) :
    ‖((primeDiscTestScaled hp4 a T eta).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((((p:ℤ_[p])^m*(c:ℤ_[p]):ℤ_[p]):ℚ_[p])*
        (-(a.val:ℚ_[p])*((primeDiscUnitConstant a.val a.isLt:ℚ_[p])*
          ((![8,-46/3,266/9] k:ℚ):ℚ_[p]))))).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(m+1) := by
  apply integralPolynomial_scaled_rational_leading _ (primeDiscMonomialScaled hp4 a k.val eta)
  · exact primeDiscTest_scaled_jet_error hp4 T a m k.val c eta hT
  · intro l
    simpa only [primeDiscMonomialScaled,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
      PadicInt.algebraMap_apply,PadicInt.coe_natCast] using
      primeDiscMonomial_high_scaled_leading hp4 a ha k eta l

end
end Li2

end
