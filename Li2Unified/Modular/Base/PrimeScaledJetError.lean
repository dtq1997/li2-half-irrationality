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

theorem primeJet_same_UV_substituted_error (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) (eta : ℤ_[p]) (n : ℕ) :
    let T := primeJetPoly p ⟨a,i⟩ * primeJetPoly p ⟨a,j⟩
    let q := (p:ℤ_[p])^(i.val+j.val)*((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p])
    let S := C ((p:ℤ_[p])^2)*(X-C eta)
    let U := (primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp S
    let V := (primePoleV hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp S
    let H := (primePoleU hp4 (primeDiscMonomialRegular hp4 a (i.val+j.val))
      (primeDiscMonomialResidue hp4 a (i.val+j.val))).comp S
    let K := (primePoleV hp4 (primeDiscMonomialRegular hp4 a (i.val+j.val))
      (primeDiscMonomialResidue hp4 a (i.val+j.val))).comp S
    ‖((C (p:ℤ_[p])*U-C (a.val:ℤ_[p])*V)-C q*(C (p:ℤ_[p])*H-C (a.val:ℤ_[p])*K)).coeff n‖ ≤
      ‖(p:ℤ_[p])^(i.val+j.val+1)‖ := by
  dsimp only
  exact integralPolynomial_UV_difference_bound _ _ _ _ _ _ _
    (primeJet_same_U_substituted_error hp4 a i j eta)
    (primeJet_same_V_substituted_error hp4 a i j eta) n

end
end Li2

end
