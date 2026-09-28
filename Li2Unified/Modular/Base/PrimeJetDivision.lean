module
public import Li2Unified.Modular.Base.PrimeScaledJetError

set_option backward.privateInPublic true

@[expose] public section

/-! Dividing pU-aV by p loses exactly one order in its coefficient bound. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma fieldPolynomial_div_prime_bound (F : (ℚ_[p])[X]) (m : ℕ)
    (hF : ∀ n, ‖F.coeff n‖ ≤ ‖(p:ℚ_[p])‖^(m+1)) (n : ℕ) :
    ‖(C ((p:ℚ_[p])⁻¹)*F).coeff n‖ ≤ ‖(p:ℚ_[p])‖^m := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hn0 : ‖(p:ℚ_[p])‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
  rw [coeff_C_mul,norm_mul,norm_inv]
  calc
    _ ≤ ‖(p:ℚ_[p])‖⁻¹*‖(p:ℚ_[p])‖^(m+1) :=
      mul_le_mul_of_nonneg_left (hF n) (inv_nonneg.mpr (norm_nonneg _))
    _ = _ := by rw [pow_succ]; field_simp

lemma polynomial_divide_scaled_UV (U V H K : (ℚ_[p])[X]) (a q : ℚ_[p]) :
    C ((p:ℚ_[p])⁻¹)*((C (p:ℚ_[p])*U-C a*V)-C q*(C (p:ℚ_[p])*H-C a*K)) =
      (U-C (a/(p:ℚ_[p]))*V)-C q*(H-C (a/(p:ℚ_[p]))*K) := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hc : C ((p:ℚ_[p])⁻¹)*C (p:ℚ_[p]) = (1:(ℚ_[p])[X]) := by
    rw [← C_mul,inv_mul_cancel₀ hp0,C_1]
  have hd : C ((p:ℚ_[p])⁻¹)*C a = (C (a/(p:ℚ_[p])) : (ℚ_[p])[X]) := by
    rw [← C_mul]
    congr 1
    simp only [div_eq_mul_inv]
    ring
  calc
    _ = (C ((p:ℚ_[p])⁻¹)*C (p:ℚ_[p]))*(U-C q*H)-
        (C ((p:ℚ_[p])⁻¹)*C a)*(V-C q*K) := by ring
    _ = _ := by rw [hc,hd]; ring

theorem integralPolynomial_UV_division_bound
    (U V H K : (ℤ_[p])[X]) (a q : ℤ_[p]) (m : ℕ)
    (he : ∀ n, ‖((C (p:ℤ_[p])*U-C a*V)-C q*(C (p:ℤ_[p])*H-C a*K)).coeff n‖ ≤
      ‖(p:ℤ_[p])^(m+1)‖) (n : ℕ) :
    ‖((U.map (algebraMap ℤ_[p] ℚ_[p])-C ((a:ℚ_[p])/(p:ℚ_[p]))*V.map (algebraMap ℤ_[p] ℚ_[p]))-
      C (q:ℚ_[p])*(H.map (algebraMap ℤ_[p] ℚ_[p])-
        C ((a:ℚ_[p])/(p:ℚ_[p]))*K.map (algebraMap ℤ_[p] ℚ_[p]))).coeff n‖ ≤ ‖(p:ℚ_[p])‖^m := by
  have hb := fieldPolynomial_div_prime_bound
    (((C (p:ℤ_[p])*U-C a*V)-C q*(C (p:ℤ_[p])*H-C a*K)).map (algebraMap ℤ_[p] ℚ_[p]))
    m (fun k => by simpa only [coeff_map,norm_pow] using he k) n
  simpa only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
    PadicInt.algebraMap_apply,PadicInt.coe_natCast,polynomial_divide_scaled_UV] using hb

theorem primeJet_same_UV_unscaled_error (hp4 : 3 < p) (a : Fin p)
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
    ‖((U.map (algebraMap ℤ_[p] ℚ_[p])-C ((a.val:ℚ_[p])/(p:ℚ_[p]))*V.map (algebraMap ℤ_[p] ℚ_[p]))-
      C (q:ℚ_[p])*(H.map (algebraMap ℤ_[p] ℚ_[p])-
        C ((a.val:ℚ_[p])/(p:ℚ_[p]))*K.map (algebraMap ℤ_[p] ℚ_[p]))).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val) := by
  dsimp only
  exact integralPolynomial_UV_division_bound _ _ _ _ (a.val:ℤ_[p]) _ _
    (primeJet_same_UV_substituted_error hp4 a i j eta) n

end
end Li2

end
