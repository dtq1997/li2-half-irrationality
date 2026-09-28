module
public import Li2Unified.Modular.Positive.Packed.P052
public import Li2Unified.Modular.Positive.Packed.P042
public import Li2Unified.Modular.Base.DetCongruence
public import Li2Unified.Modular.Positive.Packed.P013
public import Li2Unified.Modular.Base.PrimeIntegralJetBounds
public import Li2Unified.Modular.Base.PrimeDiscJetTransfer
public import Li2Unified.Modular.Base.PrimeProductJetError
public import Li2Unified.Modular.Base.PrimeScaledJetError
public import Li2Unified.Modular.Positive.Packed.P014
public import Li2Unified.Modular.Base.RationalPoleClearing

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
open Li2Unified.ParameterFamily
variable {p : ℕ} [hp : Fact p.Prime]

def parameterReferenceMatrix (lam : ℚ) (p : ℕ) (corner : Matrix (Fin 6) (Fin 6) ℚ) :
    Matrix (PrimeBlockIndex p) (PrimeBlockIndex p) ℚ[X] :=
  fun x y => C ((p:ℚ)^primeReferenceRowExponent x *
    ((p:ℚ)^primeReferenceColExponent y * parameterReferenceCore lam p corner x y))

theorem parameterReferenceMatrix_det (lam : ℚ) (corner : Matrix (Fin 6) (Fin 6) ℚ) (hp4 : 3 < p) :
    (parameterReferenceMatrix lam p corner).det =
      C ((p:ℚ)^(-2*((p-1:ℕ):ℤ))*(parameterReferenceCore lam p corner).det) := by
  classical
  let A : Matrix (PrimeBlockIndex p) (PrimeBlockIndex p) ℚ := Matrix.of (fun x y =>
    (p:ℚ)^primeReferenceRowExponent x *
      ((p:ℚ)^primeReferenceColExponent y * parameterReferenceCore lam p corner x y))
  have hN : parameterReferenceMatrix lam p corner = (Polynomial.C : ℚ →+* ℚ[X]).mapMatrix A := by
    funext x y
    rfl
  have hA : A.det =
      ((∏ x : PrimeBlockIndex p, (p:ℚ)^primeReferenceRowExponent x) *
        (∏ x : PrimeBlockIndex p, (p:ℚ)^primeReferenceColExponent x)) *
          (parameterReferenceCore lam p corner).det := by
    dsimp only [A]
    rw [Matrix.det_mul_column]
    change
      (∏ x : PrimeBlockIndex p, (p:ℚ)^primeReferenceRowExponent x) *
        (Matrix.of (fun x y : PrimeBlockIndex p =>
          (p:ℚ)^primeReferenceColExponent y * parameterReferenceCore lam p corner x y)).det =
      ((∏ x : PrimeBlockIndex p, (p:ℚ)^primeReferenceRowExponent x) *
        (∏ x : PrimeBlockIndex p, (p:ℚ)^primeReferenceColExponent x)) *
          (parameterReferenceCore lam p corner).det
    rw [Matrix.det_mul_row]
    ring
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hr := primeReference_prod_zpow (p := p) Finset.univ
    (primeReferenceRowExponent (p := p))
  have hc := primeReference_prod_zpow (p := p) Finset.univ
    (primeReferenceColExponent (p := p))
  have hscale :
      (∏ x : PrimeBlockIndex p, (p:ℚ)^primeReferenceRowExponent x) *
        (∏ x : PrimeBlockIndex p, (p:ℚ)^primeReferenceColExponent x) =
        (p:ℚ)^(-2*((p-1:ℕ):ℤ)) := by
    rw [hr,hc,← zpow_add₀ hpq,primeReference_exponent_sum hp4]
  calc
    (parameterReferenceMatrix lam p corner).det = C A.det := by
      rw [hN,← (Polynomial.C : ℚ →+* ℚ[X]).map_det A]
    _ = C ((p:ℚ)^(-2*((p-1:ℕ):ℤ))*(parameterReferenceCore lam p corner).det) := by
      rw [hA,hscale]


theorem parameterReferenceCore_unit (lam : ℚ) (corner : Matrix (Fin 6) (Fin 6) ℚ)
    (hp4 : 3 < p) (h1 : lam ≠ 1)
    (hlam : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hlow : lowBlockConstant lam ≠ 0 ∧ padicValRat p (lowBlockConstant lam) = 0)
    (hcorner : corner.det ≠ 0 ∧ padicValRat p corner.det = 0) :
    (parameterReferenceCore lam p corner).det ≠ 0 ∧
      padicValRat p (parameterReferenceCore lam p corner).det = 0 := by
  have hmul (x y : ℚ) (hx : x ≠ 0 ∧ padicValRat p x = 0)
      (hy : y ≠ 0 ∧ padicValRat p y = 0) :
      x*y ≠ 0 ∧ padicValRat p (x*y) = 0 :=
    ⟨mul_ne_zero hx.1 hy.1,by rw [padicValRat.mul hx.1 hy.1,hx.2,hy.2,add_zero]⟩
  have hpow (x : ℚ) (hx : x ≠ 0 ∧ padicValRat p x = 0) (n : ℕ) :
      x^n ≠ 0 ∧ padicValRat p (x^n) = 0 :=
    ⟨pow_ne_zero n hx.1,by rw [padicValRat.pow hx.1,hx.2,mul_zero]⟩
  rw [parameterReferenceCore_det lam p corner hlam.1 h1]
  have hprod := rational_prime_unit_finset_prod (p := p) Finset.univ
    (fun a : Fin (p-4) => (parameterLowWeight lam (a.val+1))^2) (by
      intro a _
      have ha := a.isLt
      exact hpow _ (parameterLowWeight_unit lam hp4 hlam (a.val+1)
        (by omega) (by omega)) 2)
  exact hmul _ _ (hmul _ _ hprod (hpow _ hlow (p-4))) hcorner

theorem posHalf_referenceCore_unit (corner : Matrix (Fin 6) (Fin 6) ℚ)
    (hp4 : 3 < p) (hbad : p ∉ Instances.PosHalf.badPrimes)
    (hdet : corner.det = cornerBlockConstant Instances.PosHalf.lambda) :
    (parameterReferenceCore Instances.PosHalf.lambda p corner).det ≠ 0 ∧
      padicValRat p (parameterReferenceCore Instances.PosHalf.lambda p corner).det = 0 := by
  apply parameterReferenceCore_unit _ corner hp4 Instances.PosHalf.lambda_ne_one
    (Instances.PosHalf.parameter_units p hbad).1 (Instances.PosHalf.lowBlockConstant_unit p hbad)
  rw [hdet]
  exact Instances.PosHalf.cornerBlockConstant_unit p hbad

end
end Li2Unified.Proofs.PrimeEdge

#print axioms Li2Unified.Proofs.PrimeEdge.parameterReferenceMatrix_det
#print axioms Li2Unified.Proofs.PrimeEdge.posHalf_referenceCore_unit

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterDiscTest_U_coeff_bound (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (B : ℝ) (hB : 0 ≤ B) (hT : ∀ k, ‖(integralDiscTestPolynomial T a).coeff k‖ ≤ B) (n : ℕ) :
    ‖(parameterFourPoleU z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).coeff n‖ ≤ B := by
  apply parameterFourPoleU_coeff_bound z hu hreg hp4 _ _ B hB
  · apply integralPoleMulRegular_bound_left _ _ _ _ B hB
    simpa only [Polynomial.coeff_coe] using hT
  · apply integralPoleMulResidue_bound_left _ _ _ B
    simpa only [Polynomial.coeff_coe] using hT

theorem parameterDiscTest_V_coeff_bound (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (B : ℝ) (hB : 0 ≤ B) (hT : ∀ k, ‖(integralDiscTestPolynomial T a).coeff k‖ ≤ B) (n : ℕ) :
    ‖(parameterFourPoleV z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).coeff n‖ ≤ B := by
  apply parameterFourPoleV_coeff_bound z hu hreg hp4 _ _ B hB
  · apply integralPoleMulRegular_bound_left _ _ _ _ B hB
    simpa only [Polynomial.coeff_coe] using hT
  · apply integralPoleMulResidue_bound_left _ _ _ B
    simpa only [Polynomial.coeff_coe] using hT

theorem parameterOriginalBasis_U_substituted_bound (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p)
    (i j : Fin (2*(p-1))) (a : Fin p) (eta : ℤ_[p]) (n : ℕ) :
    let T := primeOriginalBasis p (by omega) i * primeOriginalBasis p (by omega) j
    ‖((parameterFourPoleU z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta))).coeff n‖ ≤
      ‖(p:ℤ_[p])^(primeOriginalBasisLocalOrder p (by omega) i a+
        primeOriginalBasisLocalOrder p (by omega) j a)‖ := by
  dsimp only
  apply integralPolynomial_comp_coeff_bound _ _ _ (norm_nonneg _)
  exact parameterDiscTest_U_coeff_bound z hu hreg hp4 _ a _ (norm_nonneg _)
    (primeOriginalBasisProduct_integral_bound (by omega) i j a)

theorem parameterOriginalBasis_V_substituted_bound (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p)
    (i j : Fin (2*(p-1))) (a : Fin p) (eta : ℤ_[p]) (n : ℕ) :
    let T := primeOriginalBasis p (by omega) i * primeOriginalBasis p (by omega) j
    ‖((parameterFourPoleV z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta))).coeff n‖ ≤
      ‖(p:ℤ_[p])^(primeOriginalBasisLocalOrder p (by omega) i a+
        primeOriginalBasisLocalOrder p (by omega) j a)‖ := by
  dsimp only
  apply integralPolynomial_comp_coeff_bound _ _ _ (norm_nonneg _)
  exact parameterDiscTest_V_coeff_bound z hu hreg hp4 _ a _ (norm_nonneg _)
    (primeOriginalBasisProduct_integral_bound (by omega) i j a)

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterOriginalBasis_U_substituted_bound

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma parameterFourPoleU_multiplier_smul (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (g f : PowerSeries ℤ_[p])
    (hg : PowerSeries.IsRestricted 1 g) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin 4 → ℤ_[p]) (q : ℤ_[p]) :
    parameterFourPoleU z hu hreg hp4 (integralPoleMulRegular (primePoleCenters p) (q • g) f r)
      (integralPoleMulResidue (primePoleCenters p) (q • g) r) =
      C q*parameterFourPoleU z hu hreg hp4 (integralPoleMulRegular (primePoleCenters p) g f r)
        (integralPoleMulResidue (primePoleCenters p) g r) := by
  have h := integralPoleMultiplier_smul (primePoleCenters p) primePoleCenters_injective g f hg hf r q
  rw [h.1,h.2]
  exact restrictedPoleFunctional_smul _ _ _
    (integralPoleMulRegular_isRestricted _ g f hg hf r) _ q

lemma parameterFourPoleV_multiplier_smul (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (g f : PowerSeries ℤ_[p])
    (hg : PowerSeries.IsRestricted 1 g) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin 4 → ℤ_[p]) (q : ℤ_[p]) :
    parameterFourPoleV z hu hreg hp4 (integralPoleMulRegular (primePoleCenters p) (q • g) f r)
      (integralPoleMulResidue (primePoleCenters p) (q • g) r) =
      C q*parameterFourPoleV z hu hreg hp4 (integralPoleMulRegular (primePoleCenters p) g f r)
        (integralPoleMulResidue (primePoleCenters p) g r) := by
  have h := integralPoleMultiplier_smul (primePoleCenters p) primePoleCenters_injective g f hg hf r q
  rw [h.1,h.2]
  exact restrictedPoleFunctional_smul _ _ _
    (integralPoleMulRegular_isRestricted _ g f hg hf r) _ q

theorem parameterDiscTest_U_jet_error (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (q : ℤ_[p]) (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (he : ∀ n, ‖(integralDiscTestPolynomial T a-C q*X^k).coeff n‖ ≤ B) (n : ℕ) :
    ‖(parameterFourPoleU z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T) -
      C q*parameterFourPoleU z hu hreg hp4 (primeDiscMonomialRegular hp4 a k)
        (primeDiscMonomialResidue hp4 a k)).coeff n‖ ≤ B := by
  have h : ‖(parameterFourPoleU z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T) -
      parameterFourPoleU z hu hreg hp4 (integralPoleMulRegular (primePoleCenters p)
        (q • ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p])) (primeDiscRegular hp4 a) (primeDiscResidue hp4 a))
        (integralPoleMulResidue (primePoleCenters p)
          (q • ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p])) (primeDiscResidue hp4 a))).coeff n‖ ≤ B :=
    restrictedPoleFunctional_multiplier_difference _ primePoleCenters_injective _ _ _ _ _
      (polynomial_isRestricted _) (PowerSeries.IsRestricted.smul 1 (polynomial_isRestricted _) q)
      (primeDiscRegular_isRestricted hp4 a) _ B hB (integralDiscTest_series_error T a q k B he) n
  rw [parameterFourPoleU_multiplier_smul z hu hreg hp4 _ _ (polynomial_isRestricted _)
    (primeDiscRegular_isRestricted hp4 a),
    (primeDiscMonomial_from_test hp4 a k).1, (primeDiscMonomial_from_test hp4 a k).2] at h
  exact h

theorem parameterDiscTest_V_jet_error (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (q : ℤ_[p]) (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (he : ∀ n, ‖(integralDiscTestPolynomial T a-C q*X^k).coeff n‖ ≤ B) (n : ℕ) :
    ‖(parameterFourPoleV z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T) -
      C q*parameterFourPoleV z hu hreg hp4 (primeDiscMonomialRegular hp4 a k)
        (primeDiscMonomialResidue hp4 a k)).coeff n‖ ≤ B := by
  have h : ‖(parameterFourPoleV z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T) -
      parameterFourPoleV z hu hreg hp4 (integralPoleMulRegular (primePoleCenters p)
        (q • ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p])) (primeDiscRegular hp4 a) (primeDiscResidue hp4 a))
        (integralPoleMulResidue (primePoleCenters p)
          (q • ((X^k : (ℤ_[p])[X]) : PowerSeries ℤ_[p])) (primeDiscResidue hp4 a))).coeff n‖ ≤ B :=
    restrictedPoleFunctional_multiplier_difference _ primePoleCenters_injective _ _ _ _ _
      (polynomial_isRestricted _) (PowerSeries.IsRestricted.smul 1 (polynomial_isRestricted _) q)
      (primeDiscRegular_isRestricted hp4 a) _ B hB (integralDiscTest_series_error T a q k B he) n
  rw [parameterFourPoleV_multiplier_smul z hu hreg hp4 _ _ (polynomial_isRestricted _)
    (primeDiscRegular_isRestricted hp4 a),
    (primeDiscMonomial_from_test hp4 a k).1, (primeDiscMonomial_from_test hp4 a k).2] at h
  exact h

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterDiscTest_U_jet_error
#print axioms Li2Unified.Proofs.PrimeEdge.parameterDiscTest_V_jet_error

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterJet_same_U_error (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) (n : ℕ) :
    let T := primeJetPoly p ⟨a,i⟩ * primeJetPoly p ⟨a,j⟩
    let q := (p:ℤ_[p])^(i.val+j.val)*((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p])
    ‖(parameterFourPoleU z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T) -
      C q*parameterFourPoleU z hu hreg hp4 (primeDiscMonomialRegular hp4 a (i.val+j.val))
        (primeDiscMonomialResidue hp4 a (i.val+j.val))).coeff n‖ ≤ ‖(p:ℤ_[p])^(i.val+j.val+1)‖ := by
  dsimp only
  apply parameterDiscTest_U_jet_error z hu hreg hp4 _ a _ _ _ (norm_nonneg _)
  exact integralDiscTestPolynomial_jet_error _ a _ _ _ (primeJet_same_product_expansion p a i j)

theorem parameterJet_same_V_error (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) (n : ℕ) :
    let T := primeJetPoly p ⟨a,i⟩ * primeJetPoly p ⟨a,j⟩
    let q := (p:ℤ_[p])^(i.val+j.val)*((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p])
    ‖(parameterFourPoleV z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T) -
      C q*parameterFourPoleV z hu hreg hp4 (primeDiscMonomialRegular hp4 a (i.val+j.val))
        (primeDiscMonomialResidue hp4 a (i.val+j.val))).coeff n‖ ≤ ‖(p:ℤ_[p])^(i.val+j.val+1)‖ := by
  dsimp only
  apply parameterDiscTest_V_jet_error z hu hreg hp4 _ a _ _ _ (norm_nonneg _)
  exact integralDiscTestPolynomial_jet_error _ a _ _ _ (primeJet_same_product_expansion p a i j)

theorem parameterJet_same_U_substituted_error (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) (eta : ℤ_[p]) (n : ℕ) :
    let T := primeJetPoly p ⟨a,i⟩ * primeJetPoly p ⟨a,j⟩
    let q := (p:ℤ_[p])^(i.val+j.val)*((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p])
    let S := C ((p:ℤ_[p])^2)*(X-C eta)
    ‖((parameterFourPoleU z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp S -
      C q*(parameterFourPoleU z hu hreg hp4 (primeDiscMonomialRegular hp4 a (i.val+j.val))
        (primeDiscMonomialResidue hp4 a (i.val+j.val))).comp S).coeff n‖ ≤
      ‖(p:ℤ_[p])^(i.val+j.val+1)‖ := by
  dsimp only
  have h := integralPolynomial_comp_coeff_bound _ (C ((p:ℤ_[p])^2)*(X-C eta)) _
    (norm_nonneg _) (parameterJet_same_U_error z hu hreg hp4 a i j) n
  simpa only [sub_comp,mul_comp,C_comp] using h

theorem parameterJet_same_V_substituted_error (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) (eta : ℤ_[p]) (n : ℕ) :
    let T := primeJetPoly p ⟨a,i⟩ * primeJetPoly p ⟨a,j⟩
    let q := (p:ℤ_[p])^(i.val+j.val)*((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p])
    let S := C ((p:ℤ_[p])^2)*(X-C eta)
    ‖((parameterFourPoleV z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp S -
      C q*(parameterFourPoleV z hu hreg hp4 (primeDiscMonomialRegular hp4 a (i.val+j.val))
        (primeDiscMonomialResidue hp4 a (i.val+j.val))).comp S).coeff n‖ ≤
      ‖(p:ℤ_[p])^(i.val+j.val+1)‖ := by
  dsimp only
  have h := integralPolynomial_comp_coeff_bound _ (C ((p:ℤ_[p])^2)*(X-C eta)) _
    (norm_nonneg _) (parameterJet_same_V_error z hu hreg hp4 a i j) n
  simpa only [sub_comp,mul_comp,C_comp] using h

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterJet_same_U_substituted_error
#print axioms Li2Unified.Proofs.PrimeEdge.parameterJet_same_V_substituted_error

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterJet_same_UV_substituted_error (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) (eta : ℤ_[p]) (n : ℕ) :
    let T := primeJetPoly p ⟨a,i⟩ * primeJetPoly p ⟨a,j⟩
    let q := (p:ℤ_[p])^(i.val+j.val)*((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p])
    let S := C ((p:ℤ_[p])^2)*(X-C eta)
    let U := (parameterFourPoleU z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp S
    let V := (parameterFourPoleV z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp S
    let H := (parameterFourPoleU z hu hreg hp4 (primeDiscMonomialRegular hp4 a (i.val+j.val))
      (primeDiscMonomialResidue hp4 a (i.val+j.val))).comp S
    let K := (parameterFourPoleV z hu hreg hp4 (primeDiscMonomialRegular hp4 a (i.val+j.val))
      (primeDiscMonomialResidue hp4 a (i.val+j.val))).comp S
    ‖((C (p:ℤ_[p])*U-C (a.val:ℤ_[p])*V)-C q*(C (p:ℤ_[p])*H-C (a.val:ℤ_[p])*K)).coeff n‖ ≤
      ‖(p:ℤ_[p])^(i.val+j.val+1)‖ := by
  dsimp only
  exact integralPolynomial_UV_difference_bound _ _ _ _ _ _ _
    (parameterJet_same_U_substituted_error z hu hreg hp4 a i j eta)
    (parameterJet_same_V_substituted_error z hu hreg hp4 a i j eta) n

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterJet_same_UV_substituted_error

end

section
open Polynomial Finset Li2
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterFourPoleUV_rational_of_cleared (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p)
    (g : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g)
    (s : Fin 4 → ℤ_[p]) (f : ℚ[X]) (r : Fin 4 → ℚ)
    (he : PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
        (integralPoleNumerator (primePoleCenters p) g s) =
      ((rationalPoleNumerator f r).map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p]))
    (Y : ℚ_[p]) :
    (parameterFourPoleU z hu hreg hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleU z f r).eval₂ (Rat.castHom ℚ_[p]) Y ∧
      (parameterFourPoleV z hu hreg hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleV z f r).eval₂ (Rat.castHom ℚ_[p]) Y := by
  rw [← fieldPoleNumerator_integral, rationalPoleNumerator_map] at he
  obtain ⟨hf, hr⟩ := fieldPoleNumerator_injective (primePoleCenters p)
    primePoleCenters_injective _ _ (field_map_isRestricted g hg)
    (field_polynomial_isRestricted _) _ _ he
  constructor
  · rw [← eval_map, ← fieldParameterFourPoleU_integral z hu hreg hp4 g hg s, hf, hr]
    exact fieldParameterFourPoleU_rational z hu hreg hp4 f r Y
  · rw [← eval_map, ← fieldParameterFourPoleV_integral z hu hreg hp4 g hg s, hf, hr]
    exact fieldParameterFourPoleV_rational z hu hreg hp4 f r Y

theorem parameterZeroShape_monomial_rational (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (k : Fin 5) (Y : ℚ_[p]) :
    let g := integralPoleMulRegular (primePoleCenters p)
      ((X^(k.val) : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) 0 (primeZeroShapeResidue hp4)
    let s := integralPoleMulResidue (primePoleCenters p)
      ((X^(k.val) : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) (primeZeroShapeResidue hp4)
    (parameterFourPoleU z hu hreg hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleU z (zeroShapeRegular k) (zeroShapeResidue k)).eval₂
          (Rat.castHom ℚ_[p]) Y ∧
      (parameterFourPoleV z hu hreg hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleV z (zeroShapeRegular k) (zeroShapeResidue k)).eval₂
          (Rat.castHom ℚ_[p]) Y := by
  dsimp only
  apply parameterFourPoleUV_rational_of_cleared z hu hreg hp4
  · exact integralPoleMulRegular_isRestricted _ _ _ (polynomial_isRestricted _)
      (by simpa using polynomial_isRestricted (p := p) (0:(ℤ_[p])[X])) _
  · rw [integralPoleNumerator_mul _ _ _ (polynomial_isRestricted _),
      primeZeroShape_cleared, zeroShape_cleared]
    simp [pow_succ]

theorem parameterHighShape_monomial_rational (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (k : Fin 3) (Y : ℚ_[p]) :
    let g := integralPoleMulRegular (primePoleCenters p)
      ((X^(k.val) : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) 1 primeHighShapeResidue
    let s := integralPoleMulResidue (primePoleCenters p)
      ((X^(k.val) : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) primeHighShapeResidue
    (parameterFourPoleU z hu hreg hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleU z (highShapeRegular k) (highShapeResidue k)).eval₂
          (Rat.castHom ℚ_[p]) Y ∧
      (parameterFourPoleV z hu hreg hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleV z (highShapeRegular k) (highShapeResidue k)).eval₂
          (Rat.castHom ℚ_[p]) Y := by
  dsimp only
  apply parameterFourPoleUV_rational_of_cleared z hu hreg hp4
  · exact integralPoleMulRegular_isRestricted _ _ _ (polynomial_isRestricted _)
      (by simpa using polynomial_isRestricted (p := p) (1:(ℤ_[p])[X])) _
  · rw [integralPoleNumerator_mul _ _ _ (polynomial_isRestricted _),
      primeHighShape_cleared, highShape_cleared]
    simp [pow_add, mul_assoc]
    rw [← Polynomial.coe_C]
    congr 1

theorem parameterLowShape_monomial_rational (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (k : Fin 3) (Y : ℚ_[p]) :
    let g := integralPoleMulRegular (primePoleCenters p)
      ((X^(k.val) : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) 0 (primeLowShapeResidue hp4)
    let s := integralPoleMulResidue (primePoleCenters p)
      ((X^(k.val) : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) (primeLowShapeResidue hp4)
    (parameterFourPoleU z hu hreg hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleU z
          (zeroShapeRegular ⟨k.val+2,by omega⟩) (zeroShapeResidue ⟨k.val+2,by omega⟩)).eval₂
          (Rat.castHom ℚ_[p]) Y ∧
      (parameterFourPoleV z hu hreg hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleV z
          (zeroShapeRegular ⟨k.val+2,by omega⟩) (zeroShapeResidue ⟨k.val+2,by omega⟩)).eval₂
          (Rat.castHom ℚ_[p]) Y := by
  dsimp only
  apply parameterFourPoleUV_rational_of_cleared z hu hreg hp4
  · exact integralPoleMulRegular_isRestricted _ _ _ (polynomial_isRestricted _)
      (by simpa using polynomial_isRestricted (p := p) (0:(ℤ_[p])[X])) _
  · rw [integralPoleNumerator_mul _ _ _ (polynomial_isRestricted _),
      primeLowShape_cleared, zeroShape_cleared]
    simp [pow_add, mul_assoc]
    ring

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterFourPoleUV_rational_of_cleared

end


end
