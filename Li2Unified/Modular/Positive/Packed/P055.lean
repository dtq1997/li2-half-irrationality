module
public import Li2Unified.Modular.Positive.Packed.P054
public import Li2Unified.Modular.Base.PrimeMonomialLeading
public import Li2Unified.Modular.Positive.Packed.P053
public import Li2Unified.Modular.Base.PrimeActualLowLeading
public import Li2Unified.Modular.Base.PrimeOtherDiscBounds
public import Li2Unified.Modular.Positive.Packed.P017
public import Li2Unified.Modular.Base.PrimeOriginalLocalBasis
public import Li2Unified.Modular.Positive.Packed.P022
public import Li2Unified.Modular.Base.PrimeGlobalDissection

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterDiscMonomial_low_scaled_leading (lam : ℚ) (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (k : Fin 3) (eta : ℤ_[p]) (n : ℕ) :
    let U := (parameterFourPoleU (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 (primeDiscMonomialRegular hp4 a k.val)
      (primeDiscMonomialResidue hp4 a k.val)).comp (C ((p:ℤ_[p])^2)*(X-C eta))
    let V := (parameterFourPoleV (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 (primeDiscMonomialRegular hp4 a k.val)
      (primeDiscMonomialResidue hp4 a k.val)).comp (C ((p:ℤ_[p])^2)*(X-C eta))
    ‖(C (p:ℚ_[p])*U.map (algebraMap ℤ_[p] ℚ_[p]) -
      C (a.val:ℚ_[p])*V.map (algebraMap ℤ_[p] ℚ_[p]) -
      C (-(a.val:ℚ_[p])*((primeDiscUnitConstant a.val a.isLt:ℚ_[p]) *
        ((lowShapeVValue lam k):ℚ_[p])))).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  dsimp only
  apply integralPolynomial_prime_UV_leading _ _ (a.val:ℤ_[p])
  exact parameterDiscMonomial_low_V_leading lam hu hone hferm hp4 a ha0 ha k eta

theorem parameterDiscMonomial_high_scaled_leading (lam : ℚ) (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (a : Fin p)
    (ha : p-4 < a.val) (k : Fin 3) (eta : ℤ_[p]) (n : ℕ) :
    let U := (parameterFourPoleU (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 (primeDiscMonomialRegular hp4 a k.val)
      (primeDiscMonomialResidue hp4 a k.val)).comp (C ((p:ℤ_[p])^2)*(X-C eta))
    let V := (parameterFourPoleV (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 (primeDiscMonomialRegular hp4 a k.val)
      (primeDiscMonomialResidue hp4 a k.val)).comp (C ((p:ℤ_[p])^2)*(X-C eta))
    ‖(C (p:ℚ_[p])*U.map (algebraMap ℤ_[p] ℚ_[p]) -
      C (a.val:ℚ_[p])*V.map (algebraMap ℤ_[p] ℚ_[p]) -
      C (-(a.val:ℚ_[p])*((primeDiscUnitConstant a.val a.isLt:ℚ_[p]) *
        ((highShapeVValue lam k):ℚ_[p])))).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  dsimp only
  apply integralPolynomial_prime_UV_leading _ _ (a.val:ℤ_[p])
  exact parameterDiscMonomial_high_V_leading lam hu hone hferm hp4 a ha k eta

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterDiscMonomial_low_scaled_leading
#print axioms Li2Unified.Proofs.PrimeEdge.parameterDiscMonomial_high_scaled_leading

end

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def parameterDiscTestScaled (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : Fin p) (T : ℤ[X]) (eta : ℤ_[p]) : (ℤ_[p])[X] :=
  C (p:ℤ_[p])*(parameterFourPoleU z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
    (C ((p:ℤ_[p])^2)*(X-C eta)) -
  C (a.val:ℤ_[p])*(parameterFourPoleV z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
    (C ((p:ℤ_[p])^2)*(X-C eta))

def parameterDiscMonomialScaled (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : Fin p) (k : ℕ) (eta : ℤ_[p]) : (ℤ_[p])[X] :=
  C (p:ℤ_[p])*(parameterFourPoleU z hu hreg hp4 (primeDiscMonomialRegular hp4 a k)
    (primeDiscMonomialResidue hp4 a k)).comp (C ((p:ℤ_[p])^2)*(X-C eta)) -
  C (a.val:ℤ_[p])*(parameterFourPoleV z hu hreg hp4 (primeDiscMonomialRegular hp4 a k)
    (primeDiscMonomialResidue hp4 a k)).comp (C ((p:ℤ_[p])^2)*(X-C eta))

theorem parameterJet_actual_low_scaled_leading (lam : ℚ) (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (i j : Fin (primeMultiplicity p a))
    (eta : ℤ_[p]) (n : ℕ) :
    let k : Fin 3 := ⟨i.val+j.val,primeLow_pair_lt_three hp4 a ha i j⟩
    let c : ℤ_[p] := ((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p])
    let r : ℚ_[p] := -(a.val:ℚ_[p])*((primeDiscUnitConstant a.val a.isLt:ℚ_[p]) *
      ((lowShapeVValue lam k):ℚ_[p]))
    ‖((parameterDiscTestScaled (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 a (primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩) eta).map
      (algebraMap ℤ_[p] ℚ_[p])-C ((((p:ℤ_[p])^(i.val+j.val)*c:ℤ_[p]):ℚ_[p])*r)).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  apply integralPolynomial_scaled_rational_leading _ (parameterDiscMonomialScaled (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 a (i.val+j.val) eta)
  · exact parameterJet_same_UV_substituted_error (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 a i j eta
  · intro k
    simpa only [parameterDiscMonomialScaled,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
      PadicInt.algebraMap_apply,PadicInt.coe_natCast] using!
      parameterDiscMonomial_low_scaled_leading lam hu hone hferm hp4 a ha0 ha
        ⟨i.val+j.val,primeLow_pair_lt_three hp4 a ha i j⟩ eta k

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterJet_actual_low_scaled_leading

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterDiscTest_U_substituted_factor_bound (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (T : ℤ[X])
    (a : Fin p) (m : ℕ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) = C ((p:ℤ)^m)*E) (n : ℕ) :
    ‖((parameterFourPoleU z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta))).coeff n‖ ≤ ‖(p:ℤ_[p])^m‖ := by
  apply integralPolynomial_comp_coeff_bound _ _ _ (norm_nonneg _)
  exact parameterDiscTest_U_coeff_bound z hu hreg hp4 T a _ (norm_nonneg _)
    (integralDiscTestPolynomial_factor_bound T a m hT)

theorem parameterDiscTest_V_substituted_factor_bound (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (T : ℤ[X])
    (a : Fin p) (m : ℕ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) = C ((p:ℤ)^m)*E) (n : ℕ) :
    ‖((parameterFourPoleV z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta))).coeff n‖ ≤ ‖(p:ℤ_[p])^m‖ := by
  apply integralPolynomial_comp_coeff_bound _ _ _ (norm_nonneg _)
  exact parameterDiscTest_V_coeff_bound z hu hreg hp4 T a _ (norm_nonneg _)
    (integralDiscTestPolynomial_factor_bound T a m hT)

theorem parameterDiscTestScaled_factor_bound (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (T : ℤ[X])
    (a : Fin p) (m : ℕ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) = C ((p:ℤ)^m)*E) (n : ℕ) :
    ‖(parameterDiscTestScaled z hu hreg hp4 a T eta).coeff n‖ ≤ ‖(p:ℤ_[p])^m‖ := by
  have h := integralPolynomial_UV_difference_bound
    ((parameterFourPoleU z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta)))
    ((parameterFourPoleV z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta))) 0 0 (a.val:ℤ_[p]) 0 _
    (by simpa only [C_0,zero_mul,sub_zero] using!
      parameterDiscTest_U_substituted_factor_bound z hu hreg hp4 T a m eta hT)
    (by simpa only [C_0,zero_mul,sub_zero] using!
      parameterDiscTest_V_substituted_factor_bound z hu hreg hp4 T a m eta hT) n
  simpa only [parameterDiscTestScaled,C_0,zero_mul,mul_zero,sub_zero] using! h

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterDiscTestScaled_factor_bound

end

section
open Polynomial Li2 Li2Unified.Proofs.Hermite
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterPulledValue_field (lam : ℚ)
    (hunit : lam^p ≠ 0 ∧ padicValRat p (lam^p) = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (Y : ℚ_[p])
    (m : ℕ) (hm : m ≤ 4*p-4) (F : ℚ[X]) (a : Fin p) :
    parameterPulledValue lam hreg Y m F a =
      (fieldParameterFourPoleU (lam^p) hunit hreg hp4 (originalPulledRegular m F a)
        (originalPulledResidue m hm F a)).eval Y - (a.val:ℚ_[p])/(p:ℚ_[p]) *
      (fieldParameterFourPoleV (lam^p) hunit hreg hp4 (originalPulledRegular m F a)
        (originalPulledResidue m hm F a)).eval Y := by
  have hu := original_fieldPoleFunctional
    (fun n : ℕ => ((n+1:ℕ):ℤ_[p])*integralParameterMoment (lam^p) hreg n)
    (fun j : Fin 4 => (integralUPole (lam^p) hunit.1 hunit.2 j.val (by omega)).map (algebraMap ℤ_[p] ℚ_[p]))
    m hm F a
  have hv := original_fieldPoleFunctional
    (derivativeMoments (integralParameterMoment (lam^p) hreg))
    (fun j : Fin 4 => (integralVPole (lam^p) hunit.1 hunit.2 j.val (by omega)).map (algebraMap ℤ_[p] ℚ_[p]))
    m hm F a
  change _ = (fieldPoleFunctional _ _ _ _).eval Y - _*(fieldPoleFunctional _ _ _ _).eval Y
  rw [hu, hv]
  simp only [eval_add, eval_finset_sum, eval_mul, eval_C]
  rw [mul_add, add_sub_add_comm]
  unfold parameterPulledValue
  dsimp only
  rw [← parameter_original_pulled_polynomial_UV (lam^p) hunit hreg hp4 m F a Y]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro j _
  unfold parameterPulledSimplePole
  rw [parameter_original_pulled_simplePole_UV (lam^p) hunit hreg hp4 Y j.val a.val
    ((Finset.mem_Icc.mp j.property).2.trans hm) a.isLt]
  simp only [originalResidue, Rat.cast_div, fieldParameterFourPoleU, fieldParameterFourPoleV]
  ring

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterPulledValue_field

end

section
open Polynomial Li2 Li2Unified.Proofs.Hermite
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterPulledValue_integral_of_cleared (lam : ℚ)
    (hunit : lam^p ≠ 0 ∧ padicValRat p (lam^p) = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (Y : ℚ_[p])
    (m : ℕ) (hm : m ≤ 4*p-4) (F : ℚ[X]) (a : Fin p) (c : ℚ_[p])
    (g : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g) (r : Fin 4 → ℤ_[p])
    (he : primeDiscPolynomialSeries a.val m *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (integralPoleNumerator (primePoleCenters p) g r) =
      PowerSeries.C c * (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
        rationalPolynomialSeries (F.comp (C (p:ℚ)*X-C (a.val:ℚ)))) :
    c * parameterPulledValue lam hreg Y m F a =
      (parameterFourPoleU (lam^p) hunit hreg hp4 g r).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y - (a.val:ℚ_[p])/(p:ℚ_[p]) *
        (parameterFourPoleV (lam^p) hunit hreg hp4 g r).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y := by
  obtain ⟨hgEq,hrEq⟩ := originalPulled_eq_integral_of_cleared m hm F a c g hg r he
  have hu : C c * fieldParameterFourPoleU (lam^p) hunit hreg hp4 (originalPulledRegular m F a)
      (originalPulledResidue m hm F a) =
      (parameterFourPoleU (lam^p) hunit hreg hp4 g r).map (algebraMap ℤ_[p] ℚ_[p]) := by
    change C c * fieldPoleFunctional _ _ _ _ = _
    rw [← fieldPoleFunctional_smul _ _ _ (originalPulledRegular_isRestricted m F a) _ c,
      hgEq, hrEq]
    exact fieldParameterFourPoleU_integral (lam^p) hunit hreg hp4 g hg r
  have hv : C c * fieldParameterFourPoleV (lam^p) hunit hreg hp4 (originalPulledRegular m F a)
      (originalPulledResidue m hm F a) =
      (parameterFourPoleV (lam^p) hunit hreg hp4 g r).map (algebraMap ℤ_[p] ℚ_[p]) := by
    change C c * fieldPoleFunctional _ _ _ _ = _
    rw [← fieldPoleFunctional_smul _ _ _ (originalPulledRegular_isRestricted m F a) _ c,
      hgEq, hrEq]
    exact fieldParameterFourPoleV_integral (lam^p) hunit hreg hp4 g hg r
  have hu' := congrArg (fun P : (ℚ_[p])[X] => P.eval Y) hu
  have hv' := congrArg (fun P : (ℚ_[p])[X] => P.eval Y) hv
  simp only [eval_mul, eval_C, eval_map] at hu' hv'
  rw [parameterPulledValue_field lam hunit hreg hp4 Y m hm F a, mul_sub, hu']
  rw [← hv']
  ring


theorem parameterPulledValue_integer_test (lam : ℚ)
    (hunit : lam^p ≠ 0 ∧ padicValRat p (lam^p) = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (Y : ℚ_[p])
    (m : ℕ) (hm : m ≤ 4*p-4) (F : ℚ[X]) (a : Fin p) (c : ℚ_[p])
    (g : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g) (r : Fin 4 → ℤ_[p])
    (he : primeDiscPolynomialSeries a.val m *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (integralPoleNumerator (primePoleCenters p) g r) =
      PowerSeries.C c * (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
        rationalPolynomialSeries (F.comp (C (p:ℚ)*X-C (a.val:ℚ)))) (T : ℤ[X]) :
    let gT := integralPoleMulRegular (primePoleCenters p)
      (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) g r
    let rT := integralPoleMulResidue (primePoleCenters p)
      (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) r
    c * parameterPulledValue lam hreg
      Y m (F*T.map (Int.castRingHom ℚ)) a =
      (parameterFourPoleU (lam^p) hunit hreg hp4 gT rT).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y - (a.val:ℚ_[p])/(p:ℚ_[p]) *
        (parameterFourPoleV (lam^p) hunit hreg hp4 gT rT).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y := by
  apply parameterPulledValue_integral_of_cleared lam hunit hreg hp4 Y m hm
  · exact integralPoleMulRegular_isRestricted _ _ _ (polynomial_isRestricted _) hg _
  · exact original_test_integral_cleared m F a c g r he T


theorem parameterPulledValue_all_integer_tests (lam : ℚ)
    (hunit : lam^p ≠ 0 ∧ padicValRat p (lam^p) = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (Y : ℚ_[p])
    (a : Fin p) (T : ℤ[X]) :
    primeDiscScale a * parameterPulledValue lam hreg
      Y (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ)) a =
      (parameterFourPoleU (lam^p) hunit hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).eval₂
        (algebraMap ℤ_[p] ℚ_[p]) Y - (a.val:ℚ_[p])/(p:ℚ_[p]) *
      (parameterFourPoleV (lam^p) hunit hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).eval₂
        (algebraMap ℤ_[p] ℚ_[p]) Y :=
  parameterPulledValue_integer_test lam hunit hreg hp4 Y (4*(p-1)) (by omega) ((D (p-1))^3) a
    (primeDiscScale a) (primeDiscRegular hp4 a) (primeDiscRegular_isRestricted hp4 a)
    (primeDiscResidue hp4 a) (original_disc_integral_cleared hp4 a) T

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterPulledValue_all_integer_tests

end

section
open Polynomial Li2 Li2Unified.Proofs.Hermite Li2Unified.LambdaLift
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def parameterDiscTestFieldUV (z : ℚ) (hzunit : z ≠ 0 ∧ padicValRat p z = 0)
    (hzreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : Fin p) (T : ℤ[X]) (eta : ℤ_[p]) : (ℚ_[p])[X] :=
  ((parameterFourPoleU z hzunit hzreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).map
    (algebraMap ℤ_[p] ℚ_[p])).comp (C ((p:ℚ_[p])^2)*(X-C (eta:ℚ_[p]))) -
  C ((a.val:ℚ_[p])/(p:ℚ_[p])) *
    ((parameterFourPoleV z hzunit hzreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).map
      (algebraMap ℤ_[p] ℚ_[p])).comp (C ((p:ℚ_[p])^2)*(X-C (eta:ℚ_[p])))

def parameterDiscContribution (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (a : Fin p) (T : ℤ[X]) : (ℚ_[p])[X] :=
  C ((primeDiscScale a)⁻¹) * parameterDiscTestFieldUV (lam^p) (parameter_power_unit lam hu) hreg hp4 a T
    (parameterIntegralEta lam hu hreg)

lemma parameterDiscContribution_eval (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (a : Fin p) (T : ℤ[X]) (x : ℚ_[p]) :
    (parameterDiscContribution lam hu hreg hp4 a T).eval x =
      parameterPulledValue lam hreg
        ((p:ℚ_[p])^2*(x-(parameterIntegralEta lam hu hreg:ℚ_[p])))
        (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ)) a := by
  have h := parameterPulledValue_all_integer_tests lam (parameter_power_unit lam hu) hreg hp4
    ((p:ℚ_[p])^2*(x-(parameterIntegralEta lam hu hreg:ℚ_[p]))) a T
  simp only [parameterDiscContribution,parameterDiscTestFieldUV,eval_mul,eval_C,eval_sub,
    eval_comp,eval_X,eval_map]
  rw [← h]
  exact inv_mul_cancel_left₀ (primeDiscScale_ne_zero hp4 a) _

theorem parameterNumerator_global_dissection (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p)
    (hz1 : lam^p ≠ 1) (T : ℤ[X]) :
    (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
      (Rat.castHom ℚ_[p]) =
      ∑ a : Fin p, C ((lam:ℚ_[p])⁻¹^a.val)*parameterDiscContribution lam hu hreg hp4 a T := by
  apply Polynomial.funext
  intro x
  rw [eval_map,numeratorFunctional_pulled_eval lam _ _ hlam hu.1
    (Or.inr (by rw [(parameter_power_unit lam hu).2]; norm_num)) hreg hz1]
  simp only [eval_finset_sum,eval_mul,eval_C,parameterDiscContribution_eval, parameterPoleShiftY, parameterIntegralEta_coe]

lemma parameterDiscTestFieldUV_eq_div_scaled (z : ℚ)
    (hzunit : z ≠ 0 ∧ padicValRat p z = 0)
    (hzreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : Fin p)
    (T : ℤ[X]) (eta : ℤ_[p]) :
    parameterDiscTestFieldUV z hzunit hzreg hp4 a T eta = C ((p:ℚ_[p])⁻¹)*
      (parameterDiscTestScaled z hzunit hzreg hp4 a T eta).map (algebraMap ℤ_[p] ℚ_[p]) := by
  have h := polynomial_divide_scaled_UV
    (((parameterFourPoleU z hzunit hzreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).map
      (algebraMap ℤ_[p] ℚ_[p])).comp (C ((p:ℚ_[p])^2)*(X-C (eta:ℚ_[p]))))
    (((parameterFourPoleV z hzunit hzreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).map
      (algebraMap ℤ_[p] ℚ_[p])).comp (C ((p:ℚ_[p])^2)*(X-C (eta:ℚ_[p]))))
    0 0 (a.val:ℚ_[p]) 0
  simpa only [parameterDiscTestFieldUV,parameterDiscTestScaled,Polynomial.map_sub,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_comp,Polynomial.map_X,PadicInt.algebraMap_apply,
    PadicInt.coe_natCast,PadicInt.coe_pow,C_0,zero_mul,mul_zero,sub_zero] using! h.symm

lemma parameterDiscContribution_scaled (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (a : Fin p) (T : ℤ[X]) :
    C ((p:ℚ_[p])^2)*parameterDiscContribution lam hu hreg hp4 a T =
      C ((p:ℚ_[p])/primeDiscScale a)*
        (parameterDiscTestScaled (lam^p) (parameter_power_unit lam hu) hreg hp4 a T (parameterIntegralEta lam hu hreg)).map
          (algebraMap ℤ_[p] ℚ_[p]) := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [parameterDiscContribution,parameterDiscTestFieldUV_eq_div_scaled]
  rw [← mul_assoc,← mul_assoc,← C_mul,← C_mul]
  congr 2
  field_simp

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterNumerator_global_dissection

end

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma parameterDiscContribution_scaled_zero (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (a : Fin p)
    (ha : a.val = 0) (T : ℤ[X]) :
    C ((p:ℚ_[p])^2)*parameterDiscContribution lam hu hreg hp4 a T =
      C ((p:ℚ_[p])⁻¹)*
        (((parameterFourPoleU (lam^p) (parameter_power_unit lam hu) hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
          (C ((p:ℤ_[p])^2)*(X-C (parameterIntegralEta lam hu hreg)))).map
            (algebraMap ℤ_[p] ℚ_[p])) := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have he : (p:ℚ_[p])^2*((p:ℚ_[p])^3)⁻¹ = (p:ℚ_[p])⁻¹ := by field_simp
  simp only [parameterDiscContribution,parameterDiscTestFieldUV,primeDiscScale,ha,ite_true,
    Nat.cast_zero,zero_div,C_0,zero_mul,sub_zero,Polynomial.map_comp,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_sub,Polynomial.map_X,PadicInt.algebraMap_apply,
    PadicInt.coe_pow,PadicInt.coe_natCast,← mul_assoc,← C_mul,he]

lemma parameterDiscContribution_scaled_low (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (T : ℤ[X]) :
    C ((p:ℚ_[p])^2)*parameterDiscContribution lam hu hreg hp4 a T =
      (parameterDiscTestScaled (lam^p) (parameter_power_unit lam hu) hreg hp4 a T (parameterIntegralEta lam hu hreg)).map
        (algebraMap ℤ_[p] ℚ_[p]) := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [parameterDiscContribution_scaled]
  simp only [primeDiscScale,if_neg (by omega : a.val ≠ 0),if_pos ha,div_self hp0,C_1,one_mul]

lemma parameterDiscContribution_scaled_high (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (a : Fin p)
    (ha : p-4 < a.val) (T : ℤ[X]) :
    C ((p:ℚ_[p])^2)*parameterDiscContribution lam hu hreg hp4 a T =
      C (p:ℚ_[p])*(parameterDiscTestScaled (lam^p) (parameter_power_unit lam hu) hreg hp4 a T (parameterIntegralEta lam hu hreg)).map
        (algebraMap ℤ_[p] ℚ_[p]) := by
  rw [parameterDiscContribution_scaled]
  simp only [primeDiscScale,if_neg (by omega : a.val ≠ 0),if_neg (by omega : ¬ a.val ≤ p-4),div_one]

theorem parameterJet_other_contribution_scaled_bound (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) (b : Fin p) (hb : b ≠ a) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^2)*parameterDiscContribution lam hu hreg hp4 b
      (primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^3 := by
  let T := primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩
  have hT := primeJet_same_other_product_factor a i j b hb
  have hn : ‖(p:ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (p:ℤ_[p])
  change ‖(C ((p:ℚ_[p])^2)*parameterDiscContribution lam hu hreg hp4 b T).coeff n‖ ≤ _
  by_cases hz : b.val = 0
  · have hm : primeMultiplicity p b = 2 := primeMultiplicity_low hp4 b (by omega)
    have ht : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p b) = C ((p:ℤ)^4)*E := by
      simpa only [hm] using! hT
    rw [parameterDiscContribution_scaled_zero lam hu hreg hp4 b hz T]
    apply fieldPolynomial_div_prime_bound _ 3
    intro k
    simpa only [coeff_map,norm_pow] using! parameterDiscTest_U_substituted_factor_bound (lam^p) (parameter_power_unit lam hu) hreg hp4 T b 4
      (parameterIntegralEta lam hu hreg) ht k
  · by_cases hl : b.val ≤ p-4
    · have hm : primeMultiplicity p b = 2 := primeMultiplicity_low hp4 b hl
      have ht : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p b) = C ((p:ℤ)^4)*E := by
        simpa only [hm] using! hT
      rw [parameterDiscContribution_scaled_low lam hu hreg hp4 b (by omega) hl T]
      have h := parameterDiscTestScaled_factor_bound (lam^p) (parameter_power_unit lam hu) hreg hp4 T b 4
        (parameterIntegralEta lam hu hreg) ht n
      have hc : ‖((parameterDiscTestScaled (lam^p) (parameter_power_unit lam hu) hreg hp4 b T (parameterIntegralEta lam hu hreg)).map
          (algebraMap ℤ_[p] ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^4 := by
        simpa only [coeff_map,norm_pow] using! h
      exact hc.trans (pow_le_pow_of_le_one (norm_nonneg _) hn (by omega))
    · have hm : primeMultiplicity p b = 1 := by
        unfold primeMultiplicity
        rw [if_neg (by omega)]
      have ht : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p b) = C ((p:ℤ)^2)*E := by
        simpa only [hm] using! hT
      rw [parameterDiscContribution_scaled_high lam hu hreg hp4 b (by omega) T,coeff_C_mul,norm_mul]
      have h := parameterDiscTestScaled_factor_bound (lam^p) (parameter_power_unit lam hu) hreg hp4 T b 2
        (parameterIntegralEta lam hu hreg) ht n
      have hc : ‖((parameterDiscTestScaled (lam^p) (parameter_power_unit lam hu) hreg hp4 b T (parameterIntegralEta lam hu hreg)).map
          (algebraMap ℤ_[p] ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^2 := by
        simpa only [coeff_map,norm_pow] using! h
      calc
        _ ≤ ‖(p:ℚ_[p])‖*‖(p:ℚ_[p])‖^2 := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
        _ = _ := by ring

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterJet_other_contribution_scaled_bound

end


end
