module
public import Li2Unified.Modular.Positive.Packed.P055
public import Li2Unified.Modular.Base.PrimeAugmentedOther
public import Li2Unified.Modular.Base.PrimeActualLowLeading
public import Li2Unified.Modular.Base.PrimeAugmentedJets

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterDiscContribution_scaled_factor_bound (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (T : ℤ[X]) (b : Fin p)
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p b) =
      C ((p:ℤ)^(2*primeMultiplicity p b))*E) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^2)*parameterDiscContribution lam hu hreg hp4 b T).coeff n‖ ≤ ‖(p:ℚ_[p])‖^3 := by
  have hn : ‖(p:ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (p:ℤ_[p])
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
    · have hm : primeMultiplicity p b = 1 := by unfold primeMultiplicity; rw [if_neg (by omega)]
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

theorem parameterAugmented_other_contribution_scaled_bound (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a+1)) (b : Fin p) (hb : b ≠ a) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^2)*parameterDiscContribution lam hu hreg hp4 b
      (primeAugmentedJet p a i*primeAugmentedJet p a j)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^3 :=
  parameterDiscContribution_scaled_factor_bound lam hu hreg hp4 _ b (primeAugmentedJet_other_product_factor a i j b hb) n

theorem parameterAugmented_other_contribution_cube_bound (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a+1)) (b : Fin p) (hb : b ≠ a) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu hreg hp4 b
      (primeAugmentedJet p a i*primeAugmentedJet p a j)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^4 := by
  have he : (C ((p:ℚ_[p])^3) : (ℚ_[p])[X]) = C (p:ℚ_[p])*C ((p:ℚ_[p])^2) := by rw [← C_mul]; congr 1; ring
  rw [he,mul_assoc,coeff_C_mul,norm_mul]
  calc
    _ ≤ ‖(p:ℚ_[p])‖*‖(p:ℚ_[p])‖^3 := mul_le_mul_of_nonneg_left
      (parameterAugmented_other_contribution_scaled_bound lam hu hreg hp4 a i j b hb n) (norm_nonneg _)
    _ = _ := by ring

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterAugmented_other_contribution_cube_bound

end

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterDiscTest_U_substituted_jet_error (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (m k : ℕ) (c : ℤ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^m)*X^k*(C c+C (p:ℤ)*E)) (n : ℕ) :
    ‖((parameterFourPoleU z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta)) - C ((p:ℤ_[p])^m*(c:ℤ_[p]))*
      (parameterFourPoleU z hu hreg hp4 (primeDiscMonomialRegular hp4 a k) (primeDiscMonomialResidue hp4 a k)).comp
        (C ((p:ℤ_[p])^2)*(X-C eta))).coeff n‖ ≤ ‖(p:ℤ_[p])^(m+1)‖ := by
  have h := integralPolynomial_comp_coeff_bound _ (C ((p:ℤ_[p])^2)*(X-C eta)) _ (norm_nonneg _)
    (parameterDiscTest_U_jet_error z hu hreg hp4 T a _ k _ (norm_nonneg _)
      (integralDiscTestPolynomial_jet_error T a m k c hT)) n
  simpa only [sub_comp,mul_comp,C_comp] using! h

theorem parameterDiscTest_V_substituted_jet_error (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (m k : ℕ) (c : ℤ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^m)*X^k*(C c+C (p:ℤ)*E)) (n : ℕ) :
    ‖((parameterFourPoleV z hu hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta)) - C ((p:ℤ_[p])^m*(c:ℤ_[p]))*
      (parameterFourPoleV z hu hreg hp4 (primeDiscMonomialRegular hp4 a k) (primeDiscMonomialResidue hp4 a k)).comp
        (C ((p:ℤ_[p])^2)*(X-C eta))).coeff n‖ ≤ ‖(p:ℤ_[p])^(m+1)‖ := by
  have h := integralPolynomial_comp_coeff_bound _ (C ((p:ℤ_[p])^2)*(X-C eta)) _ (norm_nonneg _)
    (parameterDiscTest_V_jet_error z hu hreg hp4 T a _ k _ (norm_nonneg _)
      (integralDiscTestPolynomial_jet_error T a m k c hT)) n
  simpa only [sub_comp,mul_comp,C_comp] using! h

theorem parameterDiscTest_scaled_jet_error (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (m k : ℕ) (c : ℤ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^m)*X^k*(C c+C (p:ℤ)*E)) (n : ℕ) :
    ‖(parameterDiscTestScaled z hu hreg hp4 a T eta - C ((p:ℤ_[p])^m*(c:ℤ_[p]))*
      parameterDiscMonomialScaled z hu hreg hp4 a k eta).coeff n‖ ≤ ‖(p:ℤ_[p])^(m+1)‖ := by
  exact integralPolynomial_UV_difference_bound _ _ _ _ _ _ _
    (parameterDiscTest_U_substituted_jet_error z hu hreg hp4 T a m k c eta hT)
    (parameterDiscTest_V_substituted_jet_error z hu hreg hp4 T a m k c eta hT) n

theorem parameterDiscTest_zero_U_leading (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (T : ℤ[X])
    (m : ℕ) (k : Fin 5) (c : ℤ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p ⟨0,by omega⟩) =
      C ((p:ℤ)^m)*X^k.val*(C c+C (p:ℤ)*E)) (n : ℕ) :
    let a : Fin p := ⟨0,by omega⟩
    ‖(((parameterFourPoleU (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta))).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((((p:ℤ_[p])^m*(c:ℤ_[p]):ℤ_[p]):ℚ_[p])*
        ((primeDiscUnitConstant (p := p) 0 (by omega):ℚ_[p])*
          ((zeroShapeUValue lam k:ℚ):ℚ_[p])))).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(m+1) := by
  dsimp only
  apply integralPolynomial_scaled_rational_leading _
    ((parameterFourPoleU (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 (primeDiscMonomialRegular hp4 ⟨0,by omega⟩ k.val)
      (primeDiscMonomialResidue hp4 ⟨0,by omega⟩ k.val)).comp (C ((p:ℤ_[p])^2)*(X-C eta)))
  · exact parameterDiscTest_U_substituted_jet_error (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 T ⟨0,by omega⟩ m k.val c eta hT
  · exact parameterDiscMonomial_zero_U_leading lam hu hone hferm hp4 k eta

theorem parameterDiscTest_high_scaled_leading (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (T : ℤ[X]) (a : Fin p)
    (ha : p-4 < a.val) (m : ℕ) (k : Fin 3) (c : ℤ) (eta : ℤ_[p])
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^m)*X^k.val*(C c+C (p:ℤ)*E)) (n : ℕ) :
    ‖((parameterDiscTestScaled (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 a T eta).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((((p:ℤ_[p])^m*(c:ℤ_[p]):ℤ_[p]):ℚ_[p])*
        (-(a.val:ℚ_[p])*((primeDiscUnitConstant a.val a.isLt:ℚ_[p])*
          ((highShapeVValue lam k:ℚ):ℚ_[p]))))).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(m+1) := by
  apply integralPolynomial_scaled_rational_leading _ (parameterDiscMonomialScaled (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 a k.val eta)
  · exact parameterDiscTest_scaled_jet_error (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 T a m k.val c eta hT
  · intro l
    simpa only [parameterDiscMonomialScaled,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
      PadicInt.algebraMap_apply,PadicInt.coe_natCast] using!
      parameterDiscMonomial_high_scaled_leading lam hu hone hferm hp4 a ha k eta l

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterDiscTest_zero_U_leading
#print axioms Li2Unified.Proofs.PrimeEdge.parameterDiscTest_high_scaled_leading

end

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterAugmented_zero_U_leading (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p)
    (i j : Fin (primeMultiplicity p ⟨0,by omega⟩+1)) (eta : ℤ_[p]) (n : ℕ) :
    let a : Fin p := ⟨0,by omega⟩
    let T := primeAugmentedJet p a i*primeAugmentedJet p a j
    let k : Fin 5 := ⟨i.val+j.val,primeAugmented_zero_pair_lt_five hp4 i j⟩
    ‖(((parameterFourPoleU (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
      (C ((p:ℤ_[p])^2)*(X-C eta))).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((((p:ℤ_[p])^(i.val+j.val)*((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p]):ℤ_[p]):ℚ_[p])*
        ((primeDiscUnitConstant (p := p) 0 (by omega):ℚ_[p])*
          ((zeroShapeUValue lam k:ℚ):ℚ_[p])))).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  exact parameterDiscTest_zero_U_leading lam hu hone hferm hp4 _ (i.val+j.val)
    ⟨i.val+j.val,primeAugmented_zero_pair_lt_five hp4 i j⟩ _ eta
    (primeAugmentedJet_product_expansion p ⟨0,by omega⟩ i j) n

theorem parameterAugmented_high_scaled_leading (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (a : Fin p)
    (ha : p-4 < a.val) (i j : Fin (primeMultiplicity p a+1)) (eta : ℤ_[p]) (n : ℕ) :
    let T := primeAugmentedJet p a i*primeAugmentedJet p a j
    let k : Fin 3 := ⟨i.val+j.val,primeAugmented_high_pair_lt_three hp4 a ha i j⟩
    ‖((parameterDiscTestScaled (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 a T eta).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((((p:ℤ_[p])^(i.val+j.val)*((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p]):ℤ_[p]):ℚ_[p])*
        (-(a.val:ℚ_[p])*((primeDiscUnitConstant a.val a.isLt:ℚ_[p])*
          ((highShapeVValue lam k:ℚ):ℚ_[p]))))).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  exact parameterDiscTest_high_scaled_leading lam hu hone hferm hp4 _ a ha (i.val+j.val)
    ⟨i.val+j.val,primeAugmented_high_pair_lt_three hp4 a ha i j⟩ _ eta
    (primeAugmentedJet_product_expansion p a i j) n

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterAugmented_zero_U_leading
#print axioms Li2Unified.Proofs.PrimeEdge.parameterAugmented_high_scaled_leading

end

section
open Polynomial Li2 Li2Unified.LambdaLift
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma parameterDiscContribution_cube_zero (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (T : ℤ[X]) :
    let a : Fin p := ⟨0,by omega⟩
    C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu hreg hp4 a T =
      (((parameterFourPoleU (lam^p) (parameter_power_unit lam hu) hreg hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
        (C ((p:ℤ_[p])^2)*(X-C (parameterIntegralEta lam hu hreg)))).map
          (algebraMap ℤ_[p] ℚ_[p])) := by
  dsimp only
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  simp only [parameterDiscContribution,parameterDiscTestFieldUV,primeDiscScale,Fin.val_mk,ite_true,
    Nat.cast_zero,zero_div,C_0,zero_mul,sub_zero,Polynomial.map_comp,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_sub,Polynomial.map_X,PadicInt.algebraMap_apply,
    PadicInt.coe_pow,PadicInt.coe_natCast,← mul_assoc,← C_mul]
  rw [mul_inv_cancel₀ (pow_ne_zero 3 hp0),C_1,one_mul]

theorem parameterZero_original_entry_leading (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p)
    (i j : Fin (primeMultiplicity p ⟨0,by omega⟩+1)) (hij : i.val+j.val < 4) (n : ℕ) :
    let a : Fin p := ⟨0,by omega⟩
    let T := primeAugmentedJet p a i*primeAugmentedJet p a j
    let k : Fin 5 := ⟨i.val+j.val,primeAugmented_zero_pair_lt_five hp4 i j⟩
    ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])-
      C ((((p:ℤ_[p])^(i.val+j.val)*((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p]):ℤ_[p]):ℚ_[p])*
        ((primeDiscUnitConstant (p := p) 0 (by omega):ℚ_[p])*
          ((zeroShapeUValue lam k:ℚ):ℚ_[p])))).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  let a : Fin p := ⟨0,by omega⟩
  let T := primeAugmentedJet p a i*primeAugmentedJet p a j
  have hn : ‖(p:ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (p:ℤ_[p])
  have he : C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p]) =
      ∑ b : Fin p, C ((lam:ℚ_[p])⁻¹^b.val)*(C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 b T) := by
    rw [parameterNumerator_global_dissection lam hlam hu (parameterPowerRatio_integral lam hu hone hferm) hp4
      (Ne.symm (sub_ne_zero.mp (one_sub_parameter_power_unit lam hone hferm).1)),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  change ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])-C _).coeff n‖ ≤ _
  rw [he]
  apply fieldPolynomial_sum_leading_bound _ a _ _ (by positivity)
  · intro l
    simp only [a,Fin.val_mk,pow_zero,C_1,one_mul,parameterDiscContribution_cube_zero]
    exact parameterAugmented_zero_U_leading lam hu hone hferm hp4 i j (parameterIntegralEta lam hu (parameterPowerRatio_integral lam hu hone hferm)) l
  · intro b hb l
    have h := fieldPolynomial_integral_weight_bound
      (C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 b T) (integralParameterInvPow lam hu.1 hu.2 b.val) _
      (parameterAugmented_other_contribution_cube_bound lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a i j b hb) l
    have hw : ‖(C ((lam:ℚ_[p])⁻¹^b.val)*(C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 b T)).coeff l‖ ≤
        ‖(p:ℚ_[p])‖^4 := by
      simpa only [integralParameterInvPow,integralRational,Rat.cast_pow,Rat.cast_inv,PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast] using! h
    exact hw.trans (pow_le_pow_of_le_one (norm_nonneg _) hn (by omega))

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterZero_original_entry_leading

end

section
open Polynomial Li2 Li2Unified.LambdaLift
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma parameterDiscContribution_linear_high (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (a : Fin p)
    (ha : p-4 < a.val) (T : ℤ[X]) :
    C (p:ℚ_[p])*parameterDiscContribution lam hu hreg hp4 a T =
      (parameterDiscTestScaled (lam^p) (parameter_power_unit lam hu) hreg hp4 a T (parameterIntegralEta lam hu hreg)).map
        (algebraMap ℤ_[p] ℚ_[p]) := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  simp only [parameterDiscContribution,primeDiscScale,if_neg (by omega : a.val ≠ 0),
    if_neg (by omega : ¬ a.val ≤ p-4),inv_one,C_1,one_mul]
  rw [parameterDiscTestFieldUV_eq_div_scaled,← mul_assoc,← C_mul,mul_inv_cancel₀ hp0,C_1,one_mul]

theorem parameterAugmented_other_contribution_linear_bound (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a+1)) (b : Fin p) (hb : b ≠ a) (n : ℕ) :
    ‖(C (p:ℚ_[p])*parameterDiscContribution lam hu hreg hp4 b
      (primeAugmentedJet p a i*primeAugmentedJet p a j)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^2 := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have he : (C (p:ℚ_[p]) : (ℚ_[p])[X]) = C ((p:ℚ_[p])⁻¹)*C ((p:ℚ_[p])^2) := by
    rw [← C_mul]
    congr 1
    field_simp
  rw [he,mul_assoc]
  exact fieldPolynomial_div_prime_bound _ 2 (parameterAugmented_other_contribution_scaled_bound lam hu hreg hp4 a i j b hb) n

theorem parameterHigh_original_entry_leading (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (a : Fin p)
    (ha : p-4 < a.val) (i j : Fin (primeMultiplicity p a+1)) (hij : i.val+j.val < 2) (n : ℕ) :
    let T := primeAugmentedJet p a i*primeAugmentedJet p a j
    let k : Fin 3 := ⟨i.val+j.val,primeAugmented_high_pair_lt_three hp4 a ha i j⟩
    let c : ℚ_[p] := (((p:ℤ_[p])^(i.val+j.val)*
      ((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p]):ℤ_[p]):ℚ_[p])*
        (-(a.val:ℚ_[p])*((primeDiscUnitConstant a.val a.isLt:ℚ_[p])*
          ((highShapeVValue lam k:ℚ):ℚ_[p])))
    ‖(C (p:ℚ_[p])*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])-C ((lam:ℚ_[p])⁻¹^a.val*c)).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  let T := primeAugmentedJet p a i*primeAugmentedJet p a j
  have hn : ‖(p:ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (p:ℤ_[p])
  have he : C (p:ℚ_[p])*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p]) =
      ∑ b : Fin p, C ((lam:ℚ_[p])⁻¹^b.val)*(C (p:ℚ_[p])*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 b T) := by
    rw [parameterNumerator_global_dissection lam hlam hu (parameterPowerRatio_integral lam hu hone hferm) hp4
      (Ne.symm (sub_ne_zero.mp (one_sub_parameter_power_unit lam hone hferm).1)),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  change ‖(C (p:ℚ_[p])*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])-C _).coeff n‖ ≤ _
  rw [he]
  apply fieldPolynomial_sum_leading_bound _ a _ _ (by positivity)
  · intro l
    rw [parameterDiscContribution_linear_high lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a ha T]
    have h := fieldPolynomial_integral_weight_leading
      ((parameterDiscTestScaled (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 a T (parameterIntegralEta lam hu (parameterPowerRatio_integral lam hu hone hferm))).map
        (algebraMap ℤ_[p] ℚ_[p])) (integralParameterInvPow lam hu.1 hu.2 a.val) _ _
      (parameterAugmented_high_scaled_leading lam hu hone hferm hp4 a ha i j
        (parameterIntegralEta lam hu (parameterPowerRatio_integral lam hu hone hferm))) l
    simpa only [integralParameterInvPow,integralRational,Rat.cast_pow,Rat.cast_inv,PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast] using! h
  · intro b hb l
    have h := fieldPolynomial_integral_weight_bound
      (C (p:ℚ_[p])*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 b T) (integralParameterInvPow lam hu.1 hu.2 b.val) _
      (parameterAugmented_other_contribution_linear_bound lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a i j b hb) l
    have hw : ‖(C ((lam:ℚ_[p])⁻¹^b.val)*(C (p:ℚ_[p])*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 b T)).coeff l‖ ≤
        ‖(p:ℚ_[p])‖^2 := by
      simpa only [integralParameterInvPow,integralRational,Rat.cast_pow,Rat.cast_inv,PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast] using! h
    exact hw.trans (pow_le_pow_of_le_one (norm_nonneg _) hn (by omega))

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterHigh_original_entry_leading

end


end
