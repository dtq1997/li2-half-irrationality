module
public import Li2Unified.Modular.Base.PrimeOtherDiscBounds

set_option backward.privateInPublic true

@[expose] public section

/-! After multiplying the original numerator by p^2, each other-disc
contribution to a same-center pair is divisible by p^3 coefficientwise. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeDiscContribution_scaled_zero (hp4 : 3 < p) (a : Fin p)
    (ha : a.val = 0) (T : ℤ[X]) :
    C ((p:ℚ_[p])^2)*primeDiscContribution hp4 a T =
      C ((p:ℚ_[p])⁻¹)*
        (((primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
          (C ((p:ℤ_[p])^2)*(X-C (primeEta (p := p) (by omega) (by omega))))).map
            (algebraMap ℤ_[p] ℚ_[p])) := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have he : (p:ℚ_[p])^2*((p:ℚ_[p])^3)⁻¹ = (p:ℚ_[p])⁻¹ := by field_simp
  simp only [primeDiscContribution,primeDiscTestFieldUV,primeDiscScale,ha,ite_true,
    Nat.cast_zero,zero_div,C_0,zero_mul,sub_zero,Polynomial.map_comp,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_sub,Polynomial.map_X,PadicInt.algebraMap_apply,
    PadicInt.coe_pow,PadicInt.coe_natCast,← mul_assoc,← C_mul,he]

lemma primeDiscContribution_scaled_low (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (T : ℤ[X]) :
    C ((p:ℚ_[p])^2)*primeDiscContribution hp4 a T =
      (primeDiscTestScaled hp4 a T (primeEta (p := p) (by omega) (by omega))).map
        (algebraMap ℤ_[p] ℚ_[p]) := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [primeDiscContribution_scaled]
  simp only [primeDiscScale,if_neg (by omega : a.val ≠ 0),if_pos ha,div_self hp0,C_1,one_mul]

lemma primeDiscContribution_scaled_high (hp4 : 3 < p) (a : Fin p)
    (ha : p-4 < a.val) (T : ℤ[X]) :
    C ((p:ℚ_[p])^2)*primeDiscContribution hp4 a T =
      C (p:ℚ_[p])*(primeDiscTestScaled hp4 a T (primeEta (p := p) (by omega) (by omega))).map
        (algebraMap ℤ_[p] ℚ_[p]) := by
  rw [primeDiscContribution_scaled]
  simp only [primeDiscScale,if_neg (by omega : a.val ≠ 0),if_neg (by omega : ¬ a.val ≤ p-4),div_one]

theorem primeJet_other_contribution_scaled_bound (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) (b : Fin p) (hb : b ≠ a) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^2)*primeDiscContribution hp4 b
      (primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^3 := by
  let T := primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩
  have hT := primeJet_same_other_product_factor a i j b hb
  have hn : ‖(p:ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (p:ℤ_[p])
  change ‖(C ((p:ℚ_[p])^2)*primeDiscContribution hp4 b T).coeff n‖ ≤ _
  by_cases hz : b.val = 0
  · have hm : primeMultiplicity p b = 2 := primeMultiplicity_low hp4 b (by omega)
    have ht : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p b) = C ((p:ℤ)^4)*E := by
      simpa only [hm] using hT
    rw [primeDiscContribution_scaled_zero hp4 b hz T]
    apply fieldPolynomial_div_prime_bound _ 3
    intro k
    simpa only [coeff_map,norm_pow] using! primeDiscTest_U_substituted_factor_bound hp4 T b 4
      (primeEta (p := p) (by omega) (by omega)) ht k
  · by_cases hl : b.val ≤ p-4
    · have hm : primeMultiplicity p b = 2 := primeMultiplicity_low hp4 b hl
      have ht : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p b) = C ((p:ℤ)^4)*E := by
        simpa only [hm] using hT
      rw [primeDiscContribution_scaled_low hp4 b (by omega) hl T]
      have h := primeDiscTestScaled_factor_bound hp4 T b 4
        (primeEta (p := p) (by omega) (by omega)) ht n
      have hc : ‖((primeDiscTestScaled hp4 b T (primeEta (p := p) (by omega) (by omega))).map
          (algebraMap ℤ_[p] ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^4 := by
        simpa only [coeff_map,norm_pow] using! h
      exact hc.trans (pow_le_pow_of_le_one (norm_nonneg _) hn (by omega))
    · have hm : primeMultiplicity p b = 1 := by
        unfold primeMultiplicity
        rw [if_neg (by omega)]
      have ht : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p b) = C ((p:ℤ)^2)*E := by
        simpa only [hm] using hT
      rw [primeDiscContribution_scaled_high hp4 b (by omega) T,coeff_C_mul,norm_mul]
      have h := primeDiscTestScaled_factor_bound hp4 T b 2
        (primeEta (p := p) (by omega) (by omega)) ht n
      have hc : ‖((primeDiscTestScaled hp4 b T (primeEta (p := p) (by omega) (by omega))).map
          (algebraMap ℤ_[p] ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^2 := by
        simpa only [coeff_map,norm_pow] using! h
      calc
        _ ≤ ‖(p:ℚ_[p])‖*‖(p:ℚ_[p])‖^2 := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
        _ = _ := by ring

end
end Li2

end
