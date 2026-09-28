module
public import Li2Unified.Modular.Base.PrimeAugmentedJets
public import Li2Unified.Modular.Base.PrimeLowEntry

set_option backward.privateInPublic true

@[expose] public section

/-! Other-disc estimates also include the original appended product. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem primeAugmentedJet_other_factor (a : Fin p) (i : Fin (primeMultiplicity p a+1))
    (b : Fin p) (hb : b ≠ a) :
    ∃ A : ℤ[X], (primeAugmentedJet p a i).comp (primeDiscSubstitution p b) =
      C ((p:ℤ)^(primeMultiplicity p b))*X^(primeMultiplicity p b)*A := by
  by_cases hi : i.val < primeMultiplicity p a
  · rw [primeAugmentedJet_of_lt p a i hi]
    exact primeJetPoly_other_expansion p ⟨a,⟨i.val,hi⟩⟩ b hb
  · rw [primeAugmentedJet,dif_neg hi]
    obtain ⟨A,hA⟩ := primeProduct_expansion p b
    exact ⟨C (primeLocalUnit p b)+C (p:ℤ)*A,hA⟩

theorem primeAugmentedJet_other_product_factor (a : Fin p)
    (i j : Fin (primeMultiplicity p a+1)) (b : Fin p) (hb : b ≠ a) :
    ∃ E : ℤ[X], (primeAugmentedJet p a i*primeAugmentedJet p a j).comp
      (primeDiscSubstitution p b) = C ((p:ℤ)^(2*primeMultiplicity p b))*E := by
  obtain ⟨A,hA⟩ := primeAugmentedJet_other_factor a i b hb
  obtain ⟨B,hB⟩ := primeAugmentedJet_other_factor a j b hb
  refine ⟨X^(2*primeMultiplicity p b)*(A*B),?_⟩
  rw [mul_comp,hA,hB]
  simp only [two_mul,pow_add,C_mul]
  ring

theorem primeDiscContribution_scaled_factor_bound (hp4 : 3 < p) (T : ℤ[X]) (b : Fin p)
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p b) =
      C ((p:ℤ)^(2*primeMultiplicity p b))*E) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^2)*primeDiscContribution hp4 b T).coeff n‖ ≤ ‖(p:ℚ_[p])‖^3 := by
  have hn : ‖(p:ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (p:ℤ_[p])
  by_cases hz : b.val = 0
  · have hm : primeMultiplicity p b = 2 := primeMultiplicity_low hp4 b (by omega)
    have ht : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p b) = C ((p:ℤ)^4)*E := by
      simpa only [hm] using hT
    rw [primeDiscContribution_scaled_zero hp4 b hz T]
    apply fieldPolynomial_div_prime_bound _ 3
    intro k
    simpa only [coeff_map,norm_pow] using primeDiscTest_U_substituted_factor_bound hp4 T b 4
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
        simpa only [coeff_map,norm_pow] using h
      exact hc.trans (pow_le_pow_of_le_one (norm_nonneg _) hn (by omega))
    · have hm : primeMultiplicity p b = 1 := by unfold primeMultiplicity; rw [if_neg (by omega)]
      have ht : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p b) = C ((p:ℤ)^2)*E := by
        simpa only [hm] using hT
      rw [primeDiscContribution_scaled_high hp4 b (by omega) T,coeff_C_mul,norm_mul]
      have h := primeDiscTestScaled_factor_bound hp4 T b 2
        (primeEta (p := p) (by omega) (by omega)) ht n
      have hc : ‖((primeDiscTestScaled hp4 b T (primeEta (p := p) (by omega) (by omega))).map
          (algebraMap ℤ_[p] ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^2 := by
        simpa only [coeff_map,norm_pow] using h
      calc
        _ ≤ ‖(p:ℚ_[p])‖*‖(p:ℚ_[p])‖^2 := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
        _ = _ := by ring

theorem primeAugmented_other_contribution_scaled_bound (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a+1)) (b : Fin p) (hb : b ≠ a) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^2)*primeDiscContribution hp4 b
      (primeAugmentedJet p a i*primeAugmentedJet p a j)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^3 :=
  primeDiscContribution_scaled_factor_bound hp4 _ b (primeAugmentedJet_other_product_factor a i j b hb) n

theorem primeAugmented_other_contribution_cube_bound (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a+1)) (b : Fin p) (hb : b ≠ a) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*primeDiscContribution hp4 b
      (primeAugmentedJet p a i*primeAugmentedJet p a j)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^4 := by
  have he : (C ((p:ℚ_[p])^3) : (ℚ_[p])[X]) = C (p:ℚ_[p])*C ((p:ℚ_[p])^2) := by rw [← C_mul]; congr 1; ring
  rw [he,mul_assoc,coeff_C_mul,norm_mul]
  calc
    _ ≤ ‖(p:ℚ_[p])‖*‖(p:ℚ_[p])‖^3 := mul_le_mul_of_nonneg_left
      (primeAugmented_other_contribution_scaled_bound hp4 a i j b hb n) (norm_nonneg _)
    _ = _ := by ring

end
end Li2

end
