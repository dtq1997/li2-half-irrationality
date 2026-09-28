module
public import Li2Unified.Modular.Base.PrimeZeroEntry

set_option backward.privateInPublic true

@[expose] public section

/-! Full original high-class entries and their coupling to the original
highest-degree vector. The top-top entry is treated separately. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeDiscContribution_linear_high (hp4 : 3 < p) (a : Fin p)
    (ha : p-4 < a.val) (T : ℤ[X]) :
    C (p:ℚ_[p])*primeDiscContribution hp4 a T =
      (primeDiscTestScaled hp4 a T (primeEta (p := p) (by omega) (by omega))).map
        (algebraMap ℤ_[p] ℚ_[p]) := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  simp only [primeDiscContribution,primeDiscScale,if_neg (by omega : a.val ≠ 0),
    if_neg (by omega : ¬ a.val ≤ p-4),inv_one,C_1,one_mul]
  rw [primeDiscTestFieldUV_eq_div_scaled,← mul_assoc,← C_mul,mul_inv_cancel₀ hp0,C_1,one_mul]

theorem primeAugmented_other_contribution_linear_bound (hp4 : 3 < p) (a : Fin p)
    (i j : Fin (primeMultiplicity p a+1)) (b : Fin p) (hb : b ≠ a) (n : ℕ) :
    ‖(C (p:ℚ_[p])*primeDiscContribution hp4 b
      (primeAugmentedJet p a i*primeAugmentedJet p a j)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^2 := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have he : (C (p:ℚ_[p]) : (ℚ_[p])[X]) = C ((p:ℚ_[p])⁻¹)*C ((p:ℚ_[p])^2) := by
    rw [← C_mul]
    congr 1
    field_simp
  rw [he,mul_assoc]
  exact fieldPolynomial_div_prime_bound _ 2 (primeAugmented_other_contribution_scaled_bound hp4 a i j b hb) n

theorem primeHigh_original_entry_leading (hp4 : 3 < p) (a : Fin p)
    (ha : p-4 < a.val) (i j : Fin (primeMultiplicity p a+1)) (hij : i.val+j.val < 2) (n : ℕ) :
    let T := primeAugmentedJet p a i*primeAugmentedJet p a j
    let k : Fin 3 := ⟨i.val+j.val,primeAugmented_high_pair_lt_three hp4 a ha i j⟩
    let c : ℚ_[p] := (((p:ℤ_[p])^(i.val+j.val)*
      ((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p]):ℤ_[p]):ℚ_[p])*
        (-(a.val:ℚ_[p])*((primeDiscUnitConstant a.val a.isLt:ℚ_[p])*
          ((![8,-46/3,266/9] k:ℚ):ℚ_[p])))
    ‖(C (p:ℚ_[p])*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])-C ((-2:ℚ_[p])^a.val*c)).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  let T := primeAugmentedJet p a i*primeAugmentedJet p a j
  have hn : ‖(p:ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (p:ℤ_[p])
  have he : C (p:ℚ_[p])*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p]) =
      ∑ b : Fin p, C ((-2:ℚ_[p])^b.val)*(C (p:ℚ_[p])*primeDiscContribution hp4 b T) := by
    rw [primeNumerator_global_dissection hp4,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  change ‖(C (p:ℚ_[p])*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])-C _).coeff n‖ ≤ _
  rw [he]
  apply fieldPolynomial_sum_leading_bound _ a _ _ (by positivity)
  · intro l
    rw [primeDiscContribution_linear_high hp4 a ha T]
    have h := fieldPolynomial_integral_weight_leading
      ((primeDiscTestScaled hp4 a T (primeEta (p := p) (by omega) (by omega))).map
        (algebraMap ℤ_[p] ℚ_[p])) ((-2:ℤ_[p])^a.val) _ _
      (primeAugmented_high_scaled_leading hp4 a ha i j
        (primeEta (p := p) (by omega) (by omega))) l
    simpa only [PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast] using! h
  · intro b hb l
    have h := fieldPolynomial_integral_weight_bound
      (C (p:ℚ_[p])*primeDiscContribution hp4 b T) ((-2:ℤ_[p])^b.val) _
      (primeAugmented_other_contribution_linear_bound hp4 a i j b hb) l
    have hw : ‖(C ((-2:ℚ_[p])^b.val)*(C (p:ℚ_[p])*primeDiscContribution hp4 b T)).coeff l‖ ≤
        ‖(p:ℚ_[p])‖^2 := by
      simpa only [PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast] using! h
    exact hw.trans (pow_le_pow_of_le_one (norm_nonneg _) hn (by omega))

end
end Li2

end
