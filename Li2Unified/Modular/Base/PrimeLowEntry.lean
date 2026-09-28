module
public import Li2Unified.Modular.Base.PrimeOtherContribution

set_option backward.privateInPublic true

@[expose] public section

/-! The leading value of the full original low-class matrix entry, including
all discs, in the exact p^2 scale. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem fieldPolynomial_sum_leading_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → (ℚ_[p])[X]) (a : ι) (c : ℚ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ n, ‖(F a-C c).coeff n‖ ≤ B)
    (ho : ∀ b, b ≠ a → ∀ n, ‖(F b).coeff n‖ ≤ B) (n : ℕ) :
    ‖((∑ b, F b)-C c).coeff n‖ ≤ B := by
  have he : (∑ b, F b)-C c = (F a-C c)+∑ b ∈ Finset.univ.erase a, F b := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
    ring
  rw [he,coeff_add]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le (ha n)
  rw [finset_sum_coeff]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB
  intro b hb
  exact ho b (Finset.mem_erase.mp hb).1 n

lemma fieldPolynomial_integral_weight_bound (F : (ℚ_[p])[X]) (c : ℤ_[p])
    (B : ℝ) (hF : ∀ n, ‖F.coeff n‖ ≤ B) (n : ℕ) :
    ‖(C (c:ℚ_[p])*F).coeff n‖ ≤ B := by
  rw [coeff_C_mul,norm_mul]
  calc
    _ ≤ 1*‖F.coeff n‖ := mul_le_mul_of_nonneg_right (PadicInt.norm_le_one c) (norm_nonneg _)
    _ ≤ B := by simpa only [one_mul] using hF n

lemma fieldPolynomial_integral_weight_leading (F : (ℚ_[p])[X]) (c : ℤ_[p])
    (r : ℚ_[p]) (B : ℝ) (hF : ∀ n, ‖(F-C r).coeff n‖ ≤ B) (n : ℕ) :
    ‖(C (c:ℚ_[p])*F-C ((c:ℚ_[p])*r)).coeff n‖ ≤ B := by
  rw [C_mul,← mul_sub]
  exact fieldPolynomial_integral_weight_bound _ c B hF n

theorem primeLow_original_entry_leading (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (i j : Fin (primeMultiplicity p a)) (n : ℕ) :
    let T := primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩
    let k : Fin 3 := ⟨i.val+j.val,primeLow_pair_lt_three hp4 a ha i j⟩
    let c : ℚ_[p] := (p:ℚ_[p])^(i.val+j.val)*
      ((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℚ_[p])*
      (-(a.val:ℚ_[p])*((primeDiscUnitConstant a.val a.isLt:ℚ_[p])*
        ((![95/4,-253/4,2093/12] k:ℚ):ℚ_[p])))
    ‖(C ((p:ℚ_[p])^2)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])-C ((-2:ℚ_[p])^a.val*c)).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  let T := primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩
  have hm : i.val+j.val+1 ≤ 3 := by have h := primeLow_pair_lt_three hp4 a ha i j; omega
  have hn : ‖(p:ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (p:ℤ_[p])
  have he : C ((p:ℚ_[p])^2)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p]) =
      ∑ b : Fin p, C ((-2:ℚ_[p])^b.val)*(C ((p:ℚ_[p])^2)*primeDiscContribution hp4 b T) := by
    rw [primeNumerator_global_dissection hp4,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  change ‖(C ((p:ℚ_[p])^2)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])-C _).coeff n‖ ≤ _
  rw [he]
  apply fieldPolynomial_sum_leading_bound _ a _ _ (by positivity)
  · intro l
    rw [primeDiscContribution_scaled_low hp4 a ha0 ha T]
    have h := fieldPolynomial_integral_weight_leading
      ((primeDiscTestScaled hp4 a T (primeEta (p := p) (by omega) (by omega))).map
        (algebraMap ℤ_[p] ℚ_[p])) ((-2:ℤ_[p])^a.val) _ _
      (primeJet_actual_low_scaled_leading hp4 a ha0 ha i j
        (primeEta (p := p) (by omega) (by omega))) l
    simpa only [PadicInt.coe_pow,PadicInt.coe_mul,PadicInt.coe_natCast,PadicInt.coe_intCast,
      PadicInt.coe_neg,PadicInt.coe_natCast] using h
  · intro b hb l
    have h := fieldPolynomial_integral_weight_bound
      (C ((p:ℚ_[p])^2)*primeDiscContribution hp4 b T) ((-2:ℤ_[p])^b.val) _
      (primeJet_other_contribution_scaled_bound hp4 a i j b hb) l
    have hw : ‖(C ((-2:ℚ_[p])^b.val)*(C ((p:ℚ_[p])^2)*primeDiscContribution hp4 b T)).coeff l‖ ≤
        ‖(p:ℚ_[p])‖^3 := by
      simpa only [PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast] using h
    exact hw.trans (pow_le_pow_of_le_one (norm_nonneg _) hn hm)

end
end Li2

end
