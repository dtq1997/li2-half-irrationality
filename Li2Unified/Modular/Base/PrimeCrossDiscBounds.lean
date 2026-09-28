module
public import Li2Unified.Modular.Base.PrimeTopLocal
public import Li2Unified.Modular.Base.PrimeIntegralJetBounds

set_option backward.privateInPublic true

@[expose] public section

/-! Cube-scaled bounds for the literal integer tests and original discs. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def primeDiscCubeGain (a : Fin p) : ℕ :=
  if a.val = 0 then 0 else if a.val ≤ p-4 then 1 else 2

theorem primeDiscContribution_cube_factor_bound (hp4 : 3 < p)
    (T : ℤ[X]) (a : Fin p) (m : ℕ)
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) = C ((p:ℤ)^m)*E)
    (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a T).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(m+primeDiscCubeGain a) := by
  by_cases hz : a.val = 0
  · have he : a = (⟨0,by omega⟩ : Fin p) := Fin.ext hz
    rw [he] at hT ⊢
    rw [primeDiscContribution_cube_zero]
    simpa only [primeDiscCubeGain, Fin.val_mk, ite_true, Nat.add_zero, coeff_map, norm_pow] using
      primeDiscTest_U_substituted_factor_bound hp4 T (⟨0,by omega⟩ : Fin p) m
        (primeEta (p := p) (by omega) (by omega)) hT n
  · by_cases hl : a.val ≤ p-4
    · have h : ∀ l, ‖((primeDiscTestScaled hp4 a T
          (primeEta (p := p) (by omega) (by omega))).map
          (algebraMap ℤ_[p] ℚ_[p])).coeff l‖ ≤ ‖(p:ℚ_[p])‖^m := by
        intro l
        simpa only [coeff_map,norm_pow] using primeDiscTestScaled_factor_bound hp4 T a m
          (primeEta (p := p) (by omega) (by omega)) hT l
      have he : C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a T =
          C ((p:ℚ_[p])^1)*(C ((p:ℚ_[p])^2)*primeDiscContribution hp4 a T) := by
        simp only [C_pow]
        ring
      rw [he,primeDiscContribution_scaled_low hp4 a (by omega) hl,
        primeDiscCubeGain,if_neg hz,if_pos hl]
      simpa only [Nat.add_comm] using fieldPolynomial_prime_power_bound _ 1 m h n
    · have h : ∀ l, ‖((primeDiscTestScaled hp4 a T
          (primeEta (p := p) (by omega) (by omega))).map
          (algebraMap ℤ_[p] ℚ_[p])).coeff l‖ ≤ ‖(p:ℚ_[p])‖^m := by
        intro l
        simpa only [coeff_map,norm_pow] using primeDiscTestScaled_factor_bound hp4 T a m
          (primeEta (p := p) (by omega) (by omega)) hT l
      have he : C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a T =
          C ((p:ℚ_[p])^2)*(C (p:ℚ_[p])*primeDiscContribution hp4 a T) := by
        simp only [C_pow]
        ring
      rw [he,primeDiscContribution_linear_high hp4 a (by omega),
        primeDiscCubeGain,if_neg hz,if_neg hl]
      simpa only [Nat.add_comm] using fieldPolynomial_prime_power_bound _ 2 m h n

theorem primeOriginalBasisProduct_cube_disc_bound (hp4 : 3 < p)
    (i j : Fin (2*(p-1))) (a : Fin p) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a
      (primeOriginalBasis p (by omega) i*primeOriginalBasis p (by omega) j)).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(primeOriginalBasisLocalOrder p (by omega) i a+
        primeOriginalBasisLocalOrder p (by omega) j a+primeDiscCubeGain a) := by
  obtain ⟨A,hA⟩ := primeOriginalBasisProduct_disc_factor p (by omega) i j a
  apply primeDiscContribution_cube_factor_bound hp4
  exact ⟨X^(primeOriginalBasisLocalOrder p (by omega) i a+
    primeOriginalBasisLocalOrder p (by omega) j a)*A,by rw [hA,mul_assoc]⟩

theorem primeNumerator_cube_bound_of_disc_bounds (hp4 : 3 < p)
    (T : ℤ[X]) (k : ℕ)
    (hdisc : ∀ a : Fin p, ∀ n,
      ‖(C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a T).coeff n‖ ≤ ‖(p:ℚ_[p])‖^k)
    (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^k := by
  have he : C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p]) =
      ∑ a : Fin p, C ((-2:ℚ_[p])^a.val)*(C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a T) := by
    rw [primeNumerator_global_dissection hp4,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he,finset_sum_coeff]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro a _
  have h := fieldPolynomial_integral_weight_bound
    (C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a T)
    ((-2:ℤ_[p])^a.val) _ (hdisc a) n
  simpa only [PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast] using h

lemma primeJet_pair_disc_factor (a b : PrimeJet p) (c : Fin p) :
    ∃ E : ℤ[X], (primeJetPoly p a*primeJetPoly p b).comp (primeDiscSubstitution p c) =
      C ((p:ℤ)^(primeJetLocalOrder p a c+primeJetLocalOrder p b c))*E := by
  obtain ⟨A,hA⟩ := primeJet_disc_factor p a c
  obtain ⟨B,hB⟩ := primeJet_disc_factor p b c
  refine ⟨X^(primeJetLocalOrder p a c+primeJetLocalOrder p b c)*(A*B),?_⟩
  rw [mul_comp,hA,hB]
  simp only [pow_add,C_mul]
  ring

lemma primeLow_cross_cube_order (hp4 : 3 < p) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (hb0 : 0 < b.val) (hb : b.val ≤ p-4) (hab : a ≠ b)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b)) (c : Fin p) :
    i.val+j.val+2 ≤ primeJetLocalOrder p ⟨a,i⟩ c+
      primeJetLocalOrder p ⟨b,j⟩ c+primeDiscCubeGain c := by
  have hi : i.val ≤ 1 := by
    have hi := i.isLt
    have hm := primeMultiplicity_low hp4 a ha
    omega
  have hj : j.val ≤ 1 := by
    have hj := j.isLt
    have hm := primeMultiplicity_low hp4 b hb
    omega
  by_cases hca : c = a
  · subst c
    simp only [primeJetLocalOrder,ite_true,if_pos rfl,if_neg hab,
      primeMultiplicity_low hp4 a ha,primeDiscCubeGain,if_neg ha0.ne',if_pos ha]
    omega
  · by_cases hcb : c = b
    · subst c
      simp only [primeJetLocalOrder,ite_true,if_neg (Ne.symm hab),if_pos rfl,
        primeMultiplicity_low hp4 b hb,primeDiscCubeGain,if_neg hb0.ne',if_pos hb]
      omega
    · simp only [primeJetLocalOrder,ite_true,if_neg hca,if_neg hcb]
      by_cases hz : c.val = 0
      · have hm : primeMultiplicity p c = 2 := primeMultiplicity_low hp4 c (by omega)
        simp only [hm,primeDiscCubeGain,if_pos hz]
        omega
      · by_cases hl : c.val ≤ p-4
        · simp only [primeMultiplicity_low hp4 c hl,primeDiscCubeGain,if_neg hz,if_pos hl]
          omega
        · have hm : primeMultiplicity p c = 1 := by
            unfold primeMultiplicity
            rw [if_neg (by omega)]
          simp only [hm,primeDiscCubeGain,if_neg hz,if_neg hl]
          omega

/-- Distinct original low blocks: raw valuation at least i+j-1. -/
theorem primeLow_cross_original_entry_bound (hp4 : 3 < p) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (hb0 : 0 < b.val) (hb : b.val ≤ p-4) (hab : a ≠ b)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b)) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*
        (primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨b,j⟩).map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(i.val+j.val+2) := by
  apply primeNumerator_cube_bound_of_disc_bounds hp4 _ (i.val+j.val+2)
  intro c l
  have h := primeDiscContribution_cube_factor_bound hp4 _ c
    (primeJetLocalOrder p ⟨a,i⟩ c+primeJetLocalOrder p ⟨b,j⟩ c)
    (primeJet_pair_disc_factor ⟨a,i⟩ ⟨b,j⟩ c) l
  exact h.trans (pow_le_pow_of_le_one (norm_nonneg _)
    (PadicInt.norm_le_one (p:ℤ_[p]))
    (primeLow_cross_cube_order hp4 a b ha0 ha hb0 hb hab i j c))

lemma primeProduct_jet_disc_factor (a : PrimeJet p) (c : Fin p) :
    ∃ E : ℤ[X], (primeProduct p*primeJetPoly p a).comp (primeDiscSubstitution p c) =
      C ((p:ℤ)^(primeMultiplicity p c+primeJetLocalOrder p a c))*E := by
  obtain ⟨A,hA⟩ := primeProduct_expansion p c
  obtain ⟨B,hB⟩ := primeJet_disc_factor p a c
  refine ⟨X^(primeMultiplicity p c+primeJetLocalOrder p a c)*
    ((C (primeLocalUnit p c)+C (p:ℤ)*A)*B),?_⟩
  rw [mul_comp,hA,hB]
  simp only [pow_add,C_mul]
  ring

lemma primeTop_low_cube_order (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (i : Fin (primeMultiplicity p a)) (c : Fin p) :
    i.val+3 ≤ primeMultiplicity p c+primeJetLocalOrder p ⟨a,i⟩ c+primeDiscCubeGain c := by
  have hi : i.val ≤ 1 := by
    have hi := i.isLt
    have hm := primeMultiplicity_low hp4 a ha
    omega
  by_cases hca : c = a
  · subst c
    simp only [primeJetLocalOrder,ite_true,if_pos rfl,primeMultiplicity_low hp4 a ha,
      primeDiscCubeGain,if_neg ha0.ne',if_pos ha]
    omega
  · simp only [primeJetLocalOrder,ite_true,if_neg hca]
    by_cases hz : c.val = 0
    · have hm : primeMultiplicity p c = 2 := primeMultiplicity_low hp4 c (by omega)
      simp only [hm,primeDiscCubeGain,if_pos hz]
      omega
    · by_cases hl : c.val ≤ p-4
      · simp only [primeMultiplicity_low hp4 c hl,primeDiscCubeGain,if_neg hz,if_pos hl]
        omega
      · have hm : primeMultiplicity p c = 1 := by
          unfold primeMultiplicity
          rw [if_neg (by omega)]
        simp only [hm,primeDiscCubeGain,if_neg hz,if_neg hl]
        omega

theorem primeTop_low_original_entry_bound (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (i : Fin (primeMultiplicity p a)) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*
        (primeProduct p*primeJetPoly p ⟨a,i⟩).map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(i.val+3) := by
  apply primeNumerator_cube_bound_of_disc_bounds hp4 _ (i.val+3)
  intro c l
  have h := primeDiscContribution_cube_factor_bound hp4 _ c
    (primeMultiplicity p c+primeJetLocalOrder p ⟨a,i⟩ c)
    (primeProduct_jet_disc_factor ⟨a,i⟩ c) l
  exact h.trans (pow_le_pow_of_le_one (norm_nonneg _)
    (PadicInt.norm_le_one (p:ℤ_[p]))
    (primeTop_low_cube_order hp4 a ha0 ha i c))

lemma primeOriginalBasis_eq_jet_of_index (hp3 : 3 ≤ p)
    (I : Fin (2*(p-1))) (a : PrimeJet p)
    (hI : finCongr (primeBasisSize p hp3) I = ((primeJetEquiv p hp3).symm a).succ) :
    primeOriginalBasis p hp3 I = primeJetPoly p a := by
  unfold primeOriginalBasis
  rw [hI]
  simp only [primeFullBasis,Fin.cases_succ,primeIndexedPoly,Equiv.apply_symm_apply]

lemma primeOriginalBasis_zero_eq_product (hp3 : 3 ≤ p) :
    primeOriginalBasis p hp3 (⟨0,by omega⟩ : Fin (2*(p-1))) = primeProduct p := by
  have hI : finCongr (primeBasisSize p hp3) (⟨0,by omega⟩ : Fin (2*(p-1))) = 0 :=
    Fin.ext rfl
  unfold primeOriginalBasis
  rw [hI]
  simp only [primeFullBasis,Fin.cases_zero]

theorem primeOriginalBasis_low_cross_entry_bound (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (hb0 : 0 < b.val) (hb : b.val ≤ p-4) (hab : a ≠ b)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*
        (primeOriginalBasis p (by omega) I*primeOriginalBasis p (by omega) J).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p])).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+2) := by
  rw [primeOriginalBasis_eq_jet_of_index (by omega) I ⟨a,i⟩ hI,
    primeOriginalBasis_eq_jet_of_index (by omega) J ⟨b,j⟩ hJ]
  exact primeLow_cross_original_entry_bound hp4 a b ha0 ha hb0 hb hab i j n

theorem primeOriginalBasis_top_low_entry_bound (hp4 : 3 < p)
    (J : Fin (2*(p-1))) (a : Fin p) (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (i : Fin (primeMultiplicity p a))
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*
        (primeOriginalBasis p (by omega) (⟨0,by omega⟩ : Fin (2*(p-1)))*
          primeOriginalBasis p (by omega) J).map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(i.val+3) := by
  rw [primeOriginalBasis_zero_eq_product (by omega),
    primeOriginalBasis_eq_jet_of_index (by omega) J ⟨a,i⟩ hJ]
  exact primeTop_low_original_entry_bound hp4 a ha0 ha i n

end
end Li2

end
