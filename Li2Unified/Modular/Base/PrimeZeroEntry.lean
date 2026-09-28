module
public import Li2Unified.Modular.Base.PrimeAugmentedOther

set_option backward.privateInPublic true

@[expose] public section

/-! Full original zero-class entries including their coupling to the original
highest-degree basis vector. The highest-degree self-pairing is deliberately
excluded: it also has leading contributions from the three high discs. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeDiscContribution_cube_zero (hp4 : 3 < p) (T : ℤ[X]) :
    let a : Fin p := ⟨0,by omega⟩
    C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a T =
      (((primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
        (C ((p:ℤ_[p])^2)*(X-C (primeEta (p := p) (by omega) (by omega))))).map
          (algebraMap ℤ_[p] ℚ_[p])) := by
  dsimp only
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  simp only [primeDiscContribution,primeDiscTestFieldUV,primeDiscScale,Fin.val_mk,ite_true,
    Nat.cast_zero,zero_div,C_0,zero_mul,sub_zero,Polynomial.map_comp,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_sub,Polynomial.map_X,PadicInt.algebraMap_apply,
    PadicInt.coe_pow,PadicInt.coe_natCast,← mul_assoc,← C_mul]
  rw [mul_inv_cancel₀ (pow_ne_zero 3 hp0),C_1,one_mul]

theorem primeZero_original_entry_leading (hp4 : 3 < p)
    (i j : Fin (primeMultiplicity p ⟨0,by omega⟩+1)) (hij : i.val+j.val < 4) (n : ℕ) :
    let a : Fin p := ⟨0,by omega⟩
    let T := primeAugmentedJet p a i*primeAugmentedJet p a j
    let k : Fin 5 := ⟨i.val+j.val,primeAugmented_zero_pair_lt_five hp4 i j⟩
    ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])-
      C ((((p:ℤ_[p])^(i.val+j.val)*((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p]):ℤ_[p]):ℚ_[p])*
        ((primeDiscUnitConstant (p := p) 0 (by omega):ℚ_[p])*
          ((![-113/12,95/4,-253/4,2093/12,-17773/36] k:ℚ):ℚ_[p])))).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  let a : Fin p := ⟨0,by omega⟩
  let T := primeAugmentedJet p a i*primeAugmentedJet p a j
  have hn : ‖(p:ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (p:ℤ_[p])
  have he : C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p]) =
      ∑ b : Fin p, C ((-2:ℚ_[p])^b.val)*(C ((p:ℚ_[p])^3)*primeDiscContribution hp4 b T) := by
    rw [primeNumerator_global_dissection hp4,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  change ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])-C _).coeff n‖ ≤ _
  rw [he]
  apply fieldPolynomial_sum_leading_bound _ a _ _ (by positivity)
  · intro l
    simp only [a,Fin.val_mk,pow_zero,C_1,one_mul,primeDiscContribution_cube_zero]
    exact primeAugmented_zero_U_leading hp4 i j (primeEta (p := p) (by omega) (by omega)) l
  · intro b hb l
    have h := fieldPolynomial_integral_weight_bound
      (C ((p:ℚ_[p])^3)*primeDiscContribution hp4 b T) ((-2:ℤ_[p])^b.val) _
      (primeAugmented_other_contribution_cube_bound hp4 a i j b hb) l
    have hw : ‖(C ((-2:ℚ_[p])^b.val)*(C ((p:ℚ_[p])^3)*primeDiscContribution hp4 b T)).coeff l‖ ≤
        ‖(p:ℚ_[p])‖^4 := by
      simpa only [PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast] using! h
    exact hw.trans (pow_le_pow_of_le_one (norm_nonneg _) hn (by omega))

end
end Li2

end
