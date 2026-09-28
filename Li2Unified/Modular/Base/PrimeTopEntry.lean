module
public import Li2Unified.Modular.Base.PrimeTopLocal

set_option backward.privateInPublic true

@[expose] public section

/-! The complete original highest-degree self-pairing, retaining every leading disc. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem fieldPolynomial_sum_all_leading_bound {ι : Type*} [Fintype ι]
    (F : ι → (ℚ_[p])[X]) (c : ι → ℚ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ a n, ‖(F a-C (c a)).coeff n‖ ≤ B) (n : ℕ) :
    ‖((∑ a,F a)-C (∑ a,c a)).coeff n‖ ≤ B := by
  have he : (∑ a,F a)-C (∑ a,c a) = ∑ a,(F a-C (c a)) := by
    simp only [Finset.sum_sub_distrib,map_sum]
  rw [he,finset_sum_coeff]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB
  intro a _
  exact hF a n

def primeTopLeadingSum : ℚ_[p] := ∑ a : Fin p, (-2:ℚ_[p])^a.val*primeTopDiscLeading a

theorem primeTop_original_entry_leading (hp4 : 3 < p) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*
        (primeProduct p*primeProduct p).map (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p]) -
      C ((p:ℚ_[p])^4*primeTopLeadingSum (p := p))).coeff n‖ ≤ ‖(p:ℚ_[p])‖^5 := by
  have he : C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*
        (primeProduct p*primeProduct p).map (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p]) =
      ∑ a : Fin p, C ((-2:ℚ_[p])^a.val)*
        (C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a (primeProduct p*primeProduct p)) := by
    rw [primeNumerator_global_dissection hp4,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hc : (p:ℚ_[p])^4*primeTopLeadingSum (p := p) =
      ∑ a : Fin p,(-2:ℚ_[p])^a.val*((p:ℚ_[p])^4*primeTopDiscLeading a) := by
    rw [primeTopLeadingSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he,hc]
  apply fieldPolynomial_sum_all_leading_bound _ _ _ (by positivity)
  intro a l
  have h := fieldPolynomial_integral_weight_leading
    (C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a (primeProduct p*primeProduct p))
    ((-2:ℤ_[p])^a.val) _ _ (primeTop_disc_leading hp4 a) l
  simpa only [PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast] using! h

end
end Li2

end
