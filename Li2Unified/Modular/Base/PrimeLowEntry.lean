module
public import Li2Unified.Modular.Base.PrimeOtherDiscBounds

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
    _ ≤ B := by simpa only [one_mul] using! hF n

lemma fieldPolynomial_integral_weight_leading (F : (ℚ_[p])[X]) (c : ℤ_[p])
    (r : ℚ_[p]) (B : ℝ) (hF : ∀ n, ‖(F-C r).coeff n‖ ≤ B) (n : ℕ) :
    ‖(C (c:ℚ_[p])*F-C ((c:ℚ_[p])*r)).coeff n‖ ≤ B := by
  rw [C_mul,← mul_sub]
  exact fieldPolynomial_integral_weight_bound _ c B hF n

end
end Li2

end
