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

end
end Li2

end
