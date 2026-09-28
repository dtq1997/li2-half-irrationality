module
public import Li2Unified.Modular.Positive.Packed.P025

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation
open Finset
open scoped BigOperators

private theorem reciprocal_square_telescope (N : ℕ) (hN : 2 ≤ N) :
    (∑ A ∈ Finset.Ico 2 (N+1), (((A:ℝ)⁻¹)^2 - ((((A:ℝ)+1)⁻¹)^2))) =
      ((2:ℝ)⁻¹)^2 - ((((N:ℝ)+1)⁻¹)^2) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hN2 : 2 ≤ N
    · rw [sum_Ico_succ_top (by omega : 2 ≤ N+1), ih hN2]
      push_cast
      ring
    · have hN1 : N = 1 := by omega
      subst N
      norm_num

/-- A fixed cutoff avoids the improper integral at zero. -/
theorem profile_cell_sum_199_lower :
    (-523/840:ℝ) + (2/3:ℝ)/(200:ℝ)^2 <
      ∑ A ∈ Finset.Ico (1:ℕ) 200, cellIntegral A := by
  have h1 : cellIntegral 1 = (-383/840:ℝ) := by
    norm_num [cellIntegral]
  have htail :
      (∑ A ∈ Finset.Ico (2:ℕ) 200,
        -(2/3:ℝ)*((((A:ℝ)⁻¹)^2)-(((((A:ℝ)+1)⁻¹)^2)))) <
      ∑ A ∈ Finset.Ico (2:ℕ) 200, cellIntegral A := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨2, by simp⟩
    · intro A hA
      have hA2 : (2:ℝ) ≤ A := by exact_mod_cast (mem_Ico.mp hA).1
      exact cell_positive_remainder (A:ℝ) hA2
  have htel := reciprocal_square_telescope 199 (by omega)
  rw [← sum_Ico_consecutive (f := fun A : ℕ => cellIntegral A)
    (by decide : 1 ≤ 2) (by decide : 2 ≤ 200)]
  have hfirst : (∑ A ∈ Finset.Ico (1:ℕ) 2, cellIntegral A) = cellIntegral 1 := by norm_num
  rw [hfirst, h1]
  have hsum :
    (∑ A ∈ Finset.Ico (2:ℕ) 200,
      -(2/3:ℝ)*((((A:ℝ)⁻¹)^2)-(((((A:ℝ)+1)⁻¹)^2)))) =
      -(2/3:ℝ)*((((2:ℝ)⁻¹)^2)-((((199:ℝ)+1)⁻¹)^2)) := by
    rw [← Finset.mul_sum, htel]
    norm_num
  rw [hsum] at htail
  norm_num at htail ⊢
  linarith

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.profile_cell_sum_199_lower

end


end
