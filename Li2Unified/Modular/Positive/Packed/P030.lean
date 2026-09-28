module
public import Li2Unified.Modular.Positive.Packed.P029

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation
open Li2.PrimeSums Finset Filter Topology
open scoped BigOperators

private lemma window_left_pos_N (A : ℝ) (hA : 1 ≤ A) (j : Fin 6) :
    0 < profileWindowLeft A j := by
  fin_cases j <;> norm_num [profileWindowLeft] <;> positivity

private lemma window_left_lt_right_N (A : ℝ) (hA : 1 ≤ A) (j : Fin 6) :
    profileWindowLeft A j < profileWindowRight A j := by
  have hApos : 0 < A := by linarith
  fin_cases j <;> norm_num [profileWindowLeft, profileWindowRight]
  all_goals
    try simp only [← one_div]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith

private lemma window_mass_eq_cell_N (A : ℝ) (hA : 1 ≤ A) :
    (∑ j : Fin 6, (
      profileWindowAlpha A j *
        (((profileWindowRight A j)^2-(profileWindowLeft A j)^2)/2) +
      profileWindowBeta A j *
        (profileWindowRight A j-profileWindowLeft A j))) =
      cellIntegral A := by
  rw [← profileCellAlgebraicSum_eq_cellIntegral A hA]
  unfold profileCellAlgebraicSum affinePrimitiveDifference
  simp [Fin.sum_univ_succ, profileWindowAlpha, profileWindowBeta,
    profileWindowLeft, profileWindowRight]
  ring

/-- The closed prime-window sum with an arbitrary finite reciprocal cutoff. -/
def profileWindowClosedSumN (N n : ℕ) : ℝ :=
  ∑ A ∈ Finset.Ico (1:ℕ) (N+1), ∑ j : Fin 6,
    affineSum (profileWindowAlpha A j) (profileWindowBeta A j)
      (profileWindowLeft A j) (profileWindowRight A j) (n:ℝ)

theorem profileWindowClosedSumN_tendsto (N : ℕ) :
    Tendsto (fun n : ℕ => profileWindowClosedSumN N n/(n:ℝ)^2) atTop
      (𝓝 (∑ A ∈ Finset.Ico (1:ℕ) (N+1), cellIntegral A)) := by
  have hrow (A : ℕ) (hA : A ∈ Finset.Ico (1:ℕ) (N+1)) :
      Tendsto (fun n : ℕ =>
        (∑ j : Fin 6,
          affineSum (profileWindowAlpha A j) (profileWindowBeta A j)
            (profileWindowLeft A j) (profileWindowRight A j) (n:ℝ))/(n:ℝ)^2)
        atTop (𝓝 (cellIntegral A)) := by
    have hAr : (1:ℝ) ≤ A := by exact_mod_cast (Finset.mem_Ico.mp hA).1
    have hsum := tendsto_finset_sum (Finset.univ : Finset (Fin 6))
      (fun j _ => affineSum_nat_tendsto
        (profileWindowAlpha A j) (profileWindowBeta A j)
        (window_left_pos_N A hAr j)
        (window_left_lt_right_N A hAr j).le)
    rw [window_mass_eq_cell_N A hAr] at hsum
    simpa only [Finset.sum_div] using! hsum
  have houter := tendsto_finset_sum (Finset.Ico (1:ℕ) (N+1))
    (fun A hA => hrow A hA)
  simpa only [profileWindowClosedSumN, Finset.sum_div] using! houter

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.profileWindowClosedSumN_tendsto

end


end
