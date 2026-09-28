module
public import Li2Unified.Modular.Positive.Packed.P028

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation
open Li2.PrimeSums Finset Filter Topology
open scoped BigOperators

private lemma window_left_pos_closed (A : ℝ) (hA : 1 ≤ A) (j : Fin 6) :
    0 < profileWindowLeft A j := by
  fin_cases j <;> norm_num [profileWindowLeft] <;> positivity

private lemma window_left_lt_right_closed (A : ℝ) (hA : 1 ≤ A) (j : Fin 6) :
    profileWindowLeft A j < profileWindowRight A j := by
  have hApos : 0 < A := by linarith
  fin_cases j <;> norm_num [profileWindowLeft, profileWindowRight]
  all_goals
    try simp only [← one_div]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith

private lemma window_mass_eq_cell_closed (A : ℝ) (hA : 1 ≤ A) :
    (∑ j : Fin 6, (
      profileWindowAlpha A j *
        (((profileWindowRight A j)^2-(profileWindowLeft A j)^2)/2) +
      profileWindowBeta A j * (profileWindowRight A j-profileWindowLeft A j))) =
      cellIntegral A := by
  rw [← profileCellAlgebraicSum_eq_cellIntegral A hA]
  unfold profileCellAlgebraicSum affinePrimitiveDifference
  simp [Fin.sum_univ_succ, profileWindowAlpha, profileWindowBeta,
    profileWindowLeft, profileWindowRight]
  ring

/-- Half-open windows include exactly the floor jump endpoints. -/
def profileWindowClosedSum (n : ℕ) : ℝ :=
  ∑ A ∈ Finset.Ico (1:ℕ) 200, ∑ j : Fin 6,
    affineSum (profileWindowAlpha A j) (profileWindowBeta A j)
      (profileWindowLeft A j) (profileWindowRight A j) (n:ℝ)

theorem profileWindowClosedSum_tendsto :
    Tendsto (fun n : ℕ => profileWindowClosedSum n/(n:ℝ)^2) atTop
      (𝓝 (∑ A ∈ Finset.Ico (1:ℕ) 200, cellIntegral A)) := by
  have hrow (A : ℕ) (hA : A ∈ Finset.Ico (1:ℕ) 200) :
      Tendsto (fun n : ℕ =>
        (∑ j : Fin 6,
          affineSum (profileWindowAlpha A j) (profileWindowBeta A j)
            (profileWindowLeft A j) (profileWindowRight A j) (n:ℝ))/(n:ℝ)^2)
        atTop (𝓝 (cellIntegral A)) := by
    have hAr : (1:ℝ) ≤ A := by exact_mod_cast (Finset.mem_Ico.mp hA).1
    have hsum := tendsto_finset_sum (Finset.univ : Finset (Fin 6))
      (fun j _ => affineSum_nat_tendsto
        (profileWindowAlpha A j) (profileWindowBeta A j)
        (window_left_pos_closed A hAr j)
        (window_left_lt_right_closed A hAr j).le)
    rw [window_mass_eq_cell_closed A hAr] at hsum
    simpa only [Finset.sum_div] using! hsum
  have houter := tendsto_finset_sum (Finset.Ico (1:ℕ) 200)
    (fun A hA => hrow A hA)
  simpa only [profileWindowClosedSum, Finset.sum_div] using! houter

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.profileWindowClosedSum_tendsto

end


end
