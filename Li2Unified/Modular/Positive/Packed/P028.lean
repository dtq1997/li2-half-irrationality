module
public import Li2Unified.Modular.Positive.Packed.P026
public import Li2Unified.Modular.Positive.Packed.P027
public import Li2Unified.Modular.Base.PrimeMixedWindows
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation
open Li2.PrimeSums Finset Filter Topology
open scoped BigOperators

/-- Six affine coefficients of the actual profile on one reciprocal cell. -/
def profileWindowAlpha (A : ℝ) : Fin 6 → ℝ :=
  ![2*A^2+3*A, 2*A^2-A-1, 2*A^2+2*A,
    2*A^2+2*A, 2*A^2+5*A+2, 2*A^2+A-1]
def profileWindowBeta (A : ℝ) : Fin 6 → ℝ :=
  ![-2*A-5, -2*A+1, -2*A-2, -2*A, -2*A-3, -2*A+3]
def profileWindowLeft (A : ℝ) : Fin 6 → ℝ :=
  ![4/(4*A+1), 3/(3*A+1), 2/(2*A+1),
    3/(3*A+2), 4/(4*A+3), 1/(A+1)]
def profileWindowRight (A : ℝ) : Fin 6 → ℝ :=
  ![1/A, 4/(4*A+1), 3/(3*A+1),
    2/(2*A+1), 3/(3*A+2), 4/(4*A+3)]

private lemma window_left_pos (A : ℝ) (hA : 1 ≤ A) (j : Fin 6) :
    0 < profileWindowLeft A j := by
  fin_cases j <;> norm_num [profileWindowLeft] <;> positivity

private lemma window_left_lt_right (A : ℝ) (hA : 1 ≤ A) (j : Fin 6) :
    profileWindowLeft A j < profileWindowRight A j := by
  have hApos : 0 < A := by linarith
  fin_cases j <;> norm_num [profileWindowLeft, profileWindowRight]
  all_goals
    try simp only [← one_div]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith

private lemma window_mass_eq_cell (A : ℝ) (hA : 1 ≤ A) :
    (∑ j : Fin 6, (
      profileWindowAlpha A j *
        ((profileWindowRight A j)^2-(profileWindowLeft A j)^2)/2 +
      profileWindowBeta A j * (profileWindowRight A j-profileWindowLeft A j))) =
      cellIntegral A := by
  rw [← profileCellAlgebraicSum_eq_cellIntegral A hA]
  unfold profileCellAlgebraicSum affinePrimitiveDifference
  simp [Fin.sum_univ_succ, profileWindowAlpha, profileWindowBeta,
    profileWindowLeft, profileWindowRight]
  ring

/-- Prime-weighted open windows; their endpoints are handled separately. -/
def profileWindowOpenSum (n : ℕ) : ℝ :=
  ∑ A ∈ Finset.Ico (1:ℕ) 200, ∑ j : Fin 6,
    affineOpenSum (profileWindowAlpha A j) (profileWindowBeta A j)
      (profileWindowLeft A j) (profileWindowRight A j) (n:ℝ)

theorem profileWindowOpenSum_tendsto :
    Tendsto (fun n : ℕ => profileWindowOpenSum n/(n:ℝ)^2) atTop
      (𝓝 (∑ A ∈ Finset.Ico (1:ℕ) 200, cellIntegral A)) := by
  have hrow (A : ℕ) (hA : A ∈ Finset.Ico (1:ℕ) 200) :
      Tendsto (fun n : ℕ =>
        (∑ j : Fin 6,
          affineOpenSum (profileWindowAlpha A j) (profileWindowBeta A j)
            (profileWindowLeft A j) (profileWindowRight A j) (n:ℝ))/(n:ℝ)^2)
        atTop (𝓝 (cellIntegral A)) := by
    have hAr : (1:ℝ) ≤ A := by exact_mod_cast (Finset.mem_Ico.mp hA).1
    have hsum := tendsto_finset_sum (Finset.univ : Finset (Fin 6))
      (fun j _ => affineOpenSum_nat_tendsto
        (profileWindowAlpha A j) (profileWindowBeta A j)
        (window_left_pos A hAr j) (window_left_lt_right A hAr j))
    have hmass :
        (∑ j : Fin 6, (
          profileWindowAlpha A j *
            (((profileWindowRight A j)^2-(profileWindowLeft A j)^2)/2) +
          profileWindowBeta A j *
            (profileWindowRight A j-profileWindowLeft A j))) = cellIntegral A := by
      calc
        _ = ∑ j : Fin 6, (
          profileWindowAlpha A j *
            ((profileWindowRight A j)^2-(profileWindowLeft A j)^2)/2 +
          profileWindowBeta A j *
            (profileWindowRight A j-profileWindowLeft A j)) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = _ := window_mass_eq_cell A hAr
    rw [hmass] at hsum
    simpa only [Finset.sum_div] using hsum
  have houter := tendsto_finset_sum (Finset.Ico (1:ℕ) 200)
    (fun A hA => hrow A hA)
  simpa only [profileWindowOpenSum, Finset.sum_div] using houter

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.window_mass_eq_cell
#print axioms Li2Unified.Proofs.Arithmetic.profileWindowOpenSum_tendsto

end


end
