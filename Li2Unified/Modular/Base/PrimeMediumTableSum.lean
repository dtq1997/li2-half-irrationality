module
public import Li2Unified.Modular.Base.PrimeStrictInterval
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

set_option backward.privateInPublic true

@[expose] public section

open Finset Filter Topology
namespace Li2.PrimeSums
noncomputable section

def mediumWindowAlpha : Fin 12 → ℝ :=
  ![55, 24, 35, 27, 27, 13, 10, 17, 7, 7, 3, 8]
def mediumWindowBeta : Fin 12 → ℝ :=
  ![-18, -10, -16, -13, -15, -9, -5, -11, -5, -7, -4, -10]
def mediumWindowLeft : Fin 12 → ℝ :=
  ![14/55, 1/3, 4/11, 3/8, 11/27, 3/7, 1/2, 4/7, 3/5, 2/3, 3/4, 4/5]
def mediumWindowRight : Fin 12 → ℝ :=
  ![4/15, 4/11, 3/8, 2/5, 3/7, 4/9, 4/7, 3/5, 2/3, 3/4, 4/5, 1]

lemma mediumWindowLeft_pos (i : Fin 12) : 0 < mediumWindowLeft i := by
  fin_cases i <;> norm_num [mediumWindowLeft]
lemma mediumWindowLeft_lt_right (i : Fin 12) :
    mediumWindowLeft i < mediumWindowRight i := by
  fin_cases i <;> norm_num [mediumWindowLeft, mediumWindowRight]

/-- Baseline on (x/4,x], improvements only on the twelve strict windows. -/
def mediumWindowSum (x : ℝ) : ℝ :=
  affineSum 0 (-4) (1/4) 1 x +
    ∑ i : Fin 12, affineOpenSum (mediumWindowAlpha i) (mediumWindowBeta i+4)
      (mediumWindowLeft i) (mediumWindowRight i) x

lemma mediumWindowMass_eq :
    (-4 : ℝ)*(1-1/4) +
      (∑ i : Fin 12,
        (mediumWindowAlpha i * ((mediumWindowRight i^2-mediumWindowLeft i^2)/2) +
          (mediumWindowBeta i+4)*(mediumWindowRight i-mediumWindowLeft i))) =
      -611741/356400 := by
  norm_num [Fin.sum_univ_succ, mediumWindowAlpha, mediumWindowBeta,
    mediumWindowLeft, mediumWindowRight]

theorem mediumWindowSum_nat_tendsto :
    Tendsto (fun n : ℕ => mediumWindowSum (n : ℝ)/(n : ℝ)^2)
      atTop (𝓝 (-611741/356400 : ℝ)) := by
  have hrows : Tendsto (fun n : ℕ =>
      (∑ i : Fin 12, affineOpenSum (mediumWindowAlpha i) (mediumWindowBeta i+4)
        (mediumWindowLeft i) (mediumWindowRight i) (n : ℝ))/(n : ℝ)^2)
      atTop (𝓝 (∑ i : Fin 12,
        (mediumWindowAlpha i * ((mediumWindowRight i^2-mediumWindowLeft i^2)/2) +
          (mediumWindowBeta i+4)*(mediumWindowRight i-mediumWindowLeft i)))) := by
    simp_rw [Finset.sum_div]
    exact tendsto_finset_sum Finset.univ (fun i _ =>
      affineOpenSum_nat_tendsto (mediumWindowAlpha i) (mediumWindowBeta i+4)
        (mediumWindowLeft_pos i) (mediumWindowLeft_lt_right i))
  have hbase := affineSum_nat_tendsto (0 : ℝ) (-4)
    (a := (1/4 : ℝ)) (b := 1) (by norm_num) (by norm_num)
  have h := hbase.add hrows
  simp only [zero_mul, zero_add] at h
  rw [mediumWindowMass_eq] at h
  simpa only [mediumWindowSum, add_div] using! h

end
end Li2.PrimeSums

end
