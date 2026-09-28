module
public import Li2Unified.Modular.Base.PrimeMediumTableSum

set_option backward.privateInPublic true

@[expose] public section

open Finset Filter Topology
namespace Li2.PrimeSums
noncomputable section

def outerWindowAlpha : Fin 5 → ℝ := ![-1, 5, 1, 3, 0]
def outerWindowBeta : Fin 5 → ℝ := ![3, -7, -1, -7, 2]
def outerWindowGamma : Fin 5 → ℝ := ![2, 1, 1, -1, -1]
def outerWindowLeft : Fin 5 → ℝ := ![1, 4/3, 3/2, 2, 3]
def outerWindowRight : Fin 5 → ℝ := ![4/3, 3/2, 2, 3, 4]

lemma outerWindowLeft_pos (i : Fin 5) : 0 < outerWindowLeft i := by
  fin_cases i <;> norm_num [outerWindowLeft]
lemma outerWindowLeft_le_right (i : Fin 5) :
    outerWindowLeft i ≤ outerWindowRight i := by
  fin_cases i <;> norm_num [outerWindowLeft, outerWindowRight]

def outerWindowLeadingSum (x : ℝ) : ℝ :=
  ∑ i : Fin 5, affineSum (outerWindowAlpha i) (outerWindowBeta i)
    (outerWindowLeft i) (outerWindowRight i) x

def outerWindowCorrection (x : ℝ) : ℝ :=
  ∑ i : Fin 5, outerWindowGamma i *
    logSum (outerWindowLeft i*x) (outerWindowRight i*x)

def outerWindowSum (x : ℝ) : ℝ :=
  outerWindowLeadingSum x + outerWindowCorrection x

lemma outerWindowMass_eq :
    (∑ i : Fin 5,
      (outerWindowAlpha i*((outerWindowRight i^2-outerWindowLeft i^2)/2) +
        outerWindowBeta i*(outerWindowRight i-outerWindowLeft i))) = (7/2 : ℝ) := by
  norm_num [Fin.sum_univ_succ, outerWindowAlpha, outerWindowBeta,
    outerWindowLeft, outerWindowRight]
lemma outerWindowCorrectionMass_eq :
    (∑ i : Fin 5, outerWindowGamma i*(outerWindowRight i-outerWindowLeft i)) =
      (-2/3 : ℝ) := by
  norm_num [Fin.sum_univ_succ, outerWindowGamma, outerWindowLeft, outerWindowRight]

theorem outerWindowLeadingSum_nat_tendsto :
    Tendsto (fun n : ℕ => outerWindowLeadingSum (n : ℝ)/(n : ℝ)^2)
      atTop (𝓝 (7/2 : ℝ)) := by
  have h : Tendsto (fun n : ℕ =>
      ∑ i : Fin 5, affineSum (outerWindowAlpha i) (outerWindowBeta i)
        (outerWindowLeft i) (outerWindowRight i) (n : ℝ)/(n : ℝ)^2)
      atTop (𝓝 (∑ i : Fin 5,
        (outerWindowAlpha i*((outerWindowRight i^2-outerWindowLeft i^2)/2) +
          outerWindowBeta i*(outerWindowRight i-outerWindowLeft i)))) :=
    tendsto_finset_sum Finset.univ (fun i _ =>
      affineSum_nat_tendsto (outerWindowAlpha i) (outerWindowBeta i)
        (outerWindowLeft_pos i) (outerWindowLeft_le_right i))
  rw [outerWindowMass_eq] at h
  simpa only [outerWindowLeadingSum, Finset.sum_div] using! h

theorem outerWindowCorrection_linear_tendsto :
    Tendsto (fun n : ℕ => outerWindowCorrection (n : ℝ)/(n : ℝ))
      atTop (𝓝 (-2/3 : ℝ)) := by
  have h : Tendsto (fun n : ℕ =>
      ∑ i : Fin 5, outerWindowGamma i *
        (logSum (outerWindowLeft i*(n : ℝ)) (outerWindowRight i*(n : ℝ))/(n : ℝ)))
      atTop (𝓝 (∑ i : Fin 5,
        outerWindowGamma i*(outerWindowRight i-outerWindowLeft i))) :=
    tendsto_finset_sum Finset.univ (fun i _ =>
      (logSum_scaled_nat_tendsto (outerWindowLeft_pos i)
        (outerWindowLeft_le_right i)).const_mul (outerWindowGamma i))
  rw [outerWindowCorrectionMass_eq] at h
  simpa only [outerWindowCorrection, Finset.sum_div, mul_div_assoc] using! h

theorem outerWindowCorrection_square_tendsto_zero :
    Tendsto (fun n : ℕ => outerWindowCorrection (n : ℝ)/(n : ℝ)^2)
      atTop (𝓝 (0 : ℝ)) := by
  have h := outerWindowCorrection_linear_tendsto.div_atTop
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  simpa only [div_div, pow_two] using! h

theorem outerWindowSum_nat_tendsto :
    Tendsto (fun n : ℕ => outerWindowSum (n : ℝ)/(n : ℝ)^2)
      atTop (𝓝 (7/2 : ℝ)) := by
  simpa only [outerWindowSum, add_div, add_zero] using!
    outerWindowLeadingSum_nat_tendsto.add outerWindowCorrection_square_tendsto_zero

def mediumOuterWindowSum (x : ℝ) : ℝ := mediumWindowSum x + outerWindowSum x

theorem mediumOuterWindowSum_nat_tendsto :
    Tendsto (fun n : ℕ => mediumOuterWindowSum (n : ℝ)/(n : ℝ)^2)
      atTop (𝓝 (635659/356400 : ℝ)) := by
  have h := mediumWindowSum_nat_tendsto.add outerWindowSum_nat_tendsto
  have hmass : (-611741/356400 : ℝ)+7/2 = 635659/356400 := by norm_num
  rw [hmass] at h
  simpa only [mediumOuterWindowSum, add_div] using! h

end
end Li2.PrimeSums

end
