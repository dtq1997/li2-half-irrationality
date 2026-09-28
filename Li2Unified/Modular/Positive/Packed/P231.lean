module
public import Li2Unified.Modular.Positive.Packed.P208
public import Li2Unified.Modular.Positive.Packed.P230
public import Li2Unified.Modular.Positive.Packed.P182
public import Li2Unified.Modular.Positive.Packed.P198
public import Li2Unified.Modular.Positive.Packed.P104
public import Li2Unified.Modular.Positive.Packed.P107
public import Li2Unified.Modular.Positive.Packed.P109
public import Li2Unified.Modular.Positive.Packed.P094
public import Li2Unified.Modular.Positive.Packed.P093
public import Li2Unified.Modular.Positive.Packed.P179
public import Li2Unified.Modular.Positive.Packed.P073
public import Li2Unified.Modular.Positive.Packed.P069
public import Li2Unified.Modular.Positive.Packed.P042
public import Li2Unified.Modular.Positive.Packed.P071
public import Li2Unified.Modular.Positive.Packed.P072
public import Li2Unified.Modular.Base.OriginalContourRational
public import Li2Unified.Modular.Positive.Packed.P050
public import Li2Unified.Modular.Positive.Packed.P068

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Energy.CompactEnergy
open Li2Unified.Instances.PosHalf.LayerComparison

theorem energy_lower_triangle : (589/1000 : ℝ) ≤ comparisonEnergy :=
  energy_triangle_lower_of_certs triangleRows triangleRows_checked triangleRows_total_lower

end Li2Unified.Proofs.Energy.CompactEnergy

#print axioms Li2Unified.Proofs.Energy.CompactEnergy.energy_lower_triangle

end

section
open Polynomial MeasureTheory Filter Set
open scoped BigOperators
namespace Li2Unified.Stage0.HalfAnalytic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf
open Li2Unified.Instances.PosHalf.LayerComparison

theorem energy_lower : (589/1000:ℝ) ≤ comparisonEnergy := by
  exact Li2Unified.Proofs.Energy.CompactEnergy.energy_lower_triangle

/-- Actual measure smoothing, diagonal terms, shift and all infinite tails.
This is an all-n bridge, separate from every finite certificate. -/
theorem actual_energy_bridge :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      |aeval value (Instances.PosHalf.Qtilde n)| ≤ Real.exp
        ((6-4*Real.log 2-4*comparisonEnergy+2*(19/10:ℝ)+ε)*(n:ℝ)^2) := by
  exact Li2Unified.Proofs.Arithmetic.star_actual_energy_bridge_of_discrete_energy
    (fun h hh x hinj δ hδ =>
      Li2Unified.Proofs.Contour.starProfile_discrete_log_bound hh x hδ hinj)

theorem analytic_eventually :
    ∀ᶠ n : ℕ in atTop, |aeval value (Instances.PosHalf.Qtilde n)| ≤ Real.exp ((117/25:ℝ)*(n:ℝ)^2) := by
  have hconst :
      6 - 4*Real.log 2 - 4*comparisonEnergy + 2*(19/10:ℝ) + 1/200 ≤ 117/25 := by
    linarith [energy_lower, Real.log_two_gt_d9]
  filter_upwards [actual_energy_bridge (1/200) (by norm_num)] with n hn
  refine hn.trans (Real.exp_le_exp.mpr ?_)
  exact mul_le_mul_of_nonneg_right hconst (sq_nonneg _)

end
end Li2Unified.Stage0.HalfAnalytic

#print axioms Li2Unified.Stage0.HalfAnalytic.actual_energy_bridge

end

section
open Polynomial Filter
namespace Li2Unified.Stage0.HalfMain
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf

theorem primitive_decay :
    ∀ᶠ n : ℕ in atTop, (n+1).Prime → 5 < n+1 → n+1 ∉ badPrimes →
      |aeval value (Instances.PosHalf.P n)| ≤ Real.exp (-(1/50:ℝ)*(n:ℝ)^2) := by
  filter_upwards [HalfArithmetic.arithmetic_eventually,
    HalfAnalytic.analytic_eventually] with n hnA hnE
  intro _ _ _
  change |aeval value (ParameterFamily.P lambda n)| ≤ _
  rw [abs_P_aeval_eq_dtilde_Qtilde]
  by_cases hz : Instances.PosHalf.Qtilde n = 0
  · change (dtilde lambda n : ℝ) * |aeval value (Instances.PosHalf.Qtilde n)| ≤ _
    rw [hz, map_zero, abs_zero, mul_zero]
    exact (Real.exp_pos _).le
  · calc
      _ ≤ Real.exp (-(47/10:ℝ)*(n:ℝ)^2) *
          Real.exp ((117/25:ℝ)*(n:ℝ)^2) :=
        mul_le_mul (hnA hz) hnE (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (-(1/50:ℝ)*(n:ℝ)^2) := by
        rw [← Real.exp_add]
        congr 1
        ring

theorem irrational_value : Irrational value := by
  exact irrational_r_of_prime_decay lambda badPrimes 5
    (c := 1/50) (by norm_num) HalfPrimeEdge.edge_reduction primitive_decay

theorem irrational_literal_half :
    Irrational (∑' k : ℕ, (1/2:ℝ)^(k+1)/((k:ℝ)+1)^2) := by
  simpa only [value_eq_series] using! irrational_value

#print axioms irrational_literal_half
end
end Li2Unified.Stage0.HalfMain

end

section
namespace Li2Unified.Instances.PosHalf
noncomputable section

theorem irrational_series :
    Irrational (∑' k : ℕ, (1/2:ℝ)^(k+1)/((k:ℝ)+1)^2) :=
  @Li2Unified.Stage0.HalfMain.irrational_literal_half

end
end Li2Unified.Instances.PosHalf

end

end
