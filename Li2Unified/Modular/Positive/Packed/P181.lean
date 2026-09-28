module
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Li2Unified.Modular.Positive.Packed.P180
public import Li2Unified.Modular.Positive.Packed.P104
public import Li2Unified.Modular.Positive.Packed.P094

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section

/-- Cancel the `Sn` normalization after taking one factor per particle. -/
theorem star_particle_scale_cancel (h : ℕ) (s f a : ℝ)
    (hs : s ≠ 0) (hf : f ≠ 0) :
    (s^h/f) * (a/s)^h = a^h/f := by
  rw [div_pow]
  field_simp

/-- Split the twelfth power into the sixth power already in the fixed
prefactor and the sixth power paid for the ray shift. -/
theorem star_twelfth_split (h : ℕ) (w r : ℝ) :
    (w*r^12)^h = (w^h*r^(6*h))*r^(6*h) := by
  rw [mul_pow, ← pow_mul]
  ring

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.star_particle_scale_cancel
#print axioms Li2Unified.Proofs.Arithmetic.star_twelfth_split

end

section
open Polynomial MeasureTheory Filter
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HalfAnalytic
open Li2Unified.Instances.PosHalf.LayerComparison

private lemma star_partition_normalization_identity (n : ℕ) (hn : 1 ≤ n)
    (E : ℝ) :
    ((((Li2.Sn n)^(2*n) / Li2.Fn n : ℚ):ℝ) /
        ((2*n).factorial:ℝ)) *
      ((n:ℝ)^((2*n)^2) *
        Real.exp (-4*(n:ℝ)^2*comparisonEnergy +
          2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) *
        ((starPartitionWeightConstant*((n:ℝ)+1)^12)/(Li2.Sn n:ℝ))^(2*n) *
        (Real.exp ((n:ℝ)*(19/10:ℝ))*E)^(2*n)) =
      (starPartitionPrefactor n * E^(2*n)) *
        Real.exp ((-4*comparisonEnergy+2*(19/10:ℝ))*(n:ℝ)^2 +
          12*(n:ℝ)*Real.log ((n:ℝ)+1) +
          2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) /
        ((2*n).factorial:ℝ) := by
  have hs : (Li2.Sn n:ℝ) ≠ 0 := by exact_mod_cast (Li2.Sn_pos n).ne'
  have hf : (Li2.Fn n:ℝ) ≠ 0 := by exact_mod_cast (Li2.Fn_pos n).ne'
  have hr : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hR : ((n:ℝ)+1)^(6*(2*n)) =
      Real.exp (12*(n:ℝ)*Real.log ((n:ℝ)+1)) := by
    calc
      _ = (Real.exp (Real.log ((n:ℝ)+1)))^(6*(2*n)) := by
        rw [Real.exp_log hr]
      _ = Real.exp ((6*(2*n):ℕ)*Real.log ((n:ℝ)+1)) := by
        rw [← Real.exp_nat_mul]
      _ = _ := by
        congr 1
        push_cast
        ring
  have hE : (Real.exp ((n:ℝ)*(19/10:ℝ))*E)^(2*n) =
      Real.exp (2*(19/10:ℝ)*(n:ℝ)^2)*E^(2*n) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring_nf
  have hcancel := star_particle_scale_cancel (2*n)
    (Li2.Sn n:ℝ) (Li2.Fn n:ℝ)
    (starPartitionWeightConstant*((n:ℝ)+1)^12) hs hf
  have hsplit := star_twelfth_split (2*n)
    starPartitionWeightConstant ((n:ℝ)+1)
  let T : ℝ := -4*(n:ℝ)^2*comparisonEnergy +
    2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)
  have hExp : Real.exp ((-4*comparisonEnergy+2*(19/10:ℝ))*(n:ℝ)^2 +
      12*(n:ℝ)*Real.log ((n:ℝ)+1) +
      2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) =
      (Real.exp T * Real.exp (2*(19/10:ℝ)*(n:ℝ)^2)) *
        ((n:ℝ)+1)^(6*(2*n)) := by
    calc
      _ = Real.exp ((T+2*(19/10:ℝ)*(n:ℝ)^2) +
          12*(n:ℝ)*Real.log ((n:ℝ)+1)) := by
            congr 1
            dsimp [T]
            ring
      _ = (Real.exp T * Real.exp (2*(19/10:ℝ)*(n:ℝ)^2)) *
          Real.exp (12*(n:ℝ)*Real.log ((n:ℝ)+1)) := by
            rw [Real.exp_add, Real.exp_add]
      _ = _ := by rw [← hR]
  rw [Rat.cast_div, Rat.cast_pow, hE, hExp]
  unfold starPartitionPrefactor
  have hcore : ((Li2.Sn n:ℝ)^(2*n)/(Li2.Fn n:ℝ)) *
      ((starPartitionWeightConstant*((n:ℝ)+1)^12)/(Li2.Sn n:ℝ))^(2*n) =
      (starPartitionWeightConstant*((n:ℝ)+1)^12)^(2*n)/(Li2.Fn n:ℝ) :=
    hcancel
  rw [hsplit] at hcore
  calc
    _ = ((n:ℝ)^((2*n)^2) *
        Real.exp (-4*(n:ℝ)^2*comparisonEnergy +
          2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) *
        (((Li2.Sn n:ℝ)^(2*n)/(Li2.Fn n:ℝ)) *
          ((starPartitionWeightConstant*((n:ℝ)+1)^12)/(Li2.Sn n:ℝ))^(2*n)) *
        (Real.exp (2*(19/10:ℝ)*(n:ℝ)^2)*E^(2*n))) /
        ((2*n).factorial:ℝ) := by ring
    _ = _ := by rw [hcore]; ring

/-- The actual normalized Qtilde bound in the exact format consumed by the
subquadratic prefactor theorem. The discrete-energy input remains explicit. -/
theorem star_Qtilde_bound_of_discrete_energy (n : ℕ) (hn : 1 ≤ n)
    (henergy : ∀ v : Fin (2*n) → Fin 3 × ℝ,
      Function.Injective (fun i => starAxisPoint (v i)) →
        2 * (∑ i : Fin (2*n),
          ∑ j ∈ Finset.Ioi i,
            Real.log ‖starAxisPoint (v j) - starAxisPoint (v i)‖) ≤
          4*(n:ℝ) * (∑ i : Fin (2*n), comparisonPotential (starAxisPoint (v i))) -
            4*(n:ℝ)^2 * comparisonEnergy +
            2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) :
    |aeval Li2Unified.Instances.PosHalf.value
        (Li2Unified.Instances.PosHalf.Qtilde n)| ≤
      starPartitionPrefactor n * starEnvelopeConstant^(2*n) *
        Real.exp ((-4*comparisonEnergy+2*(19/10:ℝ))*(n:ℝ)^2 +
          12*(n:ℝ)*Real.log ((n:ℝ)+1) +
          2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) := by
  let E : ℝ := ∫ z, starEnvelope z ∂contourMeasure
  have hE : 0 ≤ E := integral_nonneg starEnvelope_nonneg
  have hEC : E ≤ starEnvelopeConstant := by
    unfold starEnvelopeConstant
    dsimp [E]
    linarith
  have hEpow : E^(2*n) ≤ starEnvelopeConstant^(2*n) :=
    pow_le_pow_left₀ hE hEC _
  have hSn : (0:ℝ) < (Li2.Sn n:ℝ) := by exact_mod_cast Li2.Sn_pos n
  have hFn : (0:ℝ) < (Li2.Fn n:ℝ) := by exact_mod_cast Li2.Fn_pos n
  have hfacpos : (0:ℝ) < ((2*n).factorial:ℝ) := by exact_mod_cast Nat.factorial_pos (2*n)
  have hfacge : (1:ℝ) ≤ ((2*n).factorial:ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (2*n)))
  have hscale : 0 ≤ ((((Li2.Sn n)^(2*n) / Li2.Fn n:ℚ):ℝ) /
      ((2*n).factorial:ℝ)) := by
    simp only [Rat.cast_div, Rat.cast_pow]
    positivity
  have hQ := Li2Unified.Proofs.Contour.actual_Qtilde_star_bound n
  have hPart := starPartition_explicit_bound n hn henergy
  have hupper := hQ.trans (mul_le_mul_of_nonneg_left hPart hscale)
  change |aeval Li2Unified.Instances.PosHalf.value
      (Li2Unified.Instances.PosHalf.Qtilde n)| ≤
    ((((Li2.Sn n)^(2*n) / Li2.Fn n:ℚ):ℝ) /
        ((2*n).factorial:ℝ)) *
      ((n:ℝ)^((2*n)^2) *
        Real.exp (-4*(n:ℝ)^2*comparisonEnergy +
          2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) *
        ((starPartitionWeightConstant*((n:ℝ)+1)^12)/(Li2.Sn n:ℝ))^(2*n) *
        (Real.exp ((n:ℝ)*(19/10:ℝ))*E)^(2*n)) at hupper
  rw [star_partition_normalization_identity n hn E] at hupper
  have hpref := starPartitionPrefactor_pos n hn
  have hXnonneg : 0 ≤ (starPartitionPrefactor n * E^(2*n)) *
      Real.exp ((-4*comparisonEnergy+2*(19/10:ℝ))*(n:ℝ)^2 +
        12*(n:ℝ)*Real.log ((n:ℝ)+1) +
        2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) := by
    positivity
  calc
    _ ≤ ((starPartitionPrefactor n * E^(2*n)) *
      Real.exp ((-4*comparisonEnergy+2*(19/10:ℝ))*(n:ℝ)^2 +
        12*(n:ℝ)*Real.log ((n:ℝ)+1) +
        2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ))) /
      ((2*n).factorial:ℝ) := hupper
    _ ≤ (starPartitionPrefactor n * E^(2*n)) *
      Real.exp ((-4*comparisonEnergy+2*(19/10:ℝ))*(n:ℝ)^2 +
        12*(n:ℝ)*Real.log ((n:ℝ)+1) +
        2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) :=
          div_le_self hXnonneg hfacge
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hEpow hpref.le) (Real.exp_pos _).le

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.star_partition_normalization_identity
#print axioms Li2Unified.Proofs.Arithmetic.star_Qtilde_bound_of_discrete_energy

end


end
