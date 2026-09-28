module
public import Li2Unified.Modular.Positive.Packed.P073
public import Li2Unified.Modular.Base.OriginalContourPatched

set_option backward.privateInPublic true

@[expose] public section

section
/-! Analytic patch for the positive-half upper kernel on a finite rectangle. -/

open Polynomial MeasureTheory
open scoped BigOperators Interval
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

def upperMultiplier (z : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * z) /
    (2 * (Real.pi : ℂ) * Complex.I)

lemma upperMultiplier_analyticAt (z : ℂ) : AnalyticAt ℂ upperMultiplier z := by
  have h : Differentiable ℂ upperMultiplier := by
    unfold upperMultiplier
    fun_prop
  exact h.analyticAt z

def upperPatchedRemainder (d : ℕ) (F : ℚ[X]) (N : ℕ) : ℂ → ℂ :=
  Li2.originalKernelFinitePatchedRemainder (Finset.Icc 1 N)
    (fun z => upperMultiplier z * deriv (Li2.originalContourG d F) z)

lemma upperPatchedRemainder_analyticAt (d : ℕ) (F : ℚ[X]) (N : ℕ)
    {z : ℂ} (hz : 0 < z.re) (hzN : z.re < (N : ℝ) + 1) :
    AnalyticAt ℂ (upperPatchedRemainder d F N) z := by
  have hf : AnalyticAt ℂ
      (fun w => upperMultiplier w * deriv (Li2.originalContourG d F) w) z :=
    (upperMultiplier_analyticAt z).mul
      (Li2.analyticAt_originalContourG_deriv d F hz)
  by_cases hs : Complex.sin ((Real.pi : ℂ) * z) = 0
  · obtain ⟨m, hm, rfl⟩ := Li2.originalContour_sineZero_in_Icc N hz hzN hs
    exact Li2.analyticAt_originalKernelFinitePatchedRemainder_nat _ _ m hm hf
  · exact Li2.analyticAt_originalKernelFinitePatchedRemainder_off_poles _ _ hf hs

lemma upperPatchedRemainder_continuousOn_rectangle
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (a b : ℂ)
    (ha : 0 < min a.re b.re) (hb : max a.re b.re < (N : ℝ) + 1) :
    ContinuousOn (upperPatchedRemainder d F N)
      ([[a.re, b.re]] ×ℂ [[a.im, b.im]]) := by
  intro z hz
  have hzr : min a.re b.re ≤ z.re ∧ z.re ≤ max a.re b.re := hz.1
  exact (upperPatchedRemainder_analyticAt d F N
    (lt_of_lt_of_le ha hzr.1) (lt_of_le_of_lt hzr.2 hb)).continuousAt.continuousWithinAt

lemma upperPatchedRemainder_boundaryIntegral_eq_zero
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (a b : ℂ)
    (ha : 0 < min a.re b.re) (hb : max a.re b.re < (N : ℝ) + 1) :
    Complex.boundaryIntegral (upperPatchedRemainder d F N) a b = 0 := by
  apply Complex.boundaryIntegral_eq_zero_of_diffOn (s := ∅) Set.countable_empty
  · exact upperPatchedRemainder_continuousOn_rectangle d F N a b ha hb
  · intro z hz
    have hzr : min a.re b.re < z.re ∧ z.re < max a.re b.re := hz.1.1
    exact (upperPatchedRemainder_analyticAt d F N
      (lt_trans ha hzr.1) (lt_trans hzr.2 hb)).differentiableAt

def upperPatchedIntegrand (d : ℕ) (F : ℚ[X]) (N : ℕ) (z : ℂ) : ℂ :=
  (∑ m ∈ Finset.Icc 1 N,
    ((-1 / 2 : ℂ) ^ m * (upperMultiplier (m : ℂ) *
      deriv (Li2.originalContourG d F) (m : ℂ))) * (z - (m : ℂ))⁻¹) +
    upperPatchedRemainder d F N z

lemma upperPatchedIntegrand_eq_off_poles (d : ℕ) (F : ℚ[X]) (N : ℕ)
    {z : ℂ} (hz : ∀ m ∈ Finset.Icc 1 N, z ≠ (m : ℂ))
    (hs : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    upperPatchedIntegrand d F N z =
      (power z * kappaPlus z) * deriv (Li2.originalContourG d F) z := by
  unfold upperPatchedIntegrand upperPatchedRemainder
  rw [Li2.originalKernelFinitePatchedRemainder_eq_raw _ _ hz]
  unfold Li2.originalKernelFiniteRawRemainder
  have hk : power z * kappaPlus z =
      upperMultiplier z * Li2.originalContourKernel z := by
    exact kappaPlus_eq_kernel z hs
  rw [hk]
  simp only [div_eq_mul_inv]
  ring

end
end Li2Unified.Proofs.Contour

end


end
