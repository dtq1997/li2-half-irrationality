module
public import Li2Unified.Modular.Positive.Packed.P074
public import Li2Unified.Modular.Positive.Packed.P080
public import Li2Unified.Modular.Positive.Packed.P082
public import Li2Unified.Modular.Positive.Packed.P085

set_option backward.privateInPublic true

@[expose] public section

section
/-! Holomorphy of both literal positive-half kernels away from sine zeros,
obtained from their independently proved relation to the old sine kernel. -/

open Filter
open scoped Topology
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

lemma upperKernel_analyticAt_of_sin_ne {z : ℂ}
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    AnalyticAt ℂ (fun w => power w * kappaPlus w) z := by
  have hsinC : Continuous (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) := by
    fun_prop
  have he : ∀ᶠ w : ℂ in 𝓝 z,
      Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := hsinC.continuousAt.eventually_ne hz
  have hEq : (fun w => power w * kappaPlus w) =ᶠ[𝓝 z]
      (fun w => upperMultiplier w * Li2.originalContourKernel w) := by
    filter_upwards [he] with w hw
    exact kappaPlus_eq_kernel w hw
  have hA : AnalyticAt ℂ
      (fun w => upperMultiplier w * Li2.originalContourKernel w) z :=
    (upperMultiplier_analyticAt z).mul
      (Li2.analyticAt_originalContourKernel_of_sin_ne_zero hz)
  exact hA.congr hEq.symm

lemma lowerKernel_analyticAt_of_sin_ne {z : ℂ}
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    AnalyticAt ℂ (fun w => power w * kappaMinus w) z := by
  have hsinC : Continuous (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) := by
    fun_prop
  have he : ∀ᶠ w : ℂ in 𝓝 z,
      Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := hsinC.continuousAt.eventually_ne hz
  have hEq : (fun w => power w * kappaMinus w) =ᶠ[𝓝 z]
      (fun w => lowerMultiplier w * Li2.originalContourKernel w) := by
    filter_upwards [he] with w hw
    exact kappaMinus_eq_kernel w hw
  have hLow : Differentiable ℂ lowerMultiplier := by
    unfold lowerMultiplier
    fun_prop
  have hA : AnalyticAt ℂ
      (fun w => lowerMultiplier w * Li2.originalContourKernel w) z :=
    (hLow.analyticAt z).mul
      (Li2.analyticAt_originalContourKernel_of_sin_ne_zero hz)
  exact hA.congr hEq.symm

end
end Li2Unified.Proofs.Contour

end

section
/-! Actual differentiated star kernels decay on their matching vertical arms. -/

namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

private lemma upper_kappa_differentiableAt (y : ℝ) :
    DifferentiableAt ℂ kappaPlus (point ⟨1, by decide⟩ y) := by
  have hz : 1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
      point ⟨1, by decide⟩ y) ≠ 0 := by
    rw [exp_upper_arm]
    have hr : 1 + Real.exp (2 * Real.pi * y) ≠ 0 := ne_of_gt (by positivity)
    have hc : (1 : ℂ) + (Real.exp (2 * Real.pi * y) : ℂ) ≠ 0 := by
      exact_mod_cast hr
    simpa only [sub_neg_eq_add] using hc
  have hd : DifferentiableAt ℂ
      (fun z : ℂ => 1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * z))
      (point ⟨1, by decide⟩ y) := by fun_prop
  have hfun : kappaPlus =
      (fun z : ℂ => (1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * z))⁻¹) := by
    funext z
    simp only [kappaPlus, one_div]
  rw [hfun]
  exact hd.inv hz

private lemma lower_kappa_differentiableAt (y : ℝ) :
    DifferentiableAt ℂ kappaMinus (point ⟨2, by decide⟩ y) := by
  have hz : 1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
      point ⟨2, by decide⟩ y) ≠ 0 := by
    rw [exp_lower_arm]
    have hr : 1 + Real.exp (2 * Real.pi * y) ≠ 0 := ne_of_gt (by positivity)
    have hc : (1 : ℂ) + (Real.exp (2 * Real.pi * y) : ℂ) ≠ 0 := by
      exact_mod_cast hr
    simpa only [sub_neg_eq_add] using hc
  have hd : DifferentiableAt ℂ
      (fun z : ℂ => 1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z))
      (point ⟨2, by decide⟩ y) := by fun_prop
  have hfun : kappaMinus =
      (fun z : ℂ => (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z))⁻¹) := by
    funext z
    simp only [kappaMinus, one_div]
  rw [hfun]
  exact hd.inv hz

lemma upperKernel_deriv_upper_norm_le (y : ℝ) :
    ‖deriv (fun z => power z * kappaPlus z) (point ⟨1, by decide⟩ y)‖ ≤
      (Real.log 2 + 2 * Real.pi) * Real.exp (-2 * Real.pi * y) := by
  let z : ℂ := point ⟨1, by decide⟩ y
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hp : ‖power z‖ ≤ 1 := by
    change ‖power (point ⟨1, by decide⟩ y)‖ ≤ 1
    rw [power_eq_original, point_up]
    exact Li2.originalContourPower_norm_le_one y
  have hpd : ‖deriv power z‖ ≤ Real.log 2 := by
    rw [power_deriv, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hlog
  have hk : ‖kappaPlus z‖ ≤ Real.exp (-2 * Real.pi * y) :=
    kappaPlus_upper_norm_le y
  have hkd : ‖deriv kappaPlus z‖ ≤
      2 * Real.pi * Real.exp (-2 * Real.pi * y) :=
    kappaPlus_deriv_upper_norm_le y
  have hdiff : deriv (fun z => power z * kappaPlus z) z =
      deriv power z * kappaPlus z + power z * deriv kappaPlus z :=
    deriv_mul (power_hasDerivAt z).differentiableAt (upper_kappa_differentiableAt y)
  have h1 : ‖deriv power z * kappaPlus z‖ ≤
      Real.log 2 * Real.exp (-2 * Real.pi * y) := by
    rw [norm_mul]
    exact mul_le_mul hpd hk (norm_nonneg _) hlog
  have h2 : ‖power z * deriv kappaPlus z‖ ≤
      2 * Real.pi * Real.exp (-2 * Real.pi * y) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans (by simpa using hkd)
  rw [hdiff]
  calc
    ‖deriv power z * kappaPlus z + power z * deriv kappaPlus z‖ ≤
        ‖deriv power z * kappaPlus z‖ + ‖power z * deriv kappaPlus z‖ :=
      norm_add_le _ _
    _ ≤ Real.log 2 * Real.exp (-2 * Real.pi * y) +
          2 * Real.pi * Real.exp (-2 * Real.pi * y) := add_le_add h1 h2
    _ = _ := by ring

lemma lowerKernel_deriv_lower_norm_le (y : ℝ) :
    ‖deriv (fun z => power z * kappaMinus z) (point ⟨2, by decide⟩ y)‖ ≤
      (Real.log 2 + 2 * Real.pi) * Real.exp (-2 * Real.pi * y) := by
  let z : ℂ := point ⟨2, by decide⟩ y
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hp : ‖power z‖ ≤ 1 := by
    change ‖power (point ⟨2, by decide⟩ y)‖ ≤ 1
    rw [power_eq_original, point_down]
    exact Li2.originalContourPower_norm_le_one (-y)
  have hpd : ‖deriv power z‖ ≤ Real.log 2 := by
    rw [power_deriv, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hlog
  have hk : ‖kappaMinus z‖ ≤ Real.exp (-2 * Real.pi * y) :=
    kappaMinus_lower_norm_le y
  have hkd : ‖deriv kappaMinus z‖ ≤
      2 * Real.pi * Real.exp (-2 * Real.pi * y) :=
    kappaMinus_deriv_lower_norm_le y
  have hdiff : deriv (fun z => power z * kappaMinus z) z =
      deriv power z * kappaMinus z + power z * deriv kappaMinus z :=
    deriv_mul (power_hasDerivAt z).differentiableAt (lower_kappa_differentiableAt y)
  have h1 : ‖deriv power z * kappaMinus z‖ ≤
      Real.log 2 * Real.exp (-2 * Real.pi * y) := by
    rw [norm_mul]
    exact mul_le_mul hpd hk (norm_nonneg _) hlog
  have h2 : ‖power z * deriv kappaMinus z‖ ≤
      2 * Real.pi * Real.exp (-2 * Real.pi * y) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans (by simpa using hkd)
  rw [hdiff]
  calc
    ‖deriv power z * kappaMinus z + power z * deriv kappaMinus z‖ ≤
        ‖deriv power z * kappaMinus z‖ + ‖power z * deriv kappaMinus z‖ :=
      norm_add_le _ _
    _ ≤ Real.log 2 * Real.exp (-2 * Real.pi * y) +
          2 * Real.pi * Real.exp (-2 * Real.pi * y) := add_le_add h1 h2
    _ = _ := by ring

end
end Li2Unified.Proofs.Contour

end


end
