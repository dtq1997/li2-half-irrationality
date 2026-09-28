module
public import Li2Unified.Modular.Base.OriginalContourKernel
public import Mathlib.Analysis.Complex.RemovableSingularity

set_option backward.privateInPublic true

@[expose] public section

open Filter Set
open scoped Topology
namespace Li2
noncomputable section

lemma originalContour_sin_nat (m : ℕ) :
    Complex.sin ((Real.pi : ℂ) * (m : ℂ)) = 0 := by
  rw [mul_comm, Complex.sin_nat_mul_pi]

lemma originalContour_cos_nat (m : ℕ) :
    Complex.cos ((Real.pi : ℂ) * (m : ℂ)) = (-1 : ℂ) ^ m := by
  rw [mul_comm]
  have h := congrArg (fun x : ℝ => (x : ℂ)) (Real.cos_nat_mul_pi m)
  simpa only [Complex.ofReal_cos, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one] using h

lemma originalContourSine_hasDerivAt_nat (m : ℕ) :
    HasDerivAt (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z))
      ((-1 : ℂ) ^ m * (Real.pi : ℂ)) (m : ℂ) := by
  simpa only [id_eq, mul_one, originalContour_cos_nat] using
    ((hasDerivAt_id (m : ℂ)).const_mul (Real.pi : ℂ)).csin

lemma originalContourPower_nat (m : ℕ) :
    originalContourPower (m : ℂ) = (1 / 2 : ℂ) ^ m := by
  have he : Complex.exp (-(Real.log 2 : ℂ)) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  unfold originalContourPower
  rw [mul_comm, Complex.exp_nat_mul, he]

/-- Explicit analytic extension of (z-m)*K(z). -/
def originalKernelRegularized (m : ℕ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * originalContourPower z /
    dslope (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) (m : ℂ) z

lemma originalKernelRegularized_eq (m : ℕ) (z : ℂ) (hz : z ≠ (m : ℂ)) :
    originalKernelRegularized m z = (z - (m : ℂ)) * originalContourKernel z := by
  unfold originalKernelRegularized originalContourKernel
  rw [dslope_of_ne _ hz, slope_def_field, originalContour_sin_nat, sub_zero,
    div_div_eq_mul_div]
  ring

lemma originalKernelRegularized_nat (m : ℕ) :
    originalKernelRegularized m (m : ℂ) = (-1 / 2 : ℂ) ^ m := by
  unfold originalKernelRegularized
  rw [dslope_same, (originalContourSine_hasDerivAt_nat m).deriv, originalContourPower_nat]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  calc
    (Real.pi : ℂ) * (1 / 2 : ℂ) ^ m / ((-1 : ℂ) ^ m * (Real.pi : ℂ)) =
        (1 / 2 : ℂ) ^ m / (-1 : ℂ) ^ m := by
      rw [mul_comm (Real.pi : ℂ), mul_div_mul_right _ _ hpi]
    _ = ((1 / 2 : ℂ) / (-1 : ℂ)) ^ m := (div_pow _ _ _).symm
    _ = (-1 / 2 : ℂ) ^ m := by norm_num

lemma originalKernelRegularized_nat_ne_zero (m : ℕ) :
    originalKernelRegularized m (m : ℂ) ≠ 0 := by
  rw [originalKernelRegularized_nat]
  exact pow_ne_zero _ (by norm_num)

lemma analyticAt_originalKernelRegularized (m : ℕ) :
    AnalyticAt ℂ (originalKernelRegularized m) (m : ℂ) := by
  have hn : Differentiable ℂ (fun z : ℂ => (Real.pi : ℂ) * originalContourPower z) := by
    unfold originalContourPower
    fun_prop
  have hs : Differentiable ℂ (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z)) := by
    fun_prop
  have hd : DifferentiableOn ℂ
      (dslope (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z)) (m : ℂ)) Set.univ :=
    (Complex.differentiableOn_dslope (by exact Filter.univ_mem)).2 hs.differentiableOn
  have hds : AnalyticAt ℂ
      (dslope (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z)) (m : ℂ)) (m : ℂ) :=
    hd.analyticAt Filter.univ_mem
  have hd0 : dslope (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z))
      (m : ℂ) (m : ℂ) ≠ 0 := by
    rw [dslope_same, (originalContourSine_hasDerivAt_nat m).deriv]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Real.pi_ne_zero)
  exact (hn.analyticAt _).div hds hd0

theorem originalContourKernel_residue_limit (m : ℕ) :
    Tendsto (fun z : ℂ => (z - (m : ℂ)) * originalContourKernel z)
      (𝓝[≠] (m : ℂ)) (𝓝 ((-1 / 2 : ℂ) ^ m)) := by
  have h : Tendsto (originalKernelRegularized m) (𝓝[≠] (m : ℂ))
      (𝓝 ((-1 / 2 : ℂ) ^ m)) := by
    simpa only [originalKernelRegularized_nat] using
      (analyticAt_originalKernelRegularized m).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  have he : originalKernelRegularized m =ᶠ[𝓝[≠] (m : ℂ)]
      (fun z : ℂ => (z - (m : ℂ)) * originalContourKernel z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact originalKernelRegularized_eq m z hz
  exact (tendsto_congr' he).mp h

end
end Li2

end
