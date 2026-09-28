module
public import Li2Unified.Modular.Positive.Packed.P073
public import Li2Unified.Modular.Base.OriginalContourHorizontalTails
public import Li2Unified.Modular.Base.OriginalContourRightActual
public import Li2Unified.Modular.Positive.Packed.P079

set_option backward.privateInPublic true

@[expose] public section

section
/-! The negative-half kernel on the lower horizontal side vanishes for `T=N`. -/

open Polynomial MeasureTheory Filter Set
open scoped Topology BigOperators Interval
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

def lowerMultiplier (z : ℂ) : ℂ :=
  -Complex.exp (-((Real.pi : ℂ) * Complex.I * z)) /
    (2 * (Real.pi : ℂ) * Complex.I)

lemma lowerMultiplier_norm_bottom (x T : ℝ) :
    ‖lowerMultiplier ((x : ℂ) - (T : ℂ) * Complex.I)‖ =
      Real.exp (-Real.pi * T) / (2 * Real.pi) := by
  unfold lowerMultiplier
  rw [norm_div, norm_neg, Complex.norm_exp]
  have hnum : (-((Real.pi : ℂ) * Complex.I *
      ((x : ℂ) - (T : ℂ) * Complex.I))).re = -Real.pi * T := by
    simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  have hden : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), Complex.norm_I]
    norm_num
  rw [hnum, hden]

lemma lower_bottom_integrand_norm_le (d : ℕ) (F : ℚ[X]) (N : ℕ)
    (hN : 1 ≤ N) {x T : ℝ}
    (hx : x ∈ Set.Icc (1 / 2) ((N : ℝ) + 1 / 2)) (hT : 1 ≤ T) :
    ‖(power ((x : ℂ) - (T : ℂ) * Complex.I) *
        kappaMinus ((x : ℂ) - (T : ℂ) * Complex.I)) *
        deriv (Li2.originalContourG d F) ((x : ℂ) - (T : ℂ) * Complex.I)‖ ≤
      (Real.exp (-Real.pi * T) / (2 * Real.pi)) *
        (Li2.originalContourHorizontalConstant d F N *
          T ^ (Li2.originalContourGDerivativeNumerator d F).natDegree *
          Real.exp (-Real.pi * T)) := by
  let z : ℂ := (x : ℂ) - (T : ℂ) * Complex.I
  have hzim : z.im = -T := by simp [z, Complex.sub_im, Complex.mul_im]
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
    Li2.originalContour_sin_ne_zero_of_im_ne_zero (by rw [hzim]; linarith)
  have hk : power z * kappaMinus z = lowerMultiplier z * Li2.originalContourKernel z :=
    kappaMinus_eq_kernel z hsin
  have hTabs : |-T| = T := by rw [abs_neg, abs_of_nonneg (by linarith)]
  have hold := Li2.originalContour_horizontal_integrand_norm_le d F N hN hx
    (t := -T) (by rw [hTabs]; exact hT)
  rw [hTabs] at hold
  calc
    ‖(power z * kappaMinus z) * deriv (Li2.originalContourG d F) z‖ =
        ‖lowerMultiplier z‖ *
          ‖Li2.originalContourKernel z * deriv (Li2.originalContourG d F) z‖ := by
      rw [hk]
      simp only [norm_mul]
      ring
    _ ≤ ‖lowerMultiplier z‖ *
        (Li2.originalContourHorizontalConstant d F N *
          T ^ (Li2.originalContourGDerivativeNumerator d F).natDegree *
          Real.exp (-Real.pi * T)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [z, Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using! hold
    _ = _ := by rw [lowerMultiplier_norm_bottom]

def lowerBottomIntegral (d : ℕ) (F : ℚ[X]) (N : ℕ) (T : ℝ) : ℂ :=
  ∫ x : ℝ in (1 / 2)..((N : ℝ) + 1 / 2),
    (power ((x : ℂ) - (T : ℂ) * Complex.I) *
      kappaMinus ((x : ℂ) - (T : ℂ) * Complex.I)) *
      deriv (Li2.originalContourG d F) ((x : ℂ) - (T : ℂ) * Complex.I)

lemma lowerBottomIntegral_norm_le (d : ℕ) (F : ℚ[X]) (N : ℕ)
    (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T) :
    ‖lowerBottomIntegral d F N T‖ ≤
      (N : ℝ) * ((Real.exp (-Real.pi * T) / (2 * Real.pi)) *
        (Li2.originalContourHorizontalConstant d F N *
          T ^ (Li2.originalContourGDerivativeNumerator d F).natDegree *
          Real.exp (-Real.pi * T))) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hab : (1 / 2 : ℝ) ≤ (N : ℝ) + 1 / 2 := by linarith
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 : ℝ)) (b := (N : ℝ) + 1 / 2)
    (f := fun x : ℝ =>
      (power ((x : ℂ) - (T : ℂ) * Complex.I) *
        kappaMinus ((x : ℂ) - (T : ℂ) * Complex.I)) *
        deriv (Li2.originalContourG d F) ((x : ℂ) - (T : ℂ) * Complex.I))
    (C := (Real.exp (-Real.pi * T) / (2 * Real.pi)) *
      (Li2.originalContourHorizontalConstant d F N *
        T ^ (Li2.originalContourGDerivativeNumerator d F).natDegree *
        Real.exp (-Real.pi * T)))
    (fun x hx => lower_bottom_integrand_norm_le d F N hN
      (by rw [Set.uIoc_of_le hab] at hx; exact ⟨hx.1.le, hx.2⟩) hT)
  have hlen : |((N : ℝ) + 1 / 2) - 1 / 2| = (N : ℝ) := by
    rw [add_sub_cancel_right, abs_of_nonneg (Nat.cast_nonneg N)]
  change ‖lowerBottomIntegral d F N T‖ ≤
    ((Real.exp (-Real.pi * T) / (2 * Real.pi)) *
      (Li2.originalContourHorizontalConstant d F N *
        T ^ (Li2.originalContourGDerivativeNumerator d F).natDegree *
        Real.exp (-Real.pi * T))) *
      |((N : ℝ) + 1 / 2) - 1 / 2| at hbound
  rw [hlen] at hbound
  convert hbound using 1; ring

theorem lowerBottomIntegral_diagonal_tendsto_zero (d : ℕ) (F : ℚ[X]) :
    Tendsto (fun N : ℕ => lowerBottomIntegral d F N (N : ℝ)) atTop (𝓝 0) := by
  let C : ℝ := Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F)
  let k : ℕ := (Li2.originalContourGDerivativeNumerator d F).natDegree
  have hC : 0 ≤ C := Li2.originalRightCoefficientNormSum_nonneg _
  have hr : Tendsto (fun t : ℝ =>
      t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi) * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using!
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        ((2 * k + 1 : ℕ) : ℝ) (2 * Real.pi) (by positivity)
  have hn : Tendsto (fun N : ℕ =>
      (N : ℝ) ^ (2 * k + 1) * Real.exp (-(2 * Real.pi) * (N : ℝ)))
      atTop (𝓝 0) := hr.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ =>
      (2 * C * 3 ^ k) *
        ((N : ℝ) ^ (2 * k + 1) * Real.exp (-(2 * Real.pi) * (N : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using! hn.const_mul (2 * C * 3 ^ k)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow : ((N : ℝ) + 2) ^ k ≤ (3 * (N : ℝ)) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc
    ‖lowerBottomIntegral d F N (N : ℝ)‖ ≤
        (N : ℝ) * ((Real.exp (-Real.pi * (N : ℝ)) / (2 * Real.pi)) *
          (Li2.originalContourHorizontalConstant d F N *
            (N : ℝ) ^ k * Real.exp (-Real.pi * (N : ℝ)))) :=
      lowerBottomIntegral_norm_le d F N hN hNR
    _ = 2 * C * ((N : ℝ) * ((N : ℝ) + 2) ^ k *
        (N : ℝ) ^ k *
        (Real.exp (-Real.pi * (N : ℝ)) * Real.exp (-Real.pi * (N : ℝ)))) := by
      unfold Li2.originalContourHorizontalConstant
      dsimp only [C, k]
      field_simp [hpi]
      ring
    _ = 2 * C * ((N : ℝ) * ((N : ℝ) + 2) ^ k *
        (N : ℝ) ^ k * Real.exp (-(2 * Real.pi) * (N : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ 2 * C * ((N : ℝ) * (3 * (N : ℝ)) ^ k *
        (N : ℝ) ^ k * Real.exp (-(2 * Real.pi) * (N : ℝ))) := by
      gcongr
    _ = (2 * C * 3 ^ k) *
        ((N : ℝ) ^ (2 * k + 1) * Real.exp (-(2 * Real.pi) * (N : ℝ))) := by
      rw [mul_pow, pow_add, pow_mul, pow_succ]
      ring

end
end Li2Unified.Proofs.Contour

end

section
/-! Exact finite lower-horizontal split `H+ + H- = power`, with genuine
interval integrability on the pole-free line below the real axis. -/

open Polynomial MeasureTheory Set
open scoped Interval
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

private lemma bottom_intervalIntegrable_of_analyticAt
    (f : ℂ → ℂ) (N : ℕ) (T : ℝ)
    (hf : ∀ x ∈ Set.Icc (1 / 2) ((N : ℝ) + 1 / 2),
      AnalyticAt ℂ f ((x : ℂ) - (T : ℂ) * Complex.I)) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) - (T : ℂ) * Complex.I))
      volume (1 / 2) ((N : ℝ) + 1 / 2) := by
  have hab : (1 / 2 : ℝ) ≤ (N : ℝ) + 1 / 2 := by
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro x hx
  have hp : ContinuousAt (fun s : ℝ => (s : ℂ) - (T : ℂ) * Complex.I) x := by fun_prop
  exact ((hf x hx).continuousAt.comp
    (f := fun s : ℝ => (s : ℂ) - (T : ℂ) * Complex.I) hp).continuousWithinAt

private lemma lowerMultiplier_analyticAt (z : ℂ) : AnalyticAt ℂ lowerMultiplier z := by
  have h : Differentiable ℂ lowerMultiplier := by unfold lowerMultiplier; fun_prop
  exact h.analyticAt z

theorem plainBottom_eq_upper_add_lower (d : ℕ) (F : ℚ[X]) (N : ℕ) (T : ℝ)
    (hT : 0 < T) :
    plainBottomIntegral d F N T =
      upperBottomIntegral d F N T + lowerBottomIntegral d F N T := by
  let z : ℝ → ℂ := fun x => (x : ℂ) - (T : ℂ) * Complex.I
  let p : ℝ → ℂ := fun x => (power (z x) * kappaPlus (z x)) *
    deriv (Li2.originalContourG d F) (z x)
  let m : ℝ → ℂ := fun x => (power (z x) * kappaMinus (z x)) *
    deriv (Li2.originalContourG d F) (z x)
  have hsin (x : ℝ) : Complex.sin ((Real.pi : ℂ) * z x) ≠ 0 := by
    apply Li2.originalContour_sin_ne_zero_of_im_ne_zero
    change (((x : ℂ) - (T : ℂ) * Complex.I).im) ≠ 0
    simp [Complex.sub_im, Complex.mul_im]
    linarith
  have hplus : IntervalIntegrable p volume (1 / 2) ((N : ℝ) + 1 / 2) := by
    have hi := bottom_intervalIntegrable_of_analyticAt
      (fun w : ℂ => upperMultiplier w * Li2.originalContourKernel w *
        deriv (Li2.originalContourG d F) w) N T (by
        intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
        have hzre : 0 < (z x).re := by
          dsimp [z]
          simpa using! hx0
        exact ((upperMultiplier_analyticAt (z x)).mul
          (Li2.analyticAt_originalContourKernel_of_sin_ne_zero (hsin x))).mul
          (Li2.analyticAt_originalContourG_deriv d F hzre))
    have heq : p = fun x => upperMultiplier (z x) *
        Li2.originalContourKernel (z x) *
          deriv (Li2.originalContourG d F) (z x) := by
      funext x
      dsimp only [p]
      rw [show power (z x) * kappaPlus (z x) =
        upperMultiplier (z x) * Li2.originalContourKernel (z x) from
        kappaPlus_eq_kernel (z x) (hsin x)]
    rw [heq]
    exact hi
  have hminus : IntervalIntegrable m volume (1 / 2) ((N : ℝ) + 1 / 2) := by
    have hi := bottom_intervalIntegrable_of_analyticAt
      (fun w : ℂ => lowerMultiplier w * Li2.originalContourKernel w *
        deriv (Li2.originalContourG d F) w) N T (by
        intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
        have hzre : 0 < (z x).re := by
          dsimp [z]
          simpa using! hx0
        exact ((lowerMultiplier_analyticAt (z x)).mul
          (Li2.analyticAt_originalContourKernel_of_sin_ne_zero (hsin x))).mul
          (Li2.analyticAt_originalContourG_deriv d F hzre))
    have heq : m = fun x => lowerMultiplier (z x) *
        Li2.originalContourKernel (z x) *
          deriv (Li2.originalContourG d F) (z x) := by
      funext x
      dsimp only [m]
      rw [show power (z x) * kappaMinus (z x) =
        lowerMultiplier (z x) * Li2.originalContourKernel (z x) from
        kappaMinus_eq_kernel (z x) (hsin x)]
    rw [heq]
    exact hi
  have hpoint (x : ℝ) : plainIntegrand d F (z x) = p x + m x := by
    dsimp [plainIntegrand, p, m]
    have hk := kappa_sum (z x) (hsin x)
    calc
      power (z x) * deriv (Li2.originalContourG d F) (z x) =
          (power (z x) * (kappaPlus (z x) + kappaMinus (z x))) *
            deriv (Li2.originalContourG d F) (z x) := by rw [hk]; ring
      _ = _ := by ring
  change (∫ x : ℝ in (1 / 2)..((N : ℝ) + 1 / 2), plainIntegrand d F (z x)) =
    (∫ x : ℝ in (1 / 2)..((N : ℝ) + 1 / 2), p x) +
    (∫ x : ℝ in (1 / 2)..((N : ℝ) + 1 / 2), m x)
  rw [← intervalIntegral.integral_add hplus hminus]
  congr 1
  funext x
  exact hpoint x

end
end Li2Unified.Proofs.Contour

end


end
