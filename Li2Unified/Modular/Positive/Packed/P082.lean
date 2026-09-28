module
public import Li2Unified.Modular.Positive.Packed.P079
public import Li2Unified.Modular.Base.OriginalContourRightActual
public import Li2Unified.Modular.Positive.Packed.P081
public import Li2Unified.Modular.Base.OriginalContourIBP

set_option backward.privateInPublic true

@[expose] public section

section
/-! The right edge in the pole-free Cauchy shift vanishes on `T=N`. -/

open Polynomial MeasureTheory Filter Set
open scoped Topology Interval
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

lemma plain_right_integrand_norm_le (d : ℕ) (F : ℚ[X]) (N : ℕ) (y : ℝ) :
    ‖plainIntegrand d F ((N : ℂ) + point ⟨1, by decide⟩ y)‖ ≤
      (1 / 2 : ℝ) ^ N *
        Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F) *
          (1 + (N : ℝ) + |y|) ^
            (Li2.originalContourGDerivativeNumerator d F).natDegree := by
  have hp : ‖power (point ⟨1, by decide⟩ y)‖ ≤ 1 := by
    rw [power_eq_original, point_up]
    exact Li2.originalContourPower_norm_le_one y
  have hg : ‖deriv (Li2.originalContourG d F)
      ((N : ℂ) + point ⟨1, by decide⟩ y)‖ ≤
      Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F) *
        (1 + (N : ℝ) + |y|) ^
          (Li2.originalContourGDerivativeNumerator d F).natDegree := by
    rw [point_up]
    exact Li2.originalContourG_deriv_right_norm_le d F N y
  have hp0 : ‖((1 / 2 : ℂ) ^ N)‖ = (1 / 2 : ℝ) ^ N := by norm_num
  calc
    ‖plainIntegrand d F ((N : ℂ) + point ⟨1, by decide⟩ y)‖ =
      (1 / 2 : ℝ) ^ N * ‖power (point ⟨1, by decide⟩ y)‖ *
        ‖deriv (Li2.originalContourG d F) ((N : ℂ) + point ⟨1, by decide⟩ y)‖ := by
      rw [plainIntegrand, power_eq_original, Li2.originalContourPower_nat_add,
        ← power_eq_original, norm_mul, norm_mul, hp0]
    _ ≤ (1 / 2 : ℝ) ^ N * 1 *
        (Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F) *
          (1 + (N : ℝ) + |y|) ^
            (Li2.originalContourGDerivativeNumerator d F).natDegree) := by
      gcongr
    _ = _ := by ring

lemma plainRightIntegral_diagonal_norm_le (d : ℕ) (F : ℚ[X]) (N : ℕ) :
    ‖plainRightIntegral d F N (N : ℝ)‖ ≤
      (N : ℝ) * ((1 / 2 : ℝ) ^ N *
        Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F) *
          (1 + (N : ℝ) + (N : ℝ)) ^
            (Li2.originalContourGDerivativeNumerator d F).natDegree) := by
  let C : ℝ := Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F)
  let k : ℕ := (Li2.originalContourGDerivativeNumerator d F).natDegree
  have hC : 0 ≤ C := Li2.originalRightCoefficientNormSum_nonneg _
  have hbound (y : ℝ) (hy : y ∈ Set.uIoc (-(N : ℝ)) 0) :
      ‖plainIntegrand d F ((N : ℂ) + point ⟨1, by decide⟩ y)‖ ≤
        (1 / 2 : ℝ) ^ N * C * (1 + (N : ℝ) + (N : ℝ)) ^ k := by
    have hy' : -(N : ℝ) < y ∧ y ≤ 0 := by
      have hInterval : -(N : ℝ) ≤ 0 := by exact neg_nonpos.mpr (Nat.cast_nonneg N)
      rw [Set.uIoc_of_le hInterval] at hy
      exact hy
    have hyN : |y| ≤ (N : ℝ) := abs_le.mpr ⟨hy'.1.le, by linarith⟩
    have hpow : (1 + (N : ℝ) + |y|) ^ k ≤
        (1 + (N : ℝ) + (N : ℝ)) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    calc
      _ ≤ (1 / 2 : ℝ) ^ N * C * (1 + (N : ℝ) + |y|) ^ k :=
        plain_right_integrand_norm_le d F N y
      _ ≤ (1 / 2 : ℝ) ^ N * C * (1 + (N : ℝ) + (N : ℝ)) ^ k := by
        gcongr
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(N : ℝ)) (b := (0 : ℝ))
    (f := fun y : ℝ => plainIntegrand d F ((N : ℂ) + point ⟨1, by decide⟩ y))
    (C := (1 / 2 : ℝ) ^ N * C * (1 + (N : ℝ) + (N : ℝ)) ^ k) hbound
  have hlen : |(0 : ℝ) - -(N : ℝ)| = (N : ℝ) := by
    rw [zero_sub, neg_neg, abs_of_nonneg (Nat.cast_nonneg N)]
  change ‖plainRightIntegral d F N (N : ℝ)‖ ≤
    ((1 / 2 : ℝ) ^ N * C * (1 + (N : ℝ) + (N : ℝ)) ^ k) *
      |(0 : ℝ) - -(N : ℝ)| at h
  rw [hlen] at h
  convert h using 1; ring

theorem plainRightIntegral_diagonal_tendsto_zero (d : ℕ) (F : ℚ[X]) :
    Tendsto (fun N : ℕ => plainRightIntegral d F N (N : ℝ)) atTop (𝓝 0) := by
  let C : ℝ := Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F)
  let k : ℕ := (Li2.originalContourGDerivativeNumerator d F).natDegree
  have hC : 0 ≤ C := Li2.originalRightCoefficientNormSum_nonneg _
  have hdecay := Li2.originalRightDecay_tendsto_zero (k + 1)
  have hlim : Tendsto (fun N : ℕ =>
      (C * 2 ^ k) * ((1 + (N : ℝ)) ^ (k + 1) * (1 / 2 : ℝ) ^ N))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using! hdecay.const_mul (C * 2 ^ k)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [] with N
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hshift : 1 + (N : ℝ) + (N : ℝ) ≤ 2 * (1 + (N : ℝ)) := by linarith
  have hpow : (1 + (N : ℝ) + (N : ℝ)) ^ k ≤
      (2 * (1 + (N : ℝ))) ^ k :=
    pow_le_pow_left₀ (by positivity) hshift k
  calc
    ‖plainRightIntegral d F N (N : ℝ)‖ ≤
        (N : ℝ) * ((1 / 2 : ℝ) ^ N * C *
          (1 + (N : ℝ) + (N : ℝ)) ^ k) :=
      plainRightIntegral_diagonal_norm_le d F N
    _ ≤ (1 + (N : ℝ)) * ((1 / 2 : ℝ) ^ N * C *
          (2 * (1 + (N : ℝ))) ^ k) := by
      gcongr
      linarith
    _ = (C * 2 ^ k) *
        ((1 + (N : ℝ)) ^ (k + 1) * (1 / 2 : ℝ) ^ N) := by
      rw [mul_pow, pow_succ]
      ring

end
end Li2Unified.Proofs.Contour

end

section
/-! The original numerator functional is the limit of the genuine three-arm
`G'` integrals, before integration by parts. -/

open Polynomial Filter
open scoped Topology BigOperators
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Instances.PosHalf Li2Unified.ParameterFamily

theorem finite_three_arm_derivative_identity (d : ℕ) (F : ℚ[X])
    (N : ℕ) (T : ℝ) (hT : 0 < T) :
    upperBottomIntegral d F N T - Complex.I * upperLeftIntegral d F T =
      plainRealIntegral d F N - lowerBottomIntegral d F N T -
        Complex.I * plainRightIntegral d F N T +
        Complex.I * lowerLeftLowerIntegral d F T -
        Complex.I * upperLeftUpperIntegral d F T := by
  have hplain := plain_finiteRectangle_four_edges d F N T
  have hbottom := plainBottom_eq_upper_add_lower d F N T hT
  have hupper := upperLeftIntegral_split d F T
  have hlower := plainLowerLeft_eq_upper_add_lower d F T
  linear_combination hplain - hbottom + Complex.I * hlower - Complex.I * hupper

theorem three_arm_derivative_diagonal_limit (d : ℕ) (F : ℚ[X]) :
    Tendsto (fun N : ℕ =>
      plainRealIntegral d F N +
        Complex.I * lowerLeftLowerIntegral d F (N : ℝ) -
        Complex.I * upperLeftUpperIntegral d F (N : ℝ)) atTop
      (𝓝 ((numeratorFunctional lambda d F).eval₂ (Rat.castHom ℂ) (value : ℂ))) := by
  have hupper := upper_diagonal_boundary_limit d F
  have hlower := lowerBottomIntegral_diagonal_tendsto_zero d F
  have hright := plainRightIntegral_diagonal_tendsto_zero d F
  have herror : Tendsto (fun N : ℕ =>
      lowerBottomIntegral d F N (N : ℝ) +
        Complex.I * plainRightIntegral d F N (N : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using! hlower.add (tendsto_const_nhds.mul hright)
  have hsum := hupper.add herror
  have hrewritten : Tendsto (fun N : ℕ =>
      (upperBottomIntegral d F N (N : ℝ) -
        Complex.I * upperLeftIntegral d F (N : ℝ)) +
      (lowerBottomIntegral d F N (N : ℝ) +
        Complex.I * plainRightIntegral d F N (N : ℝ))) atTop
      (𝓝 ((numeratorFunctional lambda d F).eval₂ (Rat.castHom ℂ) (value : ℂ))) := by
    simpa only [add_zero] using! hsum
  apply (tendsto_congr' _).mpr hrewritten
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have h := finite_three_arm_derivative_identity d F N (N : ℝ) hNR
  linear_combination -h

end
end Li2Unified.Proofs.Contour

end

section
/-! Finite integration by parts on the real ray, with its literal logarithmic weight. -/

open Polynomial MeasureTheory Set
open scoped Interval
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

lemma power_hasDerivAt (z : ℂ) :
    HasDerivAt power ((Real.log (1 / 2 : ℝ) : ℂ) * power z) z := by
  have h := ((hasDerivAt_id z).const_mul (Real.log (1 / 2 : ℝ) : ℂ)).cexp
  convert! h using 1 <;> simp only [power, id_eq, mul_one] <;> ring

lemma power_deriv (z : ℂ) :
    deriv power z = -(Real.log 2 : ℂ) * power z := by
  rw [(power_hasDerivAt z).deriv]
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    simp [one_div, Real.log_inv]
  simp only [hlog, Complex.ofReal_neg, neg_mul]

theorem ray_finite_ibp (d : ℕ) (F : ℚ[X]) (N : ℕ) :
    plainRealIntegral d F N =
      power (((N : ℝ) + 1 / 2 : ℝ) : ℂ) *
        Li2.originalContourG d F ((((N : ℝ) + 1 / 2 : ℝ) : ℂ)) -
      power (1 / 2 : ℂ) * Li2.originalContourG d F (1 / 2 : ℂ) +
      (Real.log 2 : ℂ) *
        ∫ x in (1 / 2 : ℝ)..((N : ℝ) + 1 / 2),
          power (x : ℂ) * Li2.originalContourG d F (x : ℂ) := by
  let a : ℝ := 1 / 2
  let b : ℝ := (N : ℝ) + 1 / 2
  have hab : a ≤ b := by dsimp [a, b]; have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N; linarith
  have hpos (x : ℝ) (hx : x ∈ Icc a b) : 0 < x := by
    have hx' := hx.1
    dsimp [a] at hx'
    linarith
  have hcast (x : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      (Complex.ofRealCLM.hasDerivAt (x := x))
  let u : ℝ → ℂ := fun x => power (x : ℂ)
  let v : ℝ → ℂ := fun x => Li2.originalContourG d F (x : ℂ)
  let u' : ℝ → ℂ := fun x => deriv power (x : ℂ)
  let v' : ℝ → ℂ := fun x => deriv (Li2.originalContourG d F) (x : ℂ)
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    simpa only [u, u', Function.comp_apply, mul_one] using!
      ((power_hasDerivAt (x : ℂ)).differentiableAt.hasDerivAt.comp x (hcast x))
  have hv (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt v (v' x) x := by
    have hz : 0 < (x : ℂ).re := by simpa using! hpos x hx
    simpa only [v, v', Function.comp_apply, mul_one] using!
      ((Li2.analyticAt_originalContourG d F hz).differentiableAt.hasDerivAt.comp
        x (hcast x))
  have hu' : IntervalIntegrable u' volume a b := by
    apply Continuous.intervalIntegrable
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((show Differentiable ℂ power by unfold power; fun_prop).analyticAt (x : ℂ)).deriv.continuousAt.comp
      (f := fun t : ℝ => (t : ℂ)) Complex.continuous_ofReal.continuousAt
  have hv' : IntervalIntegrable v' volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro x hx
    have hz : 0 < (x : ℂ).re := by simpa using! hpos x hx
    exact ((Li2.analyticAt_originalContourG_deriv d F hz).continuousAt.comp
      (f := fun t : ℝ => (t : ℂ)) Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) (u := u) (v := v) (u' := u') (v' := v')
    (fun x hx => hu x)
    (fun x hx => hv x (by simpa only [uIcc_of_le hab] using! hx)) hu' hv'
  change plainRealIntegral d F N = _
  dsimp only [u, v, u', v'] at h
  have hr : (∫ x in a..b, deriv power (x : ℂ) *
      Li2.originalContourG d F (x : ℂ)) =
      -(Real.log 2 : ℂ) *
        (∫ x in a..b, power (x : ℂ) * Li2.originalContourG d F (x : ℂ)) := by
    calc
      _ = ∫ x in a..b,
          (-(Real.log 2 : ℂ)) *
            (power (x : ℂ) * Li2.originalContourG d F (x : ℂ)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp
        rw [power_deriv]
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  have h' : (∫ x in a..b,
      power (x : ℂ) * deriv (Li2.originalContourG d F) (x : ℂ)) =
      power (b : ℂ) * Li2.originalContourG d F (b : ℂ) -
      power (a : ℂ) * Li2.originalContourG d F (a : ℂ) +
      (Real.log 2 : ℂ) *
        (∫ x in a..b, power (x : ℂ) * Li2.originalContourG d F (x : ℂ)) := by
    calc
      _ = power (b : ℂ) * Li2.originalContourG d F (b : ℂ) -
            power (a : ℂ) * Li2.originalContourG d F (a : ℂ) -
            ∫ x in a..b, deriv power (x : ℂ) *
              Li2.originalContourG d F (x : ℂ) := h
      _ = power (b : ℂ) * Li2.originalContourG d F (b : ℂ) -
            power (a : ℂ) * Li2.originalContourG d F (a : ℂ) -
            (-(Real.log 2 : ℂ) *
              ∫ x in a..b, power (x : ℂ) * Li2.originalContourG d F (x : ℂ)) := by
        exact congrArg (fun w : ℂ => power (b : ℂ) *
          Li2.originalContourG d F (b : ℂ) -
          power (a : ℂ) * Li2.originalContourG d F (a : ℂ) - w) hr
      _ = _ := by ring
  have hhalf : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
  simpa only [a, b, plainRealIntegral, plainIntegrand, hhalf] using! h'

end
end Li2Unified.Proofs.Contour

end


end
