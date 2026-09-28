module
public import Li2Unified.Modular.Base.OriginalContourIBP
public import Li2Unified.Modular.Base.OriginalContourHorizontalKernel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option backward.privateInPublic true

@[expose] public section

open Polynomial MeasureTheory Filter Set
open scoped BigOperators Topology Interval
namespace Li2
noncomputable section

lemma D_eval₂_complex_norm_ge_one_of_re_nonneg (d : ℕ) {z : ℂ}
    (hz : 0 ≤ z.re) : 1 ≤ ‖(D d).eval₂ (Rat.castHom ℂ) z‖ := by
  rw [D_eval₂_complex_product, norm_prod]
  apply Finset.one_le_prod
  intro j hj
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have h := Complex.re_le_norm (z + (j : ℂ))
  simp only [Complex.add_re, Complex.natCast_re] at h
  linarith

lemma originalComplexEval_norm_le_of_norm_le (F : ℚ[X]) (z : ℂ) (R : ℝ)
    (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖F.eval₂ (Rat.castHom ℂ) z‖ ≤ originalCoefficientNormSum F * R ^ F.natDegree := by
  rw [eval₂_eq_sum_range]
  simp only [Rat.coe_castHom]
  calc
    ‖∑ k ∈ Finset.range (F.natDegree + 1), (F.coeff k : ℂ) * z ^ k‖ ≤
        ∑ k ∈ Finset.range (F.natDegree + 1), ‖(F.coeff k : ℂ) * z ^ k‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (F.natDegree + 1), ‖(F.coeff k : ℂ)‖ * ‖z‖ ^ k := by
      simp only [norm_mul, norm_pow]
    _ ≤ ∑ k ∈ Finset.range (F.natDegree + 1), ‖(F.coeff k : ℂ)‖ * R ^ F.natDegree := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ F.natDegree := by have h := Finset.mem_range.mp hk; omega
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (pow_le_pow_left₀ (norm_nonneg _) hz k).trans (pow_le_pow_right₀ hR hk')
    _ = originalCoefficientNormSum F * R ^ F.natDegree := by
      rw [← Finset.sum_mul]
      rfl

lemma originalContourG_deriv_norm_le_eval (d : ℕ) (F : ℚ[X]) {z : ℂ}
    (hz : 0 ≤ z.re) :
    ‖deriv (originalContourG d F) z‖ ≤
      ‖(originalContourGDerivativeNumerator d F).eval₂ (Rat.castHom ℂ) z‖ := by
  have hD := D_eval₂_complex_norm_ge_one_of_re_nonneg d hz
  have hD0 : (D d).eval₂ (Rat.castHom ℂ) z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hD)
  rw [(originalContourG_hasDerivAt_of_den_ne_zero d F hD0).deriv, norm_div, norm_pow]
  exact div_le_self (norm_nonneg _) (one_le_pow₀ hD)

lemma originalContour_sin_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  intro hs
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
  have him : Real.pi * z.im = 0 := by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, mul_zero, zero_mul, add_zero, zero_add] using
      congrArg Complex.im hk
  exact hz ((mul_eq_zero.mp him).resolve_left Real.pi_ne_zero)

lemma continuous_originalContourKernel_horizontal {t : ℝ} (ht : t ≠ 0) :
    Continuous (fun x : ℝ => originalContourKernel ((x : ℂ) + (t : ℂ) * Complex.I)) := by
  have hp : Continuous (fun x : ℝ => originalContourPower ((x : ℂ) + (t : ℂ) * Complex.I)) := by
    unfold originalContourPower
    fun_prop
  have hs : Continuous (fun x : ℝ =>
      Complex.sin ((Real.pi : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I))) := by fun_prop
  change Continuous (fun x : ℝ =>
    (Real.pi : ℂ) * originalContourPower ((x : ℂ) + (t : ℂ) * Complex.I) /
      Complex.sin ((Real.pi : ℂ) * ((x : ℂ) + (t : ℂ) * Complex.I)))
  exact (continuous_const.mul hp).div hs (fun x =>
    originalContour_sin_ne_zero_of_im_ne_zero (by simpa using ht))

lemma intervalIntegrable_originalContour_horizontal (d : ℕ) (F : ℚ[X])
    (N : ℕ) (hN : 1 ≤ N) {t : ℝ} (ht : t ≠ 0) :
    IntervalIntegrable (fun x : ℝ =>
      originalContourKernel ((x : ℂ) + (t : ℂ) * Complex.I) *
        deriv (originalContourG d F) ((x : ℂ) + (t : ℂ) * Complex.I))
      volume (1 / 2) ((N : ℝ) + 1 / 2) := by
  have hg : ContinuousOn
      (fun x : ℝ => deriv (originalContourG d F) ((x : ℂ) + (t : ℂ) * Complex.I))
      (Set.Icc (1 / 2) ((N : ℝ) + 1 / 2)) := by
    intro x hx
    have hz : 0 < ((x : ℂ) + (t : ℂ) * Complex.I).re := by
      have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
      simpa using hx0
    have hp : ContinuousAt (fun s : ℝ => (s : ℂ) + (t : ℂ) * Complex.I) x := by fun_prop
    exact ((analyticAt_originalContourG_deriv d F hz).continuousAt.comp
      (f := fun s : ℝ => (s : ℂ) + (t : ℂ) * Complex.I) hp).continuousWithinAt
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    ((continuous_originalContourKernel_horizontal ht).continuousOn.mul hg)

lemma originalContourKernel_norm_le_exp_of_re_nonneg (z : ℂ)
    (hz : 0 ≤ z.re) (ht : 1 ≤ |z.im|) :
    ‖originalContourKernel z‖ ≤ (4 * Real.pi) * Real.exp (-Real.pi * |z.im|) := by
  have he : Real.exp (-Real.log 2 * z.re) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Real.log_nonneg (by norm_num))) hz)
  calc
    ‖originalContourKernel z‖ ≤ (4 * Real.pi) * Real.exp (-Real.log 2 * z.re) *
        Real.exp (-Real.pi * |z.im|) := originalContourKernel_norm_le_exp_general z ht
    _ ≤ (4 * Real.pi) * 1 * Real.exp (-Real.pi * |z.im|) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (Real.exp_pos _).le
    _ = (4 * Real.pi) * Real.exp (-Real.pi * |z.im|) := by ring

lemma originalContourG_deriv_horizontal_norm_le (d : ℕ) (F : ℚ[X])
    (N : ℕ) (hN : 1 ≤ N) {x t : ℝ}
    (hx : x ∈ Set.Icc (1 / 2) ((N : ℝ) + 1 / 2)) (ht : 1 ≤ |t|) :
    ‖deriv (originalContourG d F) ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      originalCoefficientNormSum (originalContourGDerivativeNumerator d F) *
        ((N : ℝ) + 2) ^ (originalContourGDerivativeNumerator d F).natDegree *
        |t| ^ (originalContourGDerivativeNumerator d F).natDegree := by
  let H := originalContourGDerivativeNumerator d F
  let z : ℂ := (x : ℂ) + (t : ℂ) * Complex.I
  let R : ℝ := ((N : ℝ) + 2) * |t|
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx.1
  have hzre : z.re = x := by simp [z]
  have hzn : ‖z‖ ≤ x + |t| := by
    calc
      ‖z‖ ≤ ‖(x : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = x + |t| := by
        simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hx0]
  have hR : 1 ≤ R := by
    have hp := mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ (N : ℝ) + 2 by linarith)
    dsimp only [R]
    nlinarith
  have hzr : ‖z‖ ≤ R := by
    have hp := mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ (N : ℝ) + 1 by linarith)
    dsimp only [R]
    nlinarith [hx.2]
  calc
    ‖deriv (originalContourG d F) z‖ ≤ ‖H.eval₂ (Rat.castHom ℂ) z‖ :=
      originalContourG_deriv_norm_le_eval d F (by rw [hzre]; exact hx0)
    _ ≤ originalCoefficientNormSum H * R ^ H.natDegree :=
      originalComplexEval_norm_le_of_norm_le H z R hR hzr
    _ = originalCoefficientNormSum H * ((N : ℝ) + 2) ^ H.natDegree * |t| ^ H.natDegree := by
      dsimp only [R]
      rw [mul_pow]
      ring

def originalContourHorizontalConstant (d : ℕ) (F : ℚ[X]) (N : ℕ) : ℝ :=
  (4 * Real.pi) * originalCoefficientNormSum (originalContourGDerivativeNumerator d F) *
    ((N : ℝ) + 2) ^ (originalContourGDerivativeNumerator d F).natDegree

lemma originalContour_horizontal_integrand_norm_le (d : ℕ) (F : ℚ[X])
    (N : ℕ) (hN : 1 ≤ N) {x t : ℝ}
    (hx : x ∈ Set.Icc (1 / 2) ((N : ℝ) + 1 / 2)) (ht : 1 ≤ |t|) :
    ‖originalContourKernel ((x : ℂ) + (t : ℂ) * Complex.I) *
      deriv (originalContourG d F) ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      originalContourHorizontalConstant d F N *
        |t| ^ (originalContourGDerivativeNumerator d F).natDegree * Real.exp (-Real.pi * |t|) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx.1
  have hK : ‖originalContourKernel ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (4 * Real.pi) * Real.exp (-Real.pi * |t|) := by
    simpa using originalContourKernel_norm_le_exp_of_re_nonneg
      ((x : ℂ) + (t : ℂ) * Complex.I) (by simpa using hx0) (by simpa using ht)
  rw [norm_mul]
  calc
    _ ≤ ((4 * Real.pi) * Real.exp (-Real.pi * |t|)) *
        (originalCoefficientNormSum (originalContourGDerivativeNumerator d F) *
          ((N : ℝ) + 2) ^ (originalContourGDerivativeNumerator d F).natDegree *
          |t| ^ (originalContourGDerivativeNumerator d F).natDegree) :=
      mul_le_mul hK (originalContourG_deriv_horizontal_norm_le d F N hN hx ht)
        (norm_nonneg _) (by positivity)
    _ = _ := by unfold originalContourHorizontalConstant; ring

def originalContourHorizontalIntegral (d : ℕ) (F : ℚ[X]) (N : ℕ) (t : ℝ) : ℂ :=
  ∫ x : ℝ in (1 / 2)..((N : ℝ) + 1 / 2),
    originalContourKernel ((x : ℂ) + (t : ℂ) * Complex.I) *
      deriv (originalContourG d F) ((x : ℂ) + (t : ℂ) * Complex.I)

lemma originalContourHorizontalIntegral_norm_le (d : ℕ) (F : ℚ[X])
    (N : ℕ) (hN : 1 ≤ N) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖originalContourHorizontalIntegral d F N t‖ ≤
      (N : ℝ) * originalContourHorizontalConstant d F N *
        |t| ^ (originalContourGDerivativeNumerator d F).natDegree * Real.exp (-Real.pi * |t|) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hab : (1 / 2 : ℝ) ≤ (N : ℝ) + 1 / 2 := by linarith
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 : ℝ)) (b := (N : ℝ) + 1 / 2)
    (f := fun x : ℝ => originalContourKernel ((x : ℂ) + (t : ℂ) * Complex.I) *
      deriv (originalContourG d F) ((x : ℂ) + (t : ℂ) * Complex.I))
    (C := originalContourHorizontalConstant d F N *
      |t| ^ (originalContourGDerivativeNumerator d F).natDegree * Real.exp (-Real.pi * |t|))
    (fun x hx => originalContour_horizontal_integrand_norm_le d F N hN
      (by rw [Set.uIoc_of_le hab] at hx; exact ⟨hx.1.le, hx.2⟩) ht)
  have hlen : |((N : ℝ) + 1 / 2) - 1 / 2| = (N : ℝ) := by
    rw [add_sub_cancel_right, abs_of_nonneg (Nat.cast_nonneg N)]
  calc
    ‖originalContourHorizontalIntegral d F N t‖ ≤
        (originalContourHorizontalConstant d F N *
          |t| ^ (originalContourGDerivativeNumerator d F).natDegree *
          Real.exp (-Real.pi * |t|)) * |((N : ℝ) + 1 / 2) - 1 / 2| := hbound
    _ = _ := by rw [hlen]; ring

lemma tendsto_originalContour_horizontal_bound (d : ℕ) (F : ℚ[X]) (N : ℕ) :
    Tendsto (fun T : ℝ => ((N : ℝ) * originalContourHorizontalConstant d F N) *
        (T ^ (originalContourGDerivativeNumerator d F).natDegree * Real.exp (-Real.pi * T)))
      atTop (𝓝 0) := by
  have h : Tendsto (fun T : ℝ =>
      T ^ (originalContourGDerivativeNumerator d F).natDegree * Real.exp (-Real.pi * T))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        ((originalContourGDerivativeNumerator d F).natDegree : ℝ) Real.pi Real.pi_pos
  simpa only [mul_zero] using h.const_mul ((N : ℝ) * originalContourHorizontalConstant d F N)

theorem tendsto_originalContourHorizontalIntegral_atTop
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (hN : 1 ≤ N) :
    Tendsto (originalContourHorizontalIntegral d F N) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_originalContour_horizontal_bound d F N)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : 0 ≤ T := by linarith
  have h := originalContourHorizontalIntegral_norm_le d F N hN
    (t := T) (by simpa only [abs_of_nonneg hT0] using hT)
  simpa only [abs_of_nonneg hT0, mul_assoc] using h

theorem tendsto_originalContourHorizontalIntegral_neg_atTop
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (hN : 1 ≤ N) :
    Tendsto (fun T : ℝ => originalContourHorizontalIntegral d F N (-T)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_originalContour_horizontal_bound d F N)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : 0 ≤ T := by linarith
  have h := originalContourHorizontalIntegral_norm_le d F N hN
    (t := -T) (by simpa only [abs_neg, abs_of_nonneg hT0] using hT)
  simpa only [abs_neg, abs_of_nonneg hT0, mul_assoc] using h

end
end Li2

end
