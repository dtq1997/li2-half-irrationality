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
  apply Finset.one_le_prod₀
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

end
end Li2

end
