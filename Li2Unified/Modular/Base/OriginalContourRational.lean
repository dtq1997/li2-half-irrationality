module
public import Li2Unified.Modular.Base.OriginalContourIntegrable
public import Li2Unified.Modular.Base.OriginalRealDerivative
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Topology.Algebra.Polynomial

set_option backward.privateInPublic true

@[expose] public section

open Polynomial MeasureTheory
open scoped BigOperators
namespace Li2
noncomputable section

def originalComplexQuotient (m : ℕ) (F : ℚ[X]) (z : ℂ) : ℂ :=
  F.eval₂ (Rat.castHom ℂ) z / (D m).eval₂ (Rat.castHom ℂ) z

lemma originalComplexEval_ofReal (F : ℚ[X]) (x : ℝ) :
    F.eval₂ (Rat.castHom ℂ) (x : ℂ) = Complex.ofReal (F.eval₂ (Rat.castHom ℝ) x) := by
  have hcast : Complex.ofRealHom.comp (Rat.castHom ℝ) = Rat.castHom ℂ := by
    ext q
    exact Complex.ofReal_ratCast q
  have h := Polynomial.hom_eval₂ F (Rat.castHom ℝ) Complex.ofRealHom x
  rw [hcast] at h
  exact h.symm

lemma originalComplexQuotient_ofReal (m : ℕ) (F : ℚ[X]) (x : ℝ) :
    originalComplexQuotient m F (x : ℂ) = (originalRealQuotient m F x : ℂ) := by
  unfold originalComplexQuotient originalRealQuotient
  rw [originalComplexEval_ofReal, originalComplexEval_ofReal, Complex.ofReal_div]

lemma D_eval₂_complex_product (m : ℕ) (z : ℂ) :
    (D m).eval₂ (Rat.castHom ℂ) z = ∏ j ∈ Finset.Icc 1 m, (z + (j : ℂ)) := by
  simp only [D, eval₂_finset_prod, eval₂_add, eval₂_X, eval₂_C,
    Rat.coe_castHom, Rat.cast_natCast]

lemma originalContourPoint_add_nat_re (j : ℕ) (y : ℝ) :
    (originalContourPoint y + (j : ℂ)).re = (1 / 2 : ℝ) + (j : ℝ) := by
  simp only [originalContourPoint, Complex.add_re, Complex.div_ofNat_re,
    Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.natCast_re]
  ring

lemma originalContourPoint_add_nat_norm_ge_one (j : ℕ) (hj : 1 ≤ j) (y : ℝ) :
    1 ≤ ‖originalContourPoint y + (j : ℂ)‖ := by
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h := Complex.re_le_norm (originalContourPoint y + (j : ℂ))
  rw [originalContourPoint_add_nat_re] at h
  linarith

lemma D_eval₂_complex_norm_ge_one (m : ℕ) (y : ℝ) :
    1 ≤ ‖(D m).eval₂ (Rat.castHom ℂ) (originalContourPoint y)‖ := by
  rw [D_eval₂_complex_product, norm_prod]
  apply Finset.one_le_prod₀
  intro j hj
  exact originalContourPoint_add_nat_norm_ge_one j (Finset.mem_Icc.mp hj).1 y

lemma D_eval₂_complex_vertical_ne_zero (m : ℕ) (y : ℝ) :
    (D m).eval₂ (Rat.castHom ℂ) (originalContourPoint y) ≠ 0 := by
  exact norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (D_eval₂_complex_norm_ge_one m y))

lemma originalComplexQuotient_vertical_norm_le (m : ℕ) (F : ℚ[X]) (y : ℝ) :
    ‖originalComplexQuotient m F (originalContourPoint y)‖ ≤
      ‖F.eval₂ (Rat.castHom ℂ) (originalContourPoint y)‖ := by
  rw [originalComplexQuotient, norm_div]
  exact div_le_self (norm_nonneg _) (D_eval₂_complex_norm_ge_one m y)

def originalCoefficientNormSum (F : ℚ[X]) : ℝ :=
  ∑ k ∈ Finset.range (F.natDegree + 1), ‖(F.coeff k : ℂ)‖

lemma originalComplexEval_vertical_norm_le (F : ℚ[X]) (y : ℝ) :
    ‖F.eval₂ (Rat.castHom ℂ) (originalContourPoint y)‖ ≤
      originalCoefficientNormSum F * (1 + |y|) ^ F.natDegree := by
  have hp : ‖originalContourPoint y‖ ≤ 1 + |y| := by
    have h := originalContourPoint_norm_le y
    linarith
  rw [eval₂_eq_sum_range]
  simp only [Rat.coe_castHom]
  calc
    ‖∑ k ∈ Finset.range (F.natDegree + 1),
        (F.coeff k : ℂ) * originalContourPoint y ^ k‖ ≤
      ∑ k ∈ Finset.range (F.natDegree + 1),
        ‖(F.coeff k : ℂ) * originalContourPoint y ^ k‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (F.natDegree + 1),
        ‖(F.coeff k : ℂ)‖ * ‖originalContourPoint y‖ ^ k := by
      simp only [norm_mul, norm_pow]
    _ ≤ ∑ k ∈ Finset.range (F.natDegree + 1),
        ‖(F.coeff k : ℂ)‖ * (1 + |y|) ^ F.natDegree := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hk' : k ≤ F.natDegree := by
        have h := Finset.mem_range.mp hk
        omega
      exact (pow_le_pow_left₀ (norm_nonneg _) hp k).trans
        (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg y)) hk')
    _ = originalCoefficientNormSum F * (1 + |y|) ^ F.natDegree := by
      rw [← Finset.sum_mul]
      rfl

lemma originalComplexQuotient_vertical_polynomial_growth
    (m : ℕ) (F : ℚ[X]) (y : ℝ) :
    ‖originalComplexQuotient m F (originalContourPoint y)‖ ≤
      originalCoefficientNormSum F * (1 + |y|) ^ F.natDegree :=
  (originalComplexQuotient_vertical_norm_le m F y).trans
    (originalComplexEval_vertical_norm_le F y)

lemma continuous_originalComplexQuotient_vertical (m : ℕ) (F : ℚ[X]) :
    Continuous (fun y : ℝ => originalComplexQuotient m F (originalContourPoint y)) := by
  unfold originalComplexQuotient
  exact ((F.continuous_eval₂ (Rat.castHom ℂ)).comp continuous_originalContourPoint).div
    (((D m).continuous_eval₂ (Rat.castHom ℂ)).comp continuous_originalContourPoint)
    (D_eval₂_complex_vertical_ne_zero m)

end
end Li2

end
