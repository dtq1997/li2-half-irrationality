module
public import Li2Unified.Modular.Base.OriginalContourIBP
public import Li2Unified.Modular.Base.OriginalContourRightTails

set_option backward.privateInPublic true

@[expose] public section

open Polynomial MeasureTheory Filter
open scoped BigOperators Topology
namespace Li2
noncomputable section

lemma originalRightContourPoint_re (N : ℕ) (y : ℝ) :
    ((N : ℂ) + originalContourPoint y).re = (N : ℝ) + (1 / 2 : ℝ) := by
  have hp : (originalContourPoint y).re = (1 / 2 : ℝ) := by
    simpa only [Nat.cast_zero, add_zero] using originalContourPoint_add_nat_re 0 y
  rw [Complex.add_re, Complex.natCast_re, hp]

lemma originalRightContourPoint_norm_le (N : ℕ) (y : ℝ) :
    ‖(N : ℂ) + originalContourPoint y‖ ≤ 1 + (N : ℝ) + |y| := by
  calc
    ‖(N : ℂ) + originalContourPoint y‖ ≤ ‖(N : ℂ)‖ + ‖originalContourPoint y‖ := norm_add_le _ _
    _ ≤ (N : ℝ) + ((1 / 2 : ℝ) + |y|) := by
      rw [Complex.norm_natCast]
      exact add_le_add (le_refl (N : ℝ)) (originalContourPoint_norm_le y)
    _ ≤ 1 + (N : ℝ) + |y| := by linarith

lemma D_eval₂_complex_right_norm_ge_one (d N : ℕ) (y : ℝ) :
    1 ≤ ‖(D d).eval₂ (Rat.castHom ℂ) ((N : ℂ) + originalContourPoint y)‖ := by
  rw [D_eval₂_complex_product, norm_prod]
  apply Finset.one_le_prod₀
  intro j hj
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hreal : 1 ≤ (((N : ℂ) + originalContourPoint y) + (j : ℂ)).re := by
    rw [Complex.add_re, originalRightContourPoint_re, Complex.natCast_re]
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  exact hreal.trans (Complex.re_le_norm _)

lemma originalRightCoefficientNormSum_nonneg (F : ℚ[X]) :
    0 ≤ originalCoefficientNormSum F := by
  unfold originalCoefficientNormSum
  exact Finset.sum_nonneg (fun k _ => norm_nonneg _)

lemma originalComplexEval_right_norm_le (F : ℚ[X]) (N : ℕ) (y : ℝ) :
    ‖F.eval₂ (Rat.castHom ℂ) ((N : ℂ) + originalContourPoint y)‖ ≤
      originalCoefficientNormSum F * (1 + (N : ℝ) + |y|) ^ F.natDegree := by
  have hp := originalRightContourPoint_norm_le N y
  have hb : 1 ≤ 1 + (N : ℝ) + |y| := by
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith [abs_nonneg y]
  rw [eval₂_eq_sum_range]
  simp only [Rat.coe_castHom]
  calc
    ‖∑ k ∈ Finset.range (F.natDegree + 1), (F.coeff k : ℂ) *
        ((N : ℂ) + originalContourPoint y) ^ k‖ ≤
      ∑ k ∈ Finset.range (F.natDegree + 1), ‖(F.coeff k : ℂ) *
        ((N : ℂ) + originalContourPoint y) ^ k‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (F.natDegree + 1), ‖(F.coeff k : ℂ)‖ *
          ‖(N : ℂ) + originalContourPoint y‖ ^ k := by simp only [norm_mul, norm_pow]
    _ ≤ ∑ k ∈ Finset.range (F.natDegree + 1), ‖(F.coeff k : ℂ)‖ *
          (1 + (N : ℝ) + |y|) ^ F.natDegree := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hk' : k ≤ F.natDegree := by have h := Finset.mem_range.mp hk; omega
      exact (pow_le_pow_left₀ (norm_nonneg _) hp k).trans (pow_le_pow_right₀ hb hk')
    _ = originalCoefficientNormSum F * (1 + (N : ℝ) + |y|) ^ F.natDegree := by
      rw [← Finset.sum_mul]
      rfl

lemma originalContourG_deriv_right_norm_le (d : ℕ) (F : ℚ[X]) (N : ℕ) (y : ℝ) :
    ‖deriv (originalContourG d F) ((N : ℂ) + originalContourPoint y)‖ ≤
      originalCoefficientNormSum (originalContourGDerivativeNumerator d F) *
        (1 + (N : ℝ) + |y|) ^ (originalContourGDerivativeNumerator d F).natDegree := by
  have hD := D_eval₂_complex_right_norm_ge_one d N y
  have hz : (D d).eval₂ (Rat.castHom ℂ) ((N : ℂ) + originalContourPoint y) ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hD)
  rw [(originalContourG_hasDerivAt_of_den_ne_zero d F hz).deriv, norm_div, norm_pow]
  exact (div_le_self (norm_nonneg _) (one_le_pow₀ hD)).trans
    (originalComplexEval_right_norm_le (originalContourGDerivativeNumerator d F) N y)

end
end Li2

end
