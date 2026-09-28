module
public import Li2Unified.Modular.Positive.Packed.P101

set_option backward.privateInPublic true

@[expose] public section

section
/-! The same all-n logarithmic-product bound on the oriented lower arm. -/

open Polynomial MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

private lemma lower_vertical_potential_eq (y : ℝ) :
    Li2.originalExternalV (-y) - Real.pi * |y| = Vvertical y := by
  rw [Li2.even_originalExternalV y, Li2.originalExternalV_eq_log_integrals]
  unfold Vvertical baseVertical
  ring

private lemma lower_ratio_exp_bound (n : ℕ) (hn : 1 ≤ n)
    (y : ℝ) (hy : 0 ≤ y) :
    let t : ℝ := (n : ℝ) * y
    let A : ℝ := (Li2.Sn n : ℝ) *
      ‖(Li2.D n).eval₂ (Rat.castHom ℂ) (Li2.originalContourPoint (-t))‖ ^ 3 /
      ‖(Li2.D (4 * n)).eval₂ (Rat.castHom ℂ) (Li2.originalContourPoint (-t))‖
    A * Real.exp (-2 * Real.pi * t) ≤
      Real.exp ((n : ℝ) * Vvertical y + Real.log 2 - Real.log (n : ℝ) +
        (9 / 2 : ℝ) * Real.log ((n : ℝ) + 3 / 2 + t) + 11 / 4) := by
  dsimp only
  let t : ℝ := (n : ℝ) * y
  let A : ℝ := (Li2.Sn n : ℝ) *
    ‖(Li2.D n).eval₂ (Rat.castHom ℂ) (Li2.originalContourPoint (-t))‖ ^ 3 /
    ‖(Li2.D (4 * n)).eval₂ (Rat.castHom ℂ) (Li2.originalContourPoint (-t))‖
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have ht : 0 ≤ t := mul_nonneg hnR.le hy
  have hS : 0 < (Li2.Sn n : ℝ) := by exact_mod_cast Li2.Sn_pos n
  have hD (m : ℕ) : 0 < ‖(Li2.D m).eval₂ (Rat.castHom ℂ)
      (Li2.originalContourPoint (-t))‖ :=
    norm_pos_iff.mpr (Li2.D_eval₂_complex_vertical_ne_zero m (-t))
  have hA : 0 < A := div_pos (mul_pos hS (pow_pos (hD n) 3)) (hD (4 * n))
  have hlog : Real.log A = Real.log (Li2.Sn n : ℝ) +
      3 * Real.log ‖(Li2.D n).eval₂ (Rat.castHom ℂ)
        (Li2.originalContourPoint (-t))‖ -
      Real.log ‖(Li2.D (4 * n)).eval₂ (Rat.castHom ℂ)
        (Li2.originalContourPoint (-t))‖ := by
    dsimp only [A]
    rw [Real.log_div (mul_ne_zero hS.ne' (pow_ne_zero 3 (hD n).ne'))
      (hD (4 * n)).ne', Real.log_mul hS.ne' (pow_ne_zero 3 (hD n).ne'),
      Real.log_pow]
    norm_num
  have hscalar : Real.log A - 2 * Real.pi * t ≤
      (n : ℝ) * Vvertical y + Real.log 2 - Real.log (n : ℝ) +
        (9 / 2 : ℝ) * Real.log ((n : ℝ) + 3 / 2 + t) + 11 / 4 := by
    have h := Li2.original_scaled_product_log_upper n hn (-y)
    have hneg : (n : ℝ) * -y = -t := by dsimp [t]; ring
    rw [hneg] at h
    rw [← hlog] at h
    rw [abs_neg, abs_of_nonneg ht] at h
    have hv := lower_vertical_potential_eq y
    rw [abs_of_nonneg hy] at hv
    dsimp only [t] at *
    nlinarith only [h, hv]
  have he := Real.exp_le_exp.mpr hscalar
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hA] at he
  rw [show -(2 * Real.pi * t) = -2 * Real.pi * t by ring] at he
  exact he

theorem normalized_down_density_exp_bound (n : ℕ) (hn : 1 ≤ n)
    (y : ℝ) (hy : 0 ≤ y) :
    let t : ℝ := (n : ℝ) * y
    (Li2.Sn n : ℝ) * ‖density ⟨2, by decide⟩ t *
      Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3)
        (point ⟨2, by decide⟩ t)‖ ≤
      (Real.log 2 + 2 * Real.pi) * (1 + t) *
        Real.exp ((n : ℝ) * Vvertical y + Real.log 2 - Real.log (n : ℝ) +
          (9 / 2 : ℝ) * Real.log ((n : ℝ) + 3 / 2 + t) + 11 / 4) := by
  dsimp only
  let t : ℝ := (n : ℝ) * y
  let z : ℂ := point ⟨2, by decide⟩ t
  let A : ℝ := (Li2.Sn n : ℝ) *
    ‖(Li2.D n).eval₂ (Rat.castHom ℂ) z‖ ^ 3 /
    ‖(Li2.D (4 * n)).eval₂ (Rat.castHom ℂ) z‖
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ht : 0 ≤ t := mul_nonneg hnR hy
  have hS : 0 ≤ (Li2.Sn n : ℝ) := by exact_mod_cast (Li2.Sn_pos n).le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hz : ‖z‖ ≤ 1 + t := by
    dsimp [z]
    change ‖point ⟨2, by decide⟩ t‖ ≤ 1 + t
    rw [point_down]
    have h := Li2.originalContourPoint_norm_le (-t)
    rw [abs_neg, abs_of_nonneg ht] at h
    linarith
  have hder := lowerKernel_deriv_lower_norm_le t
  have he : A * Real.exp (-2 * Real.pi * t) ≤
      Real.exp ((n : ℝ) * Vvertical y + Real.log 2 - Real.log (n : ℝ) +
        (9 / 2 : ℝ) * Real.log ((n : ℝ) + 3 / 2 + t) + 11 / 4) := by
    simpa only [point_down, A, z, t] using lower_ratio_exp_bound n hn y hy
  have hc : 0 ≤ (Real.log 2 + 2 * Real.pi) * (1 + t) := by positivity
  calc
    (Li2.Sn n : ℝ) * ‖density ⟨2, by decide⟩ t *
      Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3) z‖ =
        A * ‖z‖ * ‖deriv (fun w => power w * kappaMinus w) z‖ := by
      change (Li2.Sn n : ℝ) * ‖(-Complex.I * z *
        deriv (fun w => power w * kappaMinus w) z) *
        Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3) z‖ = _
      simp only [Li2.originalComplexQuotient, norm_mul, norm_div,
        norm_pow, eval₂_pow, norm_neg, Complex.norm_I, one_mul]
      dsimp only [A]
      ring
    _ ≤ A * (1 + t) *
        ((Real.log 2 + 2 * Real.pi) * Real.exp (-2 * Real.pi * t)) := by
      gcongr
    _ = ((Real.log 2 + 2 * Real.pi) * (1 + t)) *
        (A * Real.exp (-2 * Real.pi * t)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he hc

end
end Li2Unified.Proofs.Contour

end


end
