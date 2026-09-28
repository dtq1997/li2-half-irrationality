module
public import Li2Unified.Modular.Base.LogNormSumError
public import Li2Unified.Modular.Base.OriginalContourRational
public import Mathlib.Algebra.BigOperators.Intervals

set_option backward.privateInPublic true

@[expose] public section

open Polynomial MeasureTheory
open scoped BigOperators

namespace Li2
noncomputable section

theorem originalD_log_norm_eq_sum (m : ℕ) (y : ℝ) :
    Real.log ‖(D m).eval₂ (Rat.castHom ℂ) (originalContourPoint y)‖ =
      ∑ i ∈ Finset.range m,
        Real.log ‖(((i : ℝ) + 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ := by
  have hnonzero : ∀ j ∈ Finset.Icc 1 m,
      ‖originalContourPoint y + (j : ℂ)‖ ≠ 0 := by
    intro j hj
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one
      (originalContourPoint_add_nat_norm_ge_one j (Finset.mem_Icc.mp hj).1 y))
  rw [D_eval₂_complex_product, norm_prod, Real.log_prod hnonzero]
  calc
    (∑ j ∈ Finset.Icc 1 m, Real.log ‖originalContourPoint y + (j : ℂ)‖) =
        ∑ i ∈ Finset.range m,
          Real.log ‖originalContourPoint y + ((i + 1 : ℕ) : ℂ)‖ := by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      simpa only [Nat.add_sub_cancel, Nat.add_comm 1] using
        (Finset.sum_Ico_eq_sum_range
          (fun j : ℕ => Real.log ‖originalContourPoint y + (j : ℂ)‖) 1 (m + 1))
    _ = ∑ i ∈ Finset.range m,
        Real.log ‖(((i : ℝ) + 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ := by
      apply Finset.sum_congr rfl
      intro i _
      have hpoint : originalContourPoint y + ((i + 1 : ℕ) : ℂ) =
          (((i : ℝ) + 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
        simp only [originalContourPoint, Nat.cast_add, Nat.cast_one,
          Complex.ofReal_add, Complex.ofReal_div,
          Complex.ofReal_natCast, Complex.ofReal_ofNat]
        ring
      rw [hpoint]

theorem originalD_log_norm_bounds (m : ℕ) (y : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..(m : ℝ),
      Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖) ≤
        Real.log ‖(D m).eval₂ (Rat.castHom ℂ) (originalContourPoint y)‖ ∧
      Real.log ‖(D m).eval₂ (Rat.castHom ℂ) (originalContourPoint y)‖ ≤
        (∫ t : ℝ in (0 : ℝ)..(m : ℝ),
          Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖) +
          (3 / 2 : ℝ) * Real.log ((m : ℝ) + 3 / 2 + |y|) + 3 / 2 := by
  simp only [originalD_log_norm_eq_sum]
  exact ⟨(log_norm_sum_comparison m y).1,
    log_norm_sum_le_integral_add_error m y⟩

end
end Li2

end
