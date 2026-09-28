module
public import Li2Unified.Modular.Base.LogNormSumComparison

set_option backward.privateInPublic true

@[expose] public section

open MeasureTheory Set
open scoped BigOperators
namespace Li2
noncomputable section

theorem log_norm_sum_le_integral_add_error (m : ℕ) (y : ℝ) :
    (∑ i ∈ Finset.range m,
      Real.log ‖(((i : ℝ) + 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖) ≤
      (∫ t : ℝ in (0 : ℝ)..(m : ℝ),
        Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖) +
        (3 / 2 : ℝ) * Real.log ((m : ℝ) + 3 / 2 + |y|) + 3 / 2 := by
  let g : ℝ → ℝ :=
    fun t => Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖
  have hint (a b : ℝ) : IntervalIntegrable g volume a b :=
    intervalIntegrable_log_norm_real_add_imag_all y a b
  have htail :
      (∫ t in (m : ℝ)..((m : ℝ) + 3 / 2), g t) ≤
        (3 / 2 : ℝ) * Real.log ((m : ℝ) + 3 / 2 + |y|) := by
    have hcompare :
        (∫ t in (m : ℝ)..((m : ℝ) + 3 / 2), g t) ≤
          (∫ _ in (m : ℝ)..((m : ℝ) + 3 / 2),
            Real.log ((m : ℝ) + 3 / 2 + |y|)) := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo
        (by linarith) (hint (m : ℝ) ((m : ℝ) + 3 / 2)) (by simp) ?_
      intro t ht
      have ht0 : 0 < t := lt_of_le_of_lt (Nat.cast_nonneg m) ht.1
      have htabs : 0 < t + |y| := by positivity
      exact (log_norm_real_add_imag_bounds y ht0).2.trans
        (Real.log_le_log htabs (by linarith only [ht.2]))
    have hlength : ((m : ℝ) + 3 / 2) - (m : ℝ) = (3 / 2 : ℝ) := by ring
    simpa only [intervalIntegral.integral_const, hlength, smul_eq_mul] using hcompare
  have hhead :
      -(3 / 2 : ℝ) ≤ (∫ t in (0 : ℝ)..(3 / 2 : ℝ), g t) := by
    have hcompare :
        (∫ t in (0 : ℝ)..(3 / 2 : ℝ), Real.log t) ≤
          (∫ t in (0 : ℝ)..(3 / 2 : ℝ), g t) := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo
        (by norm_num)
        (intervalIntegral.intervalIntegrable_log'
          (a := (0 : ℝ)) (b := (3 / 2 : ℝ))) (hint 0 (3 / 2)) ?_
      intro t ht
      exact (log_norm_real_add_imag_bounds y ht.1).1
    rw [integral_log_from_zero] at hcompare
    have hlog : 0 ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
    linarith only [hcompare, hlog]
  have hsplit_m := intervalIntegral.integral_add_adjacent_intervals
      (hint 0 (m : ℝ)) (hint (m : ℝ) ((m : ℝ) + 3 / 2))
  have hsplit_head := intervalIntegral.integral_add_adjacent_intervals
      (hint 0 (3 / 2)) (hint (3 / 2) ((m : ℝ) + 3 / 2))
  have hsum :
      (∑ i ∈ Finset.range m, g ((i : ℝ) + 3 / 2)) ≤
        (∫ t in (3 / 2 : ℝ)..((m : ℝ) + 3 / 2), g t) :=
    (log_norm_sum_comparison m y).2
  change
    (∑ i ∈ Finset.range m, g ((i : ℝ) + 3 / 2)) ≤
      (∫ t in (0 : ℝ)..(m : ℝ), g t) +
        (3 / 2 : ℝ) * Real.log ((m : ℝ) + 3 / 2 + |y|) + 3 / 2
  linarith only [hsum, htail, hhead, hsplit_m, hsplit_head]

end
end Li2

end
