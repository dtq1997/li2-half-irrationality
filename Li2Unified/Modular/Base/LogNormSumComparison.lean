module
public import Li2Unified.Modular.Base.LogNormMonotone
public import Mathlib.Analysis.SumIntegralComparisons

set_option backward.privateInPublic true

@[expose] public section

open MeasureTheory Set
open scoped BigOperators
namespace Li2
noncomputable section

/-- The shifted samples lie between the two integral bounds.
The first comparison uses only positive points inside each open unit cell. -/
theorem log_norm_sum_comparison (m : ℕ) (y : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..(m : ℝ),
      Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖) ≤
        (∑ i ∈ Finset.range m,
          Real.log ‖(((i : ℝ) + 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖) ∧
      (∑ i ∈ Finset.range m,
        Real.log ‖(((i : ℝ) + 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖) ≤
        (∫ t : ℝ in (3 / 2 : ℝ)..((m : ℝ) + 3 / 2),
          Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖) := by
  let g : ℝ → ℝ :=
    fun t => Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖
  have hint (a b : ℝ) : IntervalIntegrable g volume a b :=
    intervalIntegrable_log_norm_real_add_imag_all y a b
  have hmono : MonotoneOn g (Ioi 0) := monotoneOn_log_norm_real_add_imag y
  change
    (∫ t in (0 : ℝ)..(m : ℝ), g t) ≤
        (∑ i ∈ Finset.range m, g ((i : ℝ) + 3 / 2)) ∧
      (∑ i ∈ Finset.range m, g ((i : ℝ) + 3 / 2)) ≤
        (∫ t in (3 / 2 : ℝ)..((m : ℝ) + 3 / 2), g t)
  constructor
  · calc
      (∫ t in (0 : ℝ)..(m : ℝ), g t) =
          ∑ i ∈ Finset.range m,
            ∫ t in (i : ℝ)..((i + 1 : ℕ) : ℝ), g t := by
        simpa only [Nat.cast_zero] using
          (intervalIntegral.sum_integral_adjacent_intervals
            (f := g) (μ := volume)
            (a := fun i : ℕ => (i : ℝ)) (n := m)
            (fun i _ => hint (i : ℝ) ((i + 1 : ℕ) : ℝ))).symm
      _ ≤ ∑ i ∈ Finset.range m, g ((i : ℝ) + 3 / 2) := by
        apply Finset.sum_le_sum
        intro i _
        have hcell :
            (∫ t in (i : ℝ)..((i + 1 : ℕ) : ℝ), g t) ≤
              (∫ _ in (i : ℝ)..((i + 1 : ℕ) : ℝ), g ((i : ℝ) + 3 / 2)) := by
          refine intervalIntegral.integral_mono_on_of_le_Ioo
            (by exact_mod_cast Nat.le_succ i)
            (hint (i : ℝ) ((i + 1 : ℕ) : ℝ)) (by simp) ?_
          intro t ht
          have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
          have ht0 : 0 < t := lt_of_le_of_lt hi0 ht.1
          have hsample : 0 < (i : ℝ) + 3 / 2 := by positivity
          have htupper : t < (i : ℝ) + 1 := by
            simpa only [Nat.cast_add, Nat.cast_one] using ht.2
          exact hmono ht0 hsample (by linarith)
        have hlength : ((i + 1 : ℕ) : ℝ) - (i : ℝ) = 1 := by simp
        simpa only [intervalIntegral.integral_const, hlength, one_smul] using hcell
  · have hrestrict :
        MonotoneOn g (Icc (3 / 2 : ℝ) ((3 / 2 : ℝ) + (m : ℝ))) := by
      apply hmono.mono
      intro t ht
      change 0 < t
      linarith [ht.1]
    simpa only [add_comm] using
      (MonotoneOn.sum_le_integral (x₀ := (3 / 2 : ℝ)) (a := m) hrestrict)

end
end Li2

end
