module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

set_option backward.privateInPublic true

@[expose] public section

section
/-! Exact dilation of the positive-ray logarithmic integral. -/

open MeasureTheory
namespace Li2Unified.Proofs.Contour
noncomputable section

lemma integral_log_shift (t a : ℝ) :
    (∫ s in (0 : ℝ)..a, Real.log (t + s)) =
      (t + a) * Real.log (t + a) - t * Real.log t - a := by
  have h := intervalIntegral.integral_comp_add_left
    (a := (0 : ℝ)) (b := a) Real.log t
  calc
    (∫ s in (0 : ℝ)..a, Real.log (t + s)) =
        ∫ s in t..t + a, Real.log s := by
      simpa only [add_zero] using h
    _ = _ := by rw [integral_log]; ring

lemma integral_log_shift_scale (n : ℕ) (hn : 1 ≤ n)
    (x a : ℝ) (hx : 0 < x) (ha : 0 ≤ a) :
    (∫ s in (0 : ℝ)..((n : ℝ) * a),
      Real.log ((n : ℝ) * x + s)) =
      ((n : ℝ) * a) * Real.log (n : ℝ) +
        (n : ℝ) * (∫ s in (0 : ℝ)..a, Real.log (x + s)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hxa : 0 < x + a := by linarith
  rw [integral_log_shift, integral_log_shift]
  have hsum : (n : ℝ) * x + (n : ℝ) * a = (n : ℝ) * (x + a) := by ring
  rw [hsum, Real.log_mul hnR.ne' hxa.ne', Real.log_mul hnR.ne' hx.ne']
  ring

end
end Li2Unified.Proofs.Contour

end


end
