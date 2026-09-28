module
public import Li2Unified.Modular.Base.LogNormIntegral

set_option backward.privateInPublic true

@[expose] public section

open MeasureTheory Set
namespace Li2
noncomputable section

/-- Integrability for every real imaginary parameter, including zero. -/
lemma intervalIntegrable_log_norm_real_add_imag_all
    (y a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖)
      volume a b := by
  simpa only [log_norm_real_add_imag, sq_abs] using
    (intervalIntegrable_log_norm_real_add_imag
      (x := |y|) (abs_nonneg y) a b)

/-- The positive real axis excludes the exceptional value `Real.log 0`. -/
lemma monotoneOn_log_norm_real_add_imag (y : ℝ) :
    MonotoneOn
      (fun t : ℝ => Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖)
      (Ioi 0) := by
  intro s hs t ht hst
  have hs0 : 0 < s := hs
  have ht0 : 0 < t := ht
  have hsquare : s ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hs0.le ht0.le).2 hst
  have hpositive : 0 < s ^ 2 + y ^ 2 :=
    add_pos_of_pos_of_nonneg (pow_pos hs0 2) (sq_nonneg y)
  simp only [log_norm_real_add_imag]
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log hpositive (by linarith only [hsquare]))
    (by norm_num)

/-- Pointwise lower and upper bounds needed for the endpoint integrals. -/
lemma log_norm_real_add_imag_bounds
    (y : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖ ∧
      Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖ ≤ Real.log (t + |y|) := by
  have ht2 : 0 < t ^ 2 := pow_pos ht 2
  have hsum : 0 < t ^ 2 + y ^ 2 :=
    add_pos_of_pos_of_nonneg ht2 (sq_nonneg y)
  have hupper : t ^ 2 + y ^ 2 ≤ (t + |y|) ^ 2 := by
    nlinarith [sq_abs y, mul_nonneg ht.le (abs_nonneg y)]
  have hlo := Real.log_le_log ht2 (le_add_of_nonneg_right (sq_nonneg y))
  have hup := Real.log_le_log hsum hupper
  norm_num only [Real.log_pow] at hlo hup
  simp only [log_norm_real_add_imag]
  constructor <;> linarith

end
end Li2

end
