module
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

set_option backward.privateInPublic true

@[expose] public section

namespace Li2

/-- Explicit logarithmic factorial bounds for positive natural numbers. -/
theorem factorial_log_error_bounds (n : ℕ) (hn : 1 ≤ n) :
    (1 / 2 : ℝ) * Real.log (n : ℝ) + 11 / 12 ≤
        Real.log (n.factorial : ℝ) - (n : ℝ) * Real.log (n : ℝ) + (n : ℝ) ∧
      Real.log (n.factorial : ℝ) - (n : ℝ) * Real.log (n : ℝ) + (n : ℝ) ≤
        (1 / 2 : ℝ) * Real.log (n : ℝ) + 1 := by
  cases n with
  | zero => norm_num at hn
  | succ k =>
      have hn0 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hlo := Stirling.log_stirlingSeq_bounded_by_constant k
      have hhi :
          Real.log (Stirling.stirlingSeq (k + 1)) ≤
            Real.log (Stirling.stirlingSeq 1) :=
        Stirling.log_stirlingSeq'_antitone (Nat.zero_le k)
      rw [Stirling.stirlingSeq_one,
        Real.log_div (by positivity) (by positivity), Real.log_exp,
        Real.log_sqrt (by norm_num)] at hhi
      have hformula := Stirling.log_stirlingSeq_formula (k + 1)
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0,
        Real.log_div hn0 (Real.exp_ne_zero 1), Real.log_exp] at hformula
      norm_num only at hlo
      constructor <;> nlinarith only [hlo, hhi, hformula]

end Li2

end
