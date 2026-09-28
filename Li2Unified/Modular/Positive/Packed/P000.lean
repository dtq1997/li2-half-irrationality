module
public import Li2Unified.Modular.Base.Definition

set_option backward.privateInPublic true

@[expose] public section

section
/-! The original real series, with a rational parameter. All definitions
are total; convergence only uses the displayed strict absolute-value bound. -/
namespace Li2Unified.ParameterFamily
noncomputable section

 def r (lam : ℚ) : ℝ :=
  ∑' k : ℕ, (lam : ℝ) ^ (k+1) / ((k : ℝ)+1)^2

 theorem term_abs_bound (lam : ℚ) (k : ℕ) :
    |(lam : ℝ) ^ (k+1) / ((k : ℝ)+1)^2| ≤ |(lam : ℝ)|^(k+1) := by
  rw [abs_div, abs_pow, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (k:ℝ)+1)]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd : (1 : ℝ) ≤ ((k : ℝ)+1)^2 := by nlinarith
  exact div_le_self (by positivity) hd

 theorem summable_abs_r (lam : ℚ) (hlam : |(lam : ℝ)| < 1) :
    Summable (fun k : ℕ => |(lam : ℝ)^(k+1) / ((k : ℝ)+1)^2|) := by
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (term_abs_bound lam)
  simpa only [pow_succ] using
    (summable_geometric_of_lt_one (abs_nonneg (lam : ℝ)) hlam).mul_right |(lam : ℝ)|

 theorem summable_r (lam : ℚ) (hlam : |(lam : ℝ)| < 1) :
    Summable (fun k : ℕ => (lam : ℝ)^(k+1) / ((k : ℝ)+1)^2) :=
  summable_abs_iff.mp (summable_abs_r lam hlam)

 theorem r_negHalf : r (-1/2) = Li2.li2NegHalf := by
  norm_num [r, Li2.li2NegHalf]

end
end Li2Unified.ParameterFamily

end


end
