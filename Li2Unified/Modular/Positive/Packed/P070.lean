module
public import Li2Unified.Modular.Positive.Packed.P001
public import Li2Unified.Modular.Base.PoleIdentity

set_option backward.privateInPublic true

@[expose] public section

section
/-! The finite tau tail and original simple-pole values for rational
parameters. Analytic statements require abs(lam)<1; inverse shifts require lam≠0. -/
namespace Li2Unified.ParameterFamily
noncomputable section

lemma tau_cast_eq_partial_sum (lam : ℚ) (j : ℕ) : (Li2.parameterTau lam j : ℝ) =
    ∑ k ∈ Finset.range j, (lam : ℝ)^(k+1) / ((k:ℝ)+1)^2 := by
  induction j with
  | zero => simp [Li2.parameterTau]
  | succ j ih =>
    rw [Li2.parameterTau, Finset.sum_Icc_succ_top (by omega)]
    push_cast
    rw [Finset.sum_range_succ]
    have hi := ih
    unfold Li2.parameterTau at hi
    push_cast at hi
    rw [hi]

lemma r_tail (lam : ℚ) (hlam : |(lam:ℝ)| < 1) (j : ℕ) :
    ∑' k : ℕ, (lam : ℝ)^(k+j+1) / ((k+j:ℕ)+1 : ℝ)^2 =
      r lam - (Li2.parameterTau lam j : ℝ) := by
  have hs := (summable_r lam hlam).sum_add_tsum_nat_add j
  rw [← tau_cast_eq_partial_sum, ← r] at hs
  simpa only [Nat.cast_add] using (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hs))

theorem shifted_dilog_identity (lam : ℚ) (hlam : |(lam:ℝ)| < 1) (h0 : lam ≠ 0) (j : ℕ) :
    ∑' k : ℕ, (lam : ℝ)^(k+1) / ((k+j:ℕ)+1 : ℝ)^2 =
      (lam : ℝ)⁻¹^j * (r lam - (Li2.parameterTau lam j : ℝ)) := by
  rw [← r_tail lam hlam, ← tsum_mul_left]
  apply tsum_congr
  intro k
  have h0R : (lam : ℝ) ≠ 0 := by exact_mod_cast h0
  have hp : (lam : ℝ)⁻¹^j * (lam : ℝ)^j = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ h0R, one_pow]
  rw [show k+j+1 = (k+1)+j by omega, pow_add _ (k+1) j]
  calc
    (lam : ℝ)^(k+1) / ((k+j:ℕ)+1 : ℝ)^2 =
        ((lam : ℝ)^(k+1) / ((k+j:ℕ)+1 : ℝ)^2) *
          ((lam : ℝ)⁻¹^j * (lam : ℝ)^j) := by rw [hp, mul_one]
    _ = _ := by ring

theorem pole_functional_identity (lam : ℚ) (hlam : |(lam:ℝ)| < 1) (h0 : lam ≠ 0) (j : ℕ) :
    ∑' k : ℕ, (lam : ℝ)^(k+1) * (j : ℝ) / ((k+j:ℕ)+1 : ℝ)^2 =
      (j : ℝ) * (lam : ℝ)⁻¹^j * (r lam - (Li2.parameterTau lam j : ℝ)) := by
  calc
    _ = (j : ℝ) * ∑' k : ℕ, (lam : ℝ)^(k+1) / ((k+j:ℕ)+1 : ℝ)^2 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      ring
    _ = _ := by rw [shifted_dilog_identity lam hlam h0]; ring

end
end Li2Unified.ParameterFamily

end


end
