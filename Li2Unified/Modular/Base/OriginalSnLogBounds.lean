module
public import Li2Unified.Modular.Base.FactorialLogBounds
public import Li2Unified.Modular.Base.DecayNormalization

set_option backward.privateInPublic true

@[expose] public section

namespace Li2

@[simp]
lemma originalSn_log_zero : Real.log (Sn 0 : ℝ) = 0 := by
  norm_num [Sn]

/-- Explicit error bounds for the original rational normalization `Sn`. -/
theorem originalSn_log_error_bounds (n : ℕ) (hn : 1 ≤ n) :
    Real.log 2 - Real.log (n : ℝ) - 25 / 12 ≤
        Real.log (Sn n : ℝ) - (n : ℝ) * Real.log (n : ℝ) -
          (4 * Real.log 4 - 1) * (n : ℝ) ∧
      Real.log (Sn n : ℝ) - (n : ℝ) * Real.log (n : ℝ) -
          (4 * Real.log 4 - 1) * (n : ℝ) ≤
        Real.log 2 - Real.log (n : ℝ) - 7 / 4 := by
  have hnNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hcast : (Sn n : ℝ) =
        ((4 * n).factorial : ℝ) / (n.factorial : ℝ) ^ 3 := by
    simp only [Sn, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  have hnum : 0 < ((4 * n).factorial : ℝ) := by positivity
  have hden : 0 < (n.factorial : ℝ) := by positivity
  have hlog : Real.log (Sn n : ℝ) =
        Real.log ((4 * n).factorial : ℝ) - 3 * Real.log (n.factorial : ℝ) := by
    rw [hcast, Real.log_div hnum.ne' (pow_ne_zero 3 hden.ne'), Real.log_pow]
    norm_num
  have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog4n : Real.log ((4 * n : ℕ) : ℝ) =
        Real.log 4 + Real.log (n : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hnR.ne')
  obtain ⟨hnlo, hnhi⟩ := factorial_log_error_bounds n hn
  have h4n : 1 ≤ 4 * n := by nlinarith only [hn]
  obtain ⟨h4lo, h4hi⟩ := factorial_log_error_bounds (4 * n) h4n
  simp only [hlog4n] at h4lo h4hi
  norm_num only [Nat.cast_mul] at h4lo h4hi
  simp only [hlogfour] at h4lo h4hi
  simp only [hlog, hlogfour]
  constructor
  · nlinarith only [h4lo, hnhi]
  · nlinarith only [h4hi, hnlo]

end Li2

end
