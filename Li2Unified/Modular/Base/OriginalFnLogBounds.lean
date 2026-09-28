module
public import Li2Unified.Modular.Base.SumNatMulLog
public import Li2Unified.Modular.Base.FactorialLogBounds
public import Li2Unified.Modular.Base.DecayNormalization
public import Mathlib.Data.Rat.BigOperators

set_option backward.privateInPublic true

@[expose] public section

open scoped BigOperators
namespace Li2
noncomputable section

private lemma factorial_log_sum_bounds (h : ℕ) (hh : 1 ≤ h) :
    (h : ℝ) ^ 2 * Real.log (h : ℝ) - (3 / 2 : ℝ) * (h : ℝ) ^ 2 -
        2 * (h : ℝ) * Real.log (h : ℝ) ≤
      2 * (∑ i ∈ Finset.range h, Real.log (i.factorial : ℝ)) ∧
    2 * (∑ i ∈ Finset.range h, Real.log (i.factorial : ℝ)) ≤
      (h : ℝ) ^ 2 * Real.log (h : ℝ) - (3 / 2 : ℝ) * (h : ℝ) ^ 2 +
        (h : ℝ) * Real.log (h : ℝ) + 4 * (h : ℝ) := by
  have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hlogh : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg hhR
  obtain ⟨htlo, hthi⟩ := sum_nat_mul_log_bounds h hh
  have hslo : (∑ i ∈ Finset.range h,
        ((i : ℝ) * Real.log (i : ℝ) - (i : ℝ))) ≤
      (∑ i ∈ Finset.range h, Real.log (i.factorial : ℝ)) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi0 : i = 0
    · simp [hi0]
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
      have hlogi : 0 ≤ Real.log (i : ℝ) := Real.log_nonneg hiR
      have hb := (factorial_log_error_bounds i hi1).1
      linarith only [hb, hlogi]
  have hsup : (∑ i ∈ Finset.range h, Real.log (i.factorial : ℝ)) ≤
      (∑ i ∈ Finset.range h,
        ((i : ℝ) * Real.log (i : ℝ) - (i : ℝ) +
          ((1 / 2 : ℝ) * Real.log (h : ℝ) + 1))) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hi0 : i = 0
    · simpa [hi0] using
        (show (0 : ℝ) ≤ (1 / 2 : ℝ) * Real.log (h : ℝ) + 1 by
          linarith only [hlogh])
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
      have hih : (i : ℝ) ≤ (h : ℝ) := by
        exact_mod_cast (Finset.mem_range.mp hi).le
      have hlogi : Real.log (i : ℝ) ≤ Real.log (h : ℝ) :=
        Real.log_le_log (by linarith only [hiR]) hih
      have hb := (factorial_log_error_bounds i hi1).2
      linarith only [hb, hlogi]
  simp only [Finset.sum_sub_distrib] at hslo
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsup
  have hid0 : (∑ i ∈ Finset.range h, (i : ℝ)) * 2 =
        (h : ℝ) * ((h - 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] using
      congrArg (fun k : ℕ => (k : ℝ)) (Finset.sum_range_id_mul_two h)
  have hid : (∑ i ∈ Finset.range h, (i : ℝ)) * 2 =
        (h : ℝ) * ((h : ℝ) - 1) := by
    simpa only [Nat.cast_sub hh, Nat.cast_one] using hid0
  constructor
  · nlinarith only [hslo, htlo, hid, hhR]
  · nlinarith only [hsup, hthi, hid, hhR]

lemma originalFn_log_eq_sum (n : ℕ) :
    Real.log (Fn n : ℝ) =
      2 * (∑ i ∈ Finset.range (2 * n), Real.log (i.factorial : ℝ)) := by
  have hcast : (Fn n : ℝ) =
        ∏ i ∈ Finset.range (2 * n), (i.factorial : ℝ) ^ 2 := by
    simp only [Fn, Rat.cast_prod, Rat.cast_pow, Rat.cast_natCast]
  have hnonzero : ∀ i ∈ Finset.range (2 * n), (i.factorial : ℝ) ^ 2 ≠ 0 := by
    intro i _
    positivity
  rw [hcast, Real.log_prod hnonzero]
  simp only [Real.log_pow, Nat.cast_ofNat, Finset.mul_sum]

/-- Explicit error for the original `Fn`, for every `n ≥ 1`. -/
theorem originalFn_log_error_bound (n : ℕ) (hn : 1 ≤ n) :
    |Real.log (Fn n : ℝ) -
      (4 * (n : ℝ) ^ 2 * Real.log (n : ℝ) +
        (4 * Real.log 2 - 6) * (n : ℝ) ^ 2)| ≤
      20 * (n : ℝ) * Real.log ((n : ℝ) + 1) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith only [hnR]
  have h2n : 1 ≤ 2 * n := by nlinarith only [hn]
  obtain ⟨hlo, hup⟩ := factorial_log_sum_bounds (2 * n) h2n
  have hlog2n : Real.log ((2 * n : ℕ) : ℝ) =
        Real.log 2 + Real.log (n : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0)
  simp only [hlog2n] at hlo hup
  norm_num only [Nat.cast_mul] at hlo hup
  have hlogtwo : Real.log 2 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by linarith only [hnR])
  have hlogn : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by linarith only [hnR]) (by linarith)
  have hhalf_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hhalf : (1 / 2 : ℝ) ≤ Real.log ((n : ℝ) + 1) := hhalf_two.trans hlogtwo
  have hmul : (n : ℝ) * (Real.log 2 + Real.log (n : ℝ)) ≤
        (n : ℝ) * (2 * Real.log ((n : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left (by linarith only [hlogtwo, hlogn])
      (by linarith only [hnR])
  have hhalf_mul : (n : ℝ) * (1 / 2 : ℝ) ≤
        (n : ℝ) * Real.log ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hhalf (by linarith only [hnR])
  rw [originalFn_log_eq_sum, abs_le]
  constructor
  · nlinarith only [hlo, hmul, hhalf_mul, hnR]
  · nlinarith only [hup, hmul, hhalf_mul]

end
end Li2

end
