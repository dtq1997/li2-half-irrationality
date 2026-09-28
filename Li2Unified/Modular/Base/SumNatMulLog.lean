module
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

set_option backward.privateInPublic true

@[expose] public section

open MeasureTheory Set
open scoped BigOperators
namespace Li2
noncomputable section

lemma integral_mul_log_one {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in (1 : ℝ)..b, x * Real.log x) =
      b ^ 2 / 2 * Real.log b - b ^ 2 / 4 + 1 / 4 := by
  have hd (x : ℝ) (hx : 1 ≤ x) :
      HasDerivAt
        (fun t : ℝ => t ^ 2 / 2 * Real.log t - t ^ 2 / 4)
        (x * Real.log x) x := by
    have hx0 : x ≠ 0 := by linarith
    convert ((((hasDerivAt_id x).fun_pow 2).div_const 2).mul
      (Real.hasDerivAt_log hx0)).sub
        (((hasDerivAt_id x).fun_pow 2).div_const 4) using 1
    <;> dsimp only [id_eq]
    <;> field_simp [hx0]
    <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (1 : ℝ)) (b := b)
    (f := fun t : ℝ => t ^ 2 / 2 * Real.log t - t ^ 2 / 4)
    (f' := fun t : ℝ => t * Real.log t)
    (fun x hx => hd x (by
      have hx' : x ∈ Icc (1 : ℝ) b := by
        simpa only [uIcc_of_le hb] using hx
      exact hx'.1))
    (Real.continuous_mul_log.intervalIntegrable 1 b)
  simpa only [one_pow, Real.log_one, mul_zero, zero_sub,
    sub_neg_eq_add] using hi

theorem sum_nat_mul_log_bounds (h : ℕ) (hh : 1 ≤ h) :
    (h : ℝ) ^ 2 / 2 * Real.log (h : ℝ) -
        (h : ℝ) ^ 2 / 4 + 1 / 4 - (h : ℝ) * Real.log (h : ℝ) ≤
      (∑ i ∈ Finset.range h, (i : ℝ) * Real.log (i : ℝ)) ∧
    (∑ i ∈ Finset.range h, (i : ℝ) * Real.log (i : ℝ)) ≤
      (h : ℝ) ^ 2 / 2 * Real.log (h : ℝ) -
        (h : ℝ) ^ 2 / 4 + 1 / 4 := by
  let f : ℝ → ℝ := fun x => x * Real.log x
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 0 := by simp [f]
  have hhpos : 0 < h := lt_of_lt_of_le Nat.zero_lt_one hh
  have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hm : MonotoneOn f (Icc (1 : ℝ) (h : ℝ)) := by
    intro x hx z hz hxz
    have hx0 : 0 < x := by linarith [hx.1]
    have hz0 : 0 ≤ z := by linarith [hz.1]
    calc
      f x = x * Real.log x := rfl
      _ ≤ z * Real.log x :=
        mul_le_mul_of_nonneg_right hxz (Real.log_nonneg hx.1)
      _ ≤ z * Real.log z :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hx0 hxz) hz0
      _ = f z := rfl
  have hleft : (∑ i ∈ Finset.Ico 1 h, f (i : ℝ)) =
        ∑ i ∈ Finset.range h, f (i : ℝ) := by
    simpa only [Nat.cast_zero, hf0, zero_add] using
      (Finset.sum_range_eq_add_Ico (fun i : ℕ => f (i : ℝ)) hhpos).symm
  have hremove : (∑ i ∈ Finset.range h, f ((i + 1 : ℕ) : ℝ)) =
        ∑ i ∈ Finset.Ico 1 h, f ((i + 1 : ℕ) : ℝ) := by
    simpa only [Nat.zero_add, Nat.cast_one, hf1, zero_add] using
      (Finset.sum_range_eq_add_Ico
        (fun i : ℕ => f ((i + 1 : ℕ) : ℝ)) hhpos)
  have hright : (∑ i ∈ Finset.Ico 1 h, f ((i + 1 : ℕ) : ℝ)) =
        (∑ i ∈ Finset.range h, f (i : ℝ)) + f (h : ℝ) := by
    have hs := Finset.sum_range_succ' (fun i : ℕ => f (i : ℝ)) h
    rw [Finset.sum_range_succ] at hs
    simp only [Nat.cast_zero, hf0, add_zero, hremove] at hs
    exact hs.symm
  have hmNat : MonotoneOn f (Icc ((1 : ℕ) : ℝ) (h : ℝ)) := by
    simpa only [Nat.cast_one] using hm
  have hup := MonotoneOn.sum_le_integral_Ico (f := f) hh hmNat
  have hlo := MonotoneOn.integral_le_sum_Ico (f := f) hh hmNat
  simp only [Nat.cast_one] at hup hlo
  rw [hleft] at hup
  rw [hright] at hlo
  have hi : (∫ x in (1 : ℝ)..(h : ℝ), f x) =
      (h : ℝ) ^ 2 / 2 * Real.log (h : ℝ) -
        (h : ℝ) ^ 2 / 4 + 1 / 4 := integral_mul_log_one hhR
  rw [hi] at hup hlo
  dsimp only [f] at hup hlo
  constructor <;> linarith only [hup, hlo]

end
end Li2

end
