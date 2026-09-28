module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import Li2Unified.Modular.Positive.Packed.P102

set_option backward.privateInPublic true

@[expose] public section

section
/-! The explicit logarithmic-product error is absorbed by a fixed sixth power. -/

namespace Li2Unified.Proofs.Contour
noncomputable section

theorem vertical_prefactor_poly (n : ℕ) (hn : 1 ≤ n)
    (y : ℝ) (hy : 0 ≤ y) :
    (1 + (n : ℝ) * y) *
      Real.exp (Real.log 2 - Real.log (n : ℝ) +
        (9 / 2 : ℝ) * Real.log ((n : ℝ) + 3 / 2 + (n : ℝ) * y) + 11 / 4) ≤
      (2 * Real.exp (11 / 4) * (5 / 2 : ℝ) ^ 5) *
        ((n : ℝ) + 1) ^ 6 * (1 + y) ^ 6 := by
  let B : ℝ := (n : ℝ) + 3 / 2 + (n : ℝ) * y
  let U : ℝ := ((n : ℝ) + 1) * (1 + y)
  let T : ℝ := (5 / 2 : ℝ) * U
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hny : 0 ≤ (n : ℝ) * y := mul_nonneg (by linarith) hy
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hT : B ≤ T := by dsimp [B, T, U]; nlinarith
  have ht : 1 + (n : ℝ) * y ≤ U := by dsimp [U]; nlinarith
  have hBpow : Real.exp ((9 / 2 : ℝ) * Real.log B) ≤ B ^ 5 := by
    calc
      _ ≤ Real.exp (5 * Real.log B) := Real.exp_le_exp.mpr (by
        have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
        nlinarith)
      _ = B ^ 5 := by
        rw [mul_comm, Real.exp_mul,
          Real.exp_log (lt_of_lt_of_le zero_lt_one hB)]
        norm_num
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hexp : Real.exp (Real.log 2 - Real.log (n : ℝ) + 11 / 4) ≤
      2 * Real.exp (11 / 4) := by
    calc
      _ ≤ Real.exp (Real.log 2 + 11 / 4) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hsplit : Real.exp (Real.log 2 - Real.log (n : ℝ) +
      (9 / 2 : ℝ) * Real.log B + 11 / 4) =
      Real.exp (Real.log 2 - Real.log (n : ℝ) + 11 / 4) *
        Real.exp ((9 / 2 : ℝ) * Real.log B) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change (1 + (n : ℝ) * y) * Real.exp (Real.log 2 - Real.log (n : ℝ) +
    (9 / 2 : ℝ) * Real.log B + 11 / 4) ≤
    (2 * Real.exp (11 / 4) * (5 / 2 : ℝ) ^ 5) *
      ((n : ℝ) + 1) ^ 6 * (1 + y) ^ 6
  rw [hsplit]
  calc
    (1 + (n : ℝ) * y) *
        (Real.exp (Real.log 2 - Real.log (n : ℝ) + 11 / 4) *
          Real.exp ((9 / 2 : ℝ) * Real.log B)) ≤
      U * ((2 * Real.exp (11 / 4)) * B ^ 5) := by gcongr
    _ ≤ U * ((2 * Real.exp (11 / 4)) * T ^ 5) := by gcongr
    _ = _ := by dsimp [T, U]; ring

end
end Li2Unified.Proofs.Contour

end

section
/-! Both actual vertical arms satisfy one all-n sixth-power weight estimate. -/

open Polynomial MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

def verticalWeightConstant : ℝ :=
  (Real.log 2 + 2 * Real.pi) *
    (2 * Real.exp (11 / 4) * (5 / 2 : ℝ) ^ 5)

private lemma vertical_exp_bound_to_poly (n : ℕ) (hn : 1 ≤ n)
    (y : ℝ) (hy : 0 ≤ y) (W : ℝ)
    (hW : W ≤ (Real.log 2 + 2 * Real.pi) *
      (1 + (n : ℝ) * y) *
      Real.exp ((n : ℝ) * Vvertical y + Real.log 2 - Real.log (n : ℝ) +
        (9 / 2 : ℝ) * Real.log ((n : ℝ) + 3 / 2 + (n : ℝ) * y) + 11 / 4)) :
    W ≤ verticalWeightConstant * ((n : ℝ) + 1) ^ 6 *
      (1 + y) ^ 6 * Real.exp ((n : ℝ) * Vvertical y) := by
  let E : ℝ := Real.log 2 - Real.log (n : ℝ) +
    (9 / 2 : ℝ) * Real.log ((n : ℝ) + 3 / 2 + (n : ℝ) * y) + 11 / 4
  have hc : 0 ≤ Real.log 2 + 2 * Real.pi := by positivity
  have hsplit : Real.exp ((n : ℝ) * Vvertical y + Real.log 2 -
      Real.log (n : ℝ) +
      (9 / 2 : ℝ) * Real.log ((n : ℝ) + 3 / 2 + (n : ℝ) * y) + 11 / 4) =
      Real.exp ((n : ℝ) * Vvertical y) * Real.exp E := by
    rw [← Real.exp_add]
    congr 1
    dsimp [E]
    ring
  have hpoly := vertical_prefactor_poly n hn y hy
  change (1 + (n : ℝ) * y) * Real.exp E ≤
    (2 * Real.exp (11 / 4) * (5 / 2 : ℝ) ^ 5) *
      ((n : ℝ) + 1) ^ 6 * (1 + y) ^ 6 at hpoly
  calc
    W ≤ (Real.log 2 + 2 * Real.pi) * (1 + (n : ℝ) * y) *
        (Real.exp ((n : ℝ) * Vvertical y) * Real.exp E) := by
      simpa only [hsplit] using! hW
    _ = (Real.log 2 + 2 * Real.pi) *
        ((1 + (n : ℝ) * y) * Real.exp E) *
        Real.exp ((n : ℝ) * Vvertical y) := by ring
    _ ≤ (Real.log 2 + 2 * Real.pi) *
        ((2 * Real.exp (11 / 4) * (5 / 2 : ℝ) ^ 5) *
          ((n : ℝ) + 1) ^ 6 * (1 + y) ^ 6) *
        Real.exp ((n : ℝ) * Vvertical y) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly hc)
        (Real.exp_nonneg _)
    _ = _ := by unfold verticalWeightConstant; ring

theorem normalized_up_density_poly_bound (n : ℕ) (hn : 1 ≤ n)
    (y : ℝ) (hy : 0 ≤ y) :
    (Li2.Sn n : ℝ) * ‖density ⟨1, by decide⟩ ((n : ℝ) * y) *
      Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3)
        (point ⟨1, by decide⟩ ((n : ℝ) * y))‖ ≤
      verticalWeightConstant * ((n : ℝ) + 1) ^ 6 *
        (1 + y) ^ 6 * Real.exp ((n : ℝ) * Vvertical y) := by
  apply vertical_exp_bound_to_poly n hn y hy
  exact normalized_up_density_exp_bound n hn y hy

theorem normalized_down_density_poly_bound (n : ℕ) (hn : 1 ≤ n)
    (y : ℝ) (hy : 0 ≤ y) :
    (Li2.Sn n : ℝ) * ‖density ⟨2, by decide⟩ ((n : ℝ) * y) *
      Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3)
        (point ⟨2, by decide⟩ ((n : ℝ) * y))‖ ≤
      verticalWeightConstant * ((n : ℝ) + 1) ^ 6 *
        (1 + y) ^ 6 * Real.exp ((n : ℝ) * Vvertical y) := by
  apply vertical_exp_bound_to_poly n hn y hy
  exact normalized_down_density_exp_bound n hn y hy

theorem up_density_uniform_bound (n : ℕ) (hn : 1 ≤ n)
    (t : ℝ) (ht : 0 ≤ t) :
    (Li2.Sn n : ℝ) * ‖density ⟨1, by decide⟩ t *
      Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3)
        (point ⟨1, by decide⟩ t)‖ ≤
      verticalWeightConstant * ((n : ℝ) + 1) ^ 6 *
        (1 + t / (n : ℝ)) ^ 6 *
          Real.exp ((n : ℝ) * Vvertical (t / (n : ℝ))) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hy : 0 ≤ t / (n : ℝ) := div_nonneg ht hnR
  have h := normalized_up_density_poly_bound n hn (t / (n : ℝ)) hy
  have hty : (n : ℝ) * (t / (n : ℝ)) = t := mul_div_cancel₀ t hn0
  simpa only [hty] using! h

theorem down_density_uniform_bound (n : ℕ) (hn : 1 ≤ n)
    (t : ℝ) (ht : 0 ≤ t) :
    (Li2.Sn n : ℝ) * ‖density ⟨2, by decide⟩ t *
      Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3)
        (point ⟨2, by decide⟩ t)‖ ≤
      verticalWeightConstant * ((n : ℝ) + 1) ^ 6 *
        (1 + t / (n : ℝ)) ^ 6 *
          Real.exp ((n : ℝ) * Vvertical (t / (n : ℝ))) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hy : 0 ≤ t / (n : ℝ) := div_nonneg ht hnR
  have h := normalized_down_density_poly_bound n hn (t / (n : ℝ)) hy
  have hty : (n : ℝ) * (t / (n : ℝ)) = t := mul_div_cancel₀ t hn0
  simpa only [hty] using! h

end
end Li2Unified.Proofs.Contour

end


end
