module
public import Li2Unified.Modular.Positive.Packed.P097
public import Li2Unified.Modular.Positive.Packed.P099

set_option backward.privateInPublic true

@[expose] public section

section
/-! The actual positive-real arm satisfies the all-n sixth-power bound. -/

open Polynomial MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

def rayWeightConstant : ℝ := 128 * Real.log 2 * Real.exp (-7 / 4)

theorem ray_density_uniform_bound (n : ℕ) (hn : 1 ≤ n)
    (u : ℝ) (hu : 0 ≤ u) :
    (Li2.Sn n : ℝ) * ‖density ⟨0, by decide⟩ u *
      Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3)
        (point ⟨0, by decide⟩ u)‖ ≤
      rayWeightConstant * ((n : ℝ) + 1) ^ 6 *
        (1 + u / (n : ℝ)) ^ 6 *
        Real.exp ((n : ℝ) * Vray ((1 / 2 + u) / (n : ℝ))) := by
  let t : ℝ := 1 / 2 + u
  let x : ℝ := t / (n : ℝ)
  let A : ℝ := (Li2.Sn n : ℝ) *
    ‖(Li2.D n).eval₂ (Rat.castHom ℂ) (t : ℂ)‖ ^ 3 /
    ‖(Li2.D (4 * n)).eval₂ (Rat.castHom ℂ) (t : ℂ)‖
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have ht : 0 < t := by dsimp [t]; linarith
  have hx : 0 < x := div_pos ht hnR
  have htx : (n : ℝ) * x = t := by dsimp [x]; exact mul_div_cancel₀ t hn0
  have hhalf : (1 / 2 : ℝ) ≤ (n : ℝ) * x := by rw [htx]; dsimp [t]; linarith
  have hratio := ray_ratio_exp_bound n hn x hx hhalf
  dsimp only at hratio
  rw [htx] at hratio
  change A * Real.exp (-Real.log 2 * t) ≤
    Real.exp ((n : ℝ) * Vray x + 2 * Real.log (n : ℝ) +
      3 * Real.log (1 + x) + 4 * Real.log 2 - 7 / 4) at hratio
  rw [ray_exp_error_to_poly n hn x hx.le] at hratio
  have hden := ray_density_original_quotient_norm n u hu
  change (Li2.Sn n : ℝ) * ‖density ⟨0, by decide⟩ u *
      Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3)
        (point ⟨0, by decide⟩ u)‖ =
      (Real.log 2 * t * Real.exp (-Real.log 2 * t)) * A at hden
  have hp := ray_prefactor_poly n hn u hu
  change (n : ℝ) ^ 2 * t * (1 + x) ^ 3 ≤
      8 * ((n : ℝ) + 1) ^ 6 * (1 + u / (n : ℝ)) ^ 6 at hp
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfactor : 0 ≤ Real.log 2 * t := mul_nonneg hlog ht.le
  have hc : 0 ≤ 16 * Real.log 2 * Real.exp (-7 / 4) := by positivity
  calc
    (Li2.Sn n : ℝ) * ‖density ⟨0, by decide⟩ u *
        Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3)
          (point ⟨0, by decide⟩ u)‖ =
        (Real.log 2 * t) * (A * Real.exp (-Real.log 2 * t)) := by
      rw [hden]
      ring
    _ ≤ (Real.log 2 * t) *
        ((16 * Real.exp (-7 / 4)) * (n : ℝ) ^ 2 *
          (1 + x) ^ 3 * Real.exp ((n : ℝ) * Vray x)) :=
      mul_le_mul_of_nonneg_left hratio hfactor
    _ = (16 * Real.log 2 * Real.exp (-7 / 4)) *
        ((n : ℝ) ^ 2 * t * (1 + x) ^ 3) *
          Real.exp ((n : ℝ) * Vray x) := by ring
    _ ≤ (16 * Real.log 2 * Real.exp (-7 / 4)) *
        (8 * ((n : ℝ) + 1) ^ 6 * (1 + u / (n : ℝ)) ^ 6) *
          Real.exp ((n : ℝ) * Vray x) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp hc) (Real.exp_nonneg _)
    _ = rayWeightConstant * ((n : ℝ) + 1) ^ 6 *
        (1 + u / (n : ℝ)) ^ 6 *
        Real.exp ((n : ℝ) * Vray ((1 / 2 + u) / (n : ℝ))) := by
      dsimp [rayWeightConstant, x, t]
      ring

end
end Li2Unified.Proofs.Contour

end


end
