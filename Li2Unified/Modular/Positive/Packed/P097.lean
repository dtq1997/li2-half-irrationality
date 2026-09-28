module
public import Li2Unified.Modular.Positive.Packed.P073
public import Li2Unified.Modular.Base.OriginalContourRational
public import Mathlib.Analysis.SumIntegralComparisons

set_option backward.privateInPublic true

@[expose] public section

section
/-! The literal positive-real star density is exactly the expected scalar
weight times the original rational-product norm. -/

open Polynomial MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

lemma ray_power_norm_eq (t : ℝ) :
    ‖power (t : ℂ)‖ = Real.exp (-Real.log 2 * t) := by
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    simp [one_div, Real.log_inv]
  unfold power
  rw [Complex.norm_exp]
  have hre : (((Real.log (1 / 2 : ℝ) : ℂ) * (t : ℂ)).re) =
      -Real.log 2 * t := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, hlog]
  rw [hre]

theorem ray_density_original_quotient_norm (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    let t : ℝ := 1 / 2 + u
    (Li2.Sn n : ℝ) * ‖density ⟨0, by decide⟩ u *
      Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3)
        (point ⟨0, by decide⟩ u)‖ =
      (Real.log 2 * t * Real.exp (-Real.log 2 * t)) *
        ((Li2.Sn n : ℝ) *
          ‖(Li2.D n).eval₂ (Rat.castHom ℂ) (t : ℂ)‖ ^ 3 /
          ‖(Li2.D (4 * n)).eval₂ (Rat.castHom ℂ) (t : ℂ)‖) := by
  dsimp only
  let t : ℝ := 1 / 2 + u
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  change (Li2.Sn n : ℝ) * ‖((Real.log 2 : ℂ) * (t : ℂ) * power (t : ℂ)) *
    Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3) (t : ℂ)‖ = _
  simp only [Li2.originalComplexQuotient, norm_mul, norm_div, norm_pow,
    eval₂_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog, abs_of_nonneg ht, ray_power_norm_eq]
  ring

end
end Li2Unified.Proofs.Contour

end

section
/-! Exact increasing-log sum comparison for the real positive ray. -/

open Polynomial MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section

private lemma log_shift_monotoneOn (t : ℝ) (ht : 0 < t) (m : ℕ) :
    MonotoneOn (fun s : ℝ => Real.log (t + s)) (Icc 0 (m : ℝ)) := by
  intro x hx y hy hxy
  exact Real.log_le_log (by linarith [hx.1]) (by linarith)

private lemma sum_range_succ_telescope (f : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, f (i + 1)) + f 0 =
      (∑ i ∈ Finset.range m, f i) + f m := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Finset.sum_range_succ]
      linarith

private lemma shifted_log_sum_bounds (m : ℕ) (t : ℝ) (ht : 0 < t) :
    (∫ s in (0 : ℝ)..(m : ℝ), Real.log (t + s)) ≤
        ∑ i ∈ Finset.range m, Real.log (t + ((i + 1 : ℕ) : ℝ)) ∧
      (∑ i ∈ Finset.range m, Real.log (t + ((i + 1 : ℕ) : ℝ))) ≤
        (∫ s in (0 : ℝ)..(m : ℝ), Real.log (t + s)) +
          Real.log (t + (m : ℝ)) - Real.log t := by
  have hm := log_shift_monotoneOn t ht m
  have hm' : MonotoneOn (fun s : ℝ => Real.log (t + s))
      (Icc (0 : ℝ) ((0 : ℝ) + (m : ℝ))) := by
    simpa only [zero_add] using! hm
  have hlo := hm'.integral_le_sum
  have hhi := hm'.sum_le_integral
  simp only [zero_add] at hlo hhi
  have hshift :
      (∑ i ∈ Finset.range m, Real.log (t + ((i + 1 : ℕ) : ℝ))) +
        Real.log t =
      (∑ i ∈ Finset.range m, Real.log (t + (i : ℝ))) +
        Real.log (t + (m : ℝ)) := by
    simpa only [Nat.cast_zero, add_zero] using!
      (sum_range_succ_telescope (fun i : ℕ => Real.log (t + (i : ℝ))) m)
  constructor
  · simpa only [Nat.cast_succ] using! hlo
  · linarith

theorem originalD_log_real_eq_sum (m : ℕ) (t : ℝ) (ht : 0 < t) :
    Real.log ‖(Li2.D m).eval₂ (Rat.castHom ℂ) (t : ℂ)‖ =
      ∑ i ∈ Finset.range m, Real.log (t + ((i + 1 : ℕ) : ℝ)) := by
  have hnonzero : ∀ j ∈ Finset.Icc 1 m, ‖(t : ℂ) + (j : ℂ)‖ ≠ 0 := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hpos : 0 < t + (j : ℝ) := by exact_mod_cast (show (0 : ℝ) < t + (j : ℝ) by positivity)
    have hEq : (t : ℂ) + (j : ℂ) = ((t + (j : ℝ)) : ℂ) := by push_cast; ring
    rw [hEq, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos]
    exact hpos.ne'
  rw [Li2.D_eval₂_complex_product, norm_prod, Real.log_prod hnonzero]
  calc
    (∑ j ∈ Finset.Icc 1 m, Real.log ‖(t : ℂ) + (j : ℂ)‖) =
        ∑ i ∈ Finset.range m,
          Real.log ‖(t : ℂ) + (((i + 1 : ℕ) : ℝ) : ℂ)‖ := by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      simpa only [Nat.add_sub_cancel, Nat.add_comm 1] using!
        (Finset.sum_Ico_eq_sum_range
          (fun j : ℕ => Real.log ‖(t : ℂ) + (j : ℂ)‖) 1 (m + 1))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hp : 0 < t + ((i + 1 : ℕ) : ℝ) := by positivity
      have hEq : (t : ℂ) + (((i + 1 : ℕ) : ℝ) : ℂ) =
          ((t + ((i + 1 : ℕ) : ℝ)) : ℂ) := by push_cast; ring
      rw [hEq, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hp]

theorem originalD_log_real_bounds (m : ℕ) (t : ℝ) (ht : 0 < t) :
    (∫ s in (0 : ℝ)..(m : ℝ), Real.log (t + s)) ≤
      Real.log ‖(Li2.D m).eval₂ (Rat.castHom ℂ) (t : ℂ)‖ ∧
    Real.log ‖(Li2.D m).eval₂ (Rat.castHom ℂ) (t : ℂ)‖ ≤
      (∫ s in (0 : ℝ)..(m : ℝ), Real.log (t + s)) +
        Real.log (t + (m : ℝ)) - Real.log t := by
  rw [originalD_log_real_eq_sum m t ht]
  exact shifted_log_sum_bounds m t ht

end
end Li2Unified.Proofs.Contour

end


end
