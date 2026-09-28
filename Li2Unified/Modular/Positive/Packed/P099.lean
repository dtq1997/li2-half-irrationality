module
public import Li2Unified.Modular.Positive.Packed.P097
public import Li2Unified.Modular.Positive.Packed.P098
public import Li2Unified.Modular.Positive.Packed.P073
public import Li2Unified.Modular.Base.OriginalSnLogBounds
public import Li2Unified.Modular.Base.OriginalContourHorizontalTails
public import Mathlib.Tactic

set_option backward.privateInPublic true

@[expose] public section

section
/-! The actual normalized positive-real product has the frozen ray potential
with a fully explicit logarithmic error. -/

open Polynomial MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

theorem ray_scaled_product_log_upper (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : 0 < x) :
    let t : ℝ := (n : ℝ) * x
    Real.log (Li2.Sn n : ℝ) +
      3 * Real.log ‖(Li2.D n).eval₂ (Rat.castHom ℂ) (t : ℂ)‖ -
      Real.log ‖(Li2.D (4 * n)).eval₂ (Rat.castHom ℂ) (t : ℂ)‖ ≤
      (n : ℝ) * baseRay x + Real.log 2 - Real.log (n : ℝ) - 7 / 4 +
        3 * Real.log (t + (n : ℝ)) - 3 * Real.log t := by
  dsimp only
  let t : ℝ := (n : ℝ) * x
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have ht : 0 < t := mul_pos hnR hx
  have hnum := (originalD_log_real_bounds n t ht).2
  have hden := (originalD_log_real_bounds (4 * n) t ht).1
  have hSn := (Li2.originalSn_log_error_bounds n hn).2
  have hI1 := integral_log_shift_scale n hn x 1 hx (by norm_num)
  have hI4 := integral_log_shift_scale n hn x 4 hx (by norm_num)
  simp only [mul_one] at hI1
  have hc : (((4 * n : ℕ) : ℝ)) = (n : ℝ) * 4 := by push_cast; ring
  rw [hc] at hden
  dsimp [t] at hnum hden
  simp_rw [add_comm x] at hI1 hI4
  dsimp [baseRay]
  nlinarith only [hnum, hden, hSn, hI1, hI4]

end
end Li2Unified.Proofs.Contour

end

section
/-! An all-n exponential upper bound for the actual positive-ray product. -/

open Polynomial MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

theorem ray_ratio_exp_bound (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : 0 < x) (ht : (1 / 2 : ℝ) ≤ (n : ℝ) * x) :
    let t : ℝ := (n : ℝ) * x
    let A : ℝ := (Li2.Sn n : ℝ) *
      ‖(Li2.D n).eval₂ (Rat.castHom ℂ) (t : ℂ)‖ ^ 3 /
      ‖(Li2.D (4 * n)).eval₂ (Rat.castHom ℂ) (t : ℂ)‖
    A * Real.exp (-Real.log 2 * t) ≤
      Real.exp ((n : ℝ) * Vray x +
        2 * Real.log (n : ℝ) + 3 * Real.log (1 + x) +
        4 * Real.log 2 - 7 / 4) := by
  dsimp only
  let t : ℝ := (n : ℝ) * x
  let A : ℝ := (Li2.Sn n : ℝ) *
    ‖(Li2.D n).eval₂ (Rat.castHom ℂ) (t : ℂ)‖ ^ 3 /
    ‖(Li2.D (4 * n)).eval₂ (Rat.castHom ℂ) (t : ℂ)‖
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have htpos : 0 < t := by dsimp [t]; linarith
  have hS : 0 < (Li2.Sn n : ℝ) := by exact_mod_cast Li2.Sn_pos n
  have hD (m : ℕ) : 0 < ‖(Li2.D m).eval₂ (Rat.castHom ℂ) (t : ℂ)‖ := by
    have hd := Li2.D_eval₂_complex_norm_ge_one_of_re_nonneg m
      (z := (t : ℂ)) (by simp [htpos.le])
    linarith
  have hA : 0 < A := div_pos (mul_pos hS (pow_pos (hD n) 3)) (hD (4 * n))
  have hlog : Real.log A = Real.log (Li2.Sn n : ℝ) +
      3 * Real.log ‖(Li2.D n).eval₂ (Rat.castHom ℂ) (t : ℂ)‖ -
      Real.log ‖(Li2.D (4 * n)).eval₂ (Rat.castHom ℂ) (t : ℂ)‖ := by
    dsimp only [A]
    rw [Real.log_div (mul_ne_zero hS.ne' (pow_ne_zero 3 (hD n).ne'))
      (hD (4 * n)).ne', Real.log_mul hS.ne' (pow_ne_zero 3 (hD n).ne'),
      Real.log_pow]
    norm_num
  have hraw := ray_scaled_product_log_upper n hn x hx
  change Real.log (Li2.Sn n : ℝ) +
      3 * Real.log ‖(Li2.D n).eval₂ (Rat.castHom ℂ) (t : ℂ)‖ -
      Real.log ‖(Li2.D (4 * n)).eval₂ (Rat.castHom ℂ) (t : ℂ)‖ ≤
      (n : ℝ) * baseRay x + Real.log 2 - Real.log (n : ℝ) - 7 / 4 +
        3 * Real.log (t + (n : ℝ)) - 3 * Real.log t at hraw
  rw [← hlog] at hraw
  have htp : t + (n : ℝ) = (n : ℝ) * (1 + x) := by dsimp [t]; ring
  have hx1 : 0 < 1 + x := by linarith
  rw [htp, Real.log_mul hnR.ne' hx1.ne'] at hraw
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    simp [one_div, Real.log_inv]
  have hlow : -Real.log 2 ≤ Real.log t := by
    rw [← hhalf]
    exact Real.log_le_log (by norm_num) (by simpa only [t] using ht)
  have hscalar : Real.log A - Real.log 2 * t ≤
      (n : ℝ) * Vray x + 2 * Real.log (n : ℝ) +
        3 * Real.log (1 + x) + 4 * Real.log 2 - 7 / 4 := by
    dsimp [Vray]
    dsimp [t] at *
    nlinarith only [hraw, hlow]
  have he := Real.exp_le_exp.mpr hscalar
  rw [show Real.log A - Real.log 2 * t =
      Real.log A + -(Real.log 2 * t) by ring,
    Real.exp_add, Real.exp_log hA] at he
  simpa [t, A, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using he

end
end Li2Unified.Proofs.Contour

end

section
/-! Exact exponentiation of the logarithmic ray error. -/

namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

lemma ray_exp_error_to_poly (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : 0 ≤ x) :
    Real.exp ((n : ℝ) * Vray x + 2 * Real.log (n : ℝ) +
      3 * Real.log (1 + x) + 4 * Real.log 2 - 7 / 4) =
      (16 * Real.exp (-7 / 4)) * (n : ℝ) ^ 2 *
        (1 + x) ^ 3 * Real.exp ((n : ℝ) * Vray x) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hx1 : 0 < 1 + x := by linarith
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hE : (n : ℝ) * Vray x + 2 * Real.log (n : ℝ) +
      3 * Real.log (1 + x) + 4 * Real.log 2 - 7 / 4 =
      (n : ℝ) * Vray x + (-7 / 4) +
      Real.log (n : ℝ) + Real.log (n : ℝ) +
      Real.log (1 + x) + Real.log (1 + x) + Real.log (1 + x) +
      Real.log 2 + Real.log 2 + Real.log 2 + Real.log 2 := by ring
  rw [hE]
  simp only [Real.exp_add, Real.exp_log hnR, Real.exp_log hx1,
    Real.exp_log htwo]
  ring

end
end Li2Unified.Proofs.Contour

end

section
/-! The ray parameter starts at one half; its extra linear factor still fits
the uniform sixth-power polynomial allowance. -/

namespace Li2Unified.Proofs.Contour
noncomputable section

lemma ray_prefactor_poly (n : ℕ) (hn : 1 ≤ n)
    (u : ℝ) (hu : 0 ≤ u) :
    (n : ℝ) ^ 2 * (1 / 2 + u) *
        (1 + (1 / 2 + u) / (n : ℝ)) ^ 3 ≤
      8 * ((n : ℝ) + 1) ^ 6 * (1 + u / (n : ℝ)) ^ 6 := by
  let N : ℝ := n
  let Y : ℝ := 1 + u / N
  let X : ℝ := 1 + (1 / 2 + u) / N
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hNne : N ≠ 0 := ne_of_gt hN0
  have hY : 1 ≤ Y := by
    dsimp [Y]
    have hdiv : 0 ≤ u / N := div_nonneg hu hN0.le
    linarith
  have hY0 : 0 ≤ Y := by linarith
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hNY : N * Y = N + u := by dsimp [Y]; field_simp
  have hX : X = Y + (1 / 2 : ℝ) / N := by dsimp [X, Y]; ring
  have hsmall : (1 / 2 : ℝ) / N ≤ 1 := by
    apply (div_le_iff₀ hN0).2
    linarith
  have hXle : X ≤ 2 * Y := by rw [hX]; linarith
  have ht : 1 / 2 + u ≤ (N + 1) * Y := by
    nlinarith only [hNY, hN, hY]
  have hNle : N ≤ N + 1 := by linarith
  change N ^ 2 * (1 / 2 + u) * X ^ 3 ≤
    8 * (N + 1) ^ 6 * Y ^ 6
  calc
    N ^ 2 * (1 / 2 + u) * X ^ 3 ≤
        (N + 1) ^ 2 * ((N + 1) * Y) * (2 * Y) ^ 3 := by
      gcongr
    _ = 8 * (N + 1) ^ 3 * Y ^ 4 := by ring
    _ ≤ 8 * (N + 1) ^ 6 * Y ^ 6 := by
      gcongr <;> linarith

end
end Li2Unified.Proofs.Contour

end


end
