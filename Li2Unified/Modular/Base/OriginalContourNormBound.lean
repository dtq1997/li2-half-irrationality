module
public import Li2Unified.Modular.Base.OriginalContourAndreiefIntegrable
public import Li2Unified.Modular.Base.DecayNormalization
public import Mathlib.Data.Complex.BigOperators

set_option backward.privateInPublic true

@[expose] public section

open Polynomial MeasureTheory
open scoped BigOperators

namespace Li2
noncomputable section

private lemma originalContour_real_vandermonde_integrand_norm
    (n : ℕ) (x : Fin (2 * n) → ℝ) :
    ‖(∏ k : Fin (2 * n), originalContourDensity n (x k)) *
        (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
          ((x j - x i : ℝ) : ℂ)) ^ 2‖ =
      (∏ k : Fin (2 * n), ‖originalContourDensity n (x k)‖) *
        (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
          (x j - x i)) ^ 2 := by
  have hv :
      (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
        ((x j - x i : ℝ) : ℂ)) =
      ((∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
        (x j - x i) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_prod]
  rw [norm_mul, norm_prod, hv, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem integrable_originalContour_norm_vandermonde (n : ℕ) :
    Integrable
      (fun x : Fin (2 * n) → ℝ =>
        (∏ k : Fin (2 * n), ‖originalContourDensity n (x k)‖) *
          (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
            (x j - x i)) ^ 2)
      (Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ)) := by
  simpa only [originalContour_real_vandermonde_integrand_norm] using!
    (integrable_originalContour_real_vandermonde n).norm

theorem Q_real_eval_abs_le_originalContour_norm_integral (n : ℕ) :
    |(Q n).eval₂ (Rat.castHom ℝ) li2NegHalf| ≤
      (1 / ((2 * n).factorial : ℝ)) *
        ∫ x : Fin (2 * n) → ℝ,
          (∏ k : Fin (2 * n), ‖originalContourDensity n (x k)‖) *
            (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
              (x j - x i)) ^ 2
          ∂(Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ)) := by
  have hnorm := congrArg (fun z : ℂ => ‖z‖)
    (Q_real_eval_originalContour_vandermonde n)
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_div,
    norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast] at hnorm
  rw [hnorm]
  refine (mul_le_mul_of_nonneg_left
      (norm_integral_le_integral_norm
        (μ := Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ))
        (fun x : Fin (2 * n) → ℝ =>
          (∏ k : Fin (2 * n), originalContourDensity n (x k)) *
            (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
              ((x j - x i : ℝ) : ℂ)) ^ 2))
      (by positivity : (0 : ℝ) ≤ 1 / ((2 * n).factorial : ℝ))).trans_eq ?_
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  exact originalContour_real_vandermonde_integrand_norm n x

theorem Qtilde_real_eval_abs_le_originalContour_norm_integral (n : ℕ) :
    |(Qtilde n).eval₂ (Rat.castHom ℝ) li2NegHalf| ≤
      ((Sn n : ℝ) ^ (2 * n) / (Fn n : ℝ)) *
        (1 / ((2 * n).factorial : ℝ)) *
          ∫ x : Fin (2 * n) → ℝ,
            (∏ k : Fin (2 * n), ‖originalContourDensity n (x k)‖) *
              (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
                (x j - x i)) ^ 2
            ∂(Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ)) := by
  have hs : 0 < (Sn n : ℝ) ^ (2 * n) / (Fn n : ℝ) := by
    exact_mod_cast Qtilde_scale_pos n
  calc
    _ = ((Sn n : ℝ) ^ (2 * n) / (Fn n : ℝ)) *
        |(Q n).eval₂ (Rat.castHom ℝ) li2NegHalf| := by
      simp only [Qtilde, eval₂_mul, eval₂_C, Rat.coe_castHom,
        Rat.cast_div, Rat.cast_pow, abs_mul, abs_of_pos hs]
    _ ≤ ((Sn n : ℝ) ^ (2 * n) / (Fn n : ℝ)) *
        ((1 / ((2 * n).factorial : ℝ)) *
          ∫ x : Fin (2 * n) → ℝ,
            (∏ k : Fin (2 * n), ‖originalContourDensity n (x k)‖) *
              (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
                (x j - x i)) ^ 2
            ∂(Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ))) :=
      mul_le_mul_of_nonneg_left
        (Q_real_eval_abs_le_originalContour_norm_integral n) hs.le
    _ = _ := (mul_assoc _ _ _).symm

end
end Li2

end
