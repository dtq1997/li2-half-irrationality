module
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Algebra.BigOperators.Intervals

set_option backward.privateInPublic true

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Li2
noncomputable section

lemma integrable_pi_mul_scale_iff (h : ℕ) (c : ℝ) (hc : c ≠ 0)
    (f : (Fin h → ℝ) → ℝ) :
    Integrable (fun x : Fin h → ℝ => f (fun i => c * x i))
        (Measure.pi fun _ : Fin h => (volume : Measure ℝ)) ↔
      Integrable f (Measure.pi fun _ : Fin h => (volume : Measure ℝ)) := by
  simpa only [Pi.smul_apply, smul_eq_mul] using
    (MeasureTheory.integrable_comp_smul_iff
      (Measure.pi fun _ : Fin h => (volume : Measure ℝ)) f hc)

theorem integral_pi_mul_scale (h : ℕ) (c : ℝ) (hc : 0 < c)
    (f : (Fin h → ℝ) → ℝ) :
    (∫ x : Fin h → ℝ, f x ∂(Measure.pi fun _ : Fin h => (volume : Measure ℝ))) =
      c ^ h * (∫ x : Fin h → ℝ, f (fun i => c * x i)
        ∂(Measure.pi fun _ : Fin h => (volume : Measure ℝ))) := by
  have hi := Measure.integral_comp_inv_smul_of_nonneg
    (Measure.pi fun _ : Fin h => (volume : Measure ℝ))
    (fun x : Fin h → ℝ => f (c • x)) (R := c) hc.le
  simpa only [← mul_smul, mul_inv_cancel₀ hc.ne', one_smul,
    Module.finrank_pi, Fintype.card_fin, Pi.smul_apply, smul_eq_mul] using hi

theorem vandermonde_sq_mul_scale (h : ℕ) (c : ℝ) (x : Fin h → ℝ) :
    (∏ i : Fin h, ∏ j ∈ Finset.Ioi i, (c * x j - c * x i)) ^ 2 =
      c ^ (h * (h - 1)) *
        (∏ i : Fin h, ∏ j ∈ Finset.Ioi i, (x j - x i)) ^ 2 := by
  have hm : Matrix.vandermonde (fun i : Fin h => c * x i) =
      Matrix.of (fun i j : Fin h => c ^ j.val * Matrix.vandermonde x i j) := by
    ext i j
    simp only [Matrix.vandermonde_apply, Matrix.of_apply, mul_pow]
  have hd : (Matrix.vandermonde (fun i : Fin h => c * x i)).det =
        c ^ (∑ j : Fin h, j.val) * (Matrix.vandermonde x).det := by
    rw [hm, Matrix.det_mul_row, Finset.prod_pow_eq_pow_sum]
  have hcount : (∑ j : Fin h, j.val) * 2 = h * (h - 1) := by
    have hs := Finset.sum_range_id_mul_two h
    rw [← Fin.sum_univ_eq_sum_range] at hs
    exact hs
  have hsquare := congrArg (fun z : ℝ => z ^ 2) hd
  dsimp only at hsquare
  rw [mul_pow, ← pow_mul, hcount] at hsquare
  simpa only [Matrix.det_vandermonde] using hsquare

end
end Li2

end
