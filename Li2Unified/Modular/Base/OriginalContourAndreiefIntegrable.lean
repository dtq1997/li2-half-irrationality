module
public import Li2Unified.Modular.Base.AndreiefIntegrable
public import Li2Unified.Modular.Base.OriginalContourAndreief

set_option backward.privateInPublic true

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Li2
noncomputable section

theorem integrable_originalContour_complex_vandermonde (n : ℕ) :
    Integrable
      (fun x : Fin (2 * n) → ℝ =>
        (∏ k : Fin (2 * n), originalContourDensity n (x k)) *
          (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
            (originalContourPoint (x j) - originalContourPoint (x i))) ^ 2)
      (Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ)) := by
  have h := Andreief.integrable_det_mul_det
    (μ := (volume : Measure ℝ))
    (fun i : Fin (2 * n) => fun y : ℝ => originalContourPoint y ^ i.val)
    (fun i : Fin (2 * n) => fun y : ℝ =>
      originalContourDensity n y * originalContourPoint y ^ i.val)
    (integrable_originalContour_monomial_product n)
  refine h.congr ?_
  filter_upwards [] with x
  change
    ((Matrix.vandermonde
      (fun i : Fin (2 * n) => originalContourPoint (x i))).transpose).det *
      (Matrix.of fun i j : Fin (2 * n) =>
        originalContourDensity n (x j) *
          (Matrix.vandermonde
            (fun k : Fin (2 * n) => originalContourPoint (x k))).transpose i j).det = _
  rw [Matrix.det_mul_row]
  simp only [Matrix.det_transpose, Matrix.det_vandermonde]
  ring

theorem integrable_originalContour_real_vandermonde (n : ℕ) :
    Integrable
      (fun x : Fin (2 * n) → ℝ =>
        (∏ k : Fin (2 * n), originalContourDensity n (x k)) *
          (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
            ((x j - x i : ℝ) : ℂ)) ^ 2)
      (Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ)) := by
  have hphase : Integrable
      (fun x : Fin (2 * n) → ℝ =>
        (-1 : ℂ) ^ n *
          ((∏ k : Fin (2 * n), originalContourDensity n (x k)) *
            (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
              ((x j - x i : ℝ) : ℂ)) ^ 2))
      (Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ)) := by
    refine (integrable_originalContour_complex_vandermonde n).congr ?_
    filter_upwards [] with x
    rw [originalContour_vandermonde_sq]
    ring
  have hc : IsUnit ((-1 : ℂ) ^ n) :=
    isUnit_iff_ne_zero.mpr (pow_ne_zero n (by norm_num))
  exact (integrable_const_mul_iff hc _).mp hphase

end
end Li2

end
