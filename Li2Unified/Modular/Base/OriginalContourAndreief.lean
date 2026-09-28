module
public import Li2Unified.Modular.Base.Andreief
public import Li2Unified.Modular.Base.OriginalContourRepresentation
public import Li2Unified.Modular.Base.OriginalRealDeterminant
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Algebra.BigOperators.Intervals

set_option backward.privateInPublic true

@[expose] public section

open Polynomial MeasureTheory
open scoped BigOperators
namespace Li2
noncomputable section

def originalContourDensity (n : ℕ) (y : ℝ) : ℂ :=
  originalContourWeight y *
    (((D n).eval₂ (Rat.castHom ℂ) (originalContourPoint y)) ^ 3 /
      (D (4 * n)).eval₂ (Rat.castHom ℂ) (originalContourPoint y))

lemma originalContour_monomial_product (n : ℕ) (i j : Fin (2 * n)) (y : ℝ) :
    originalContourPoint y ^ i.val *
        (originalContourDensity n y * originalContourPoint y ^ j.val) =
      originalContourWeight y *
        (originalContourPoint y ^ (i.val + j.val) *
          ((D n).eval₂ (Rat.castHom ℂ) (originalContourPoint y)) ^ 3 /
          (D (4 * n)).eval₂ (Rat.castHom ℂ) (originalContourPoint y)) := by
  simp only [originalContourDensity, pow_add, div_eq_mul_inv]
  ring

lemma integrable_originalContour_monomial_product (n : ℕ) (i j : Fin (2 * n)) :
    Integrable (fun y : ℝ => originalContourPoint y ^ i.val *
      (originalContourDensity n y * originalContourPoint y ^ j.val)) := by
  simpa only [originalContour_monomial_product] using integrable_originalContourEntry_explicit n i j

theorem Q_originalContour_moment_det (n : ℕ) :
    (Q n).eval₂ (Rat.castHom ℂ) (li2NegHalf : ℂ) =
      (Matrix.of fun i j : Fin (2 * n) => ∫ y : ℝ, originalContourPoint y ^ i.val *
          (originalContourDensity n y * originalContourPoint y ^ j.val)).det := by
  change (eval₂RingHom (Rat.castHom ℂ) (li2NegHalf : ℂ)) (Q n) = _
  rw [Q, RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  change (X * C (B n i j) + C (A n i j)).eval₂ (Rat.castHom ℂ) (li2NegHalf : ℂ) = _
  calc
    _ = (A n i j : ℂ) + (li2NegHalf : ℂ) * (B n i j : ℂ) := by
      simp only [eval₂_add, eval₂_mul, eval₂_X, eval₂_C, Rat.coe_castHom]
      ring
    _ = ∫ y : ℝ, originalContourWeight y *
        (originalContourPoint y ^ (i.val + j.val) *
          ((D n).eval₂ (Rat.castHom ℂ) (originalContourPoint y)) ^ 3 /
          (D (4 * n)).eval₂ (Rat.castHom ℂ) (originalContourPoint y)) :=
      originalContourEntry_eq_weight_integral_explicit n i j
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact (originalContour_monomial_product n i j y).symm

theorem Q_originalContour_andreief_vandermonde (n : ℕ) :
    (Q n).eval₂ (Rat.castHom ℂ) (li2NegHalf : ℂ) =
      (1 / ((2 * n).factorial : ℂ)) *
        ∫ x : Fin (2 * n) → ℝ,
          (∏ k : Fin (2 * n), originalContourDensity n (x k)) *
            (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
              (originalContourPoint (x j) - originalContourPoint (x i))) ^ 2
          ∂(Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ)) := by
  rw [Q_originalContour_moment_det]
  refine (Andreief.andreief (μ := (volume : Measure ℝ))
    (fun i : Fin (2 * n) => fun y : ℝ => originalContourPoint y ^ i.val)
    (fun i : Fin (2 * n) => fun y : ℝ => originalContourDensity n y * originalContourPoint y ^ i.val)
    (integrable_originalContour_monomial_product n)).trans ?_
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  change ((Matrix.vandermonde (fun i : Fin (2 * n) => originalContourPoint (x i))).transpose).det *
    (Matrix.of fun i j : Fin (2 * n) => originalContourDensity n (x j) *
        (Matrix.vandermonde (fun k : Fin (2 * n) => originalContourPoint (x k))).transpose i j).det = _
  rw [Matrix.det_mul_row]
  simp only [Matrix.det_transpose, Matrix.det_vandermonde]
  ring

private lemma originalContour_index_sum (n : ℕ) :
    (∑ i : Fin (2 * n), i.val) = n * (2 * n - 1) := by
  have h := Finset.sum_range_id_mul_two (2 * n)
  rw [← Fin.sum_univ_eq_sum_range] at h
  nlinarith

lemma originalContour_vandermonde_det (n : ℕ) (x : Fin (2 * n) → ℝ) :
    (Matrix.vandermonde (fun i : Fin (2 * n) => originalContourPoint (x i))).det =
      Complex.I ^ (n * (2 * n - 1)) *
        (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, ((x j - x i : ℝ) : ℂ)) := by
  have hz : (fun i : Fin (2 * n) => originalContourPoint (x i)) =
      (fun i => (x i : ℂ) * Complex.I + (1 / 2 : ℂ)) := by
    funext i
    unfold originalContourPoint
    ring
  rw [hz, Matrix.det_vandermonde_add]
  have hm : Matrix.vandermonde (fun i : Fin (2 * n) => (x i : ℂ) * Complex.I) =
        Matrix.of (fun i j : Fin (2 * n) => Complex.I ^ j.val *
          Matrix.vandermonde (fun k : Fin (2 * n) => (x k : ℂ)) i j) := by
    ext i j
    simp only [Matrix.vandermonde_apply, Matrix.of_apply, mul_pow]
    ring
  rw [hm, Matrix.det_mul_row, Finset.prod_pow_eq_pow_sum,
    originalContour_index_sum, Matrix.det_vandermonde]
  simp only [Complex.ofReal_sub]

lemma originalContour_vandermonde_phase (n : ℕ) :
    Complex.I ^ (2 * n * (2 * n - 1)) = (-1 : ℂ) ^ n := by
  by_cases hn : n = 0
  · simp [hn]
  have ho : Odd (2 * n - 1) := ⟨n - 1, by omega⟩
  rw [show 2 * n * (2 * n - 1) = 2 * ((2 * n - 1) * n) by ring,
    pow_mul, Complex.I_sq, pow_mul, ho.neg_one_pow]

lemma originalContour_vandermonde_sq (n : ℕ) (x : Fin (2 * n) → ℝ) :
    (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
      (originalContourPoint (x j) - originalContourPoint (x i))) ^ 2 =
      (-1 : ℂ) ^ n *
        (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, ((x j - x i : ℝ) : ℂ)) ^ 2 := by
  calc
    _ = ((Matrix.vandermonde (fun i : Fin (2 * n) => originalContourPoint (x i))).det) ^ 2 := by
      rw [Matrix.det_vandermonde]
    _ = (Complex.I ^ (n * (2 * n - 1)) *
        (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, ((x j - x i : ℝ) : ℂ))) ^ 2 :=
      congrArg (fun z : ℂ => z ^ 2) (originalContour_vandermonde_det n x)
    _ = Complex.I ^ (2 * n * (2 * n - 1)) *
        (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, ((x j - x i : ℝ) : ℂ)) ^ 2 := by
      rw [mul_pow, ← pow_mul, show (n * (2 * n - 1)) * 2 = 2 * n * (2 * n - 1) by ring]
    _ = _ := by rw [originalContour_vandermonde_phase]

theorem Q_originalContour_real_vandermonde (n : ℕ) :
    (Q n).eval₂ (Rat.castHom ℂ) (li2NegHalf : ℂ) =
      ((-1 : ℂ) ^ n / ((2 * n).factorial : ℂ)) *
        ∫ x : Fin (2 * n) → ℝ,
          (∏ k : Fin (2 * n), originalContourDensity n (x k)) *
            (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, ((x j - x i : ℝ) : ℂ)) ^ 2
          ∂(Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ)) := by
  rw [Q_originalContour_andreief_vandermonde]
  calc
    _ = (1 / ((2 * n).factorial : ℂ)) *
        ∫ x : Fin (2 * n) → ℝ, (-1 : ℂ) ^ n *
            ((∏ k : Fin (2 * n), originalContourDensity n (x k)) *
              (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, ((x j - x i : ℝ) : ℂ)) ^ 2)
          ∂(Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      rw [originalContour_vandermonde_sq]
      ring
    _ = _ := by
      refine (congrArg
        (fun z : ℂ => (1 / ((2 * n).factorial : ℂ)) * z)
        (MeasureTheory.integral_const_mul ((-1 : ℂ) ^ n)
          (fun x : Fin (2 * n) → ℝ =>
            (∏ k : Fin (2 * n), originalContourDensity n (x k)) *
              (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
                ((x j - x i : ℝ) : ℂ)) ^ 2)
          (μ := Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ)))).trans ?_
      simp only [div_eq_mul_inv]
      rw [mul_left_comm, ← mul_assoc]
      congr 1 <;> simp only [one_mul]

theorem Q_real_eval_originalContour_vandermonde (n : ℕ) :
    (((Q n).eval₂ (Rat.castHom ℝ) li2NegHalf : ℝ) : ℂ) =
      ((-1 : ℂ) ^ n / ((2 * n).factorial : ℂ)) *
        ∫ x : Fin (2 * n) → ℝ,
          (∏ k : Fin (2 * n), originalContourDensity n (x k)) *
            (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, ((x j - x i : ℝ) : ℂ)) ^ 2
          ∂(Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ)) := by
  rw [← originalComplexEval_ofReal (Q n) li2NegHalf]
  exact Q_originalContour_real_vandermonde n

end
end Li2

end
