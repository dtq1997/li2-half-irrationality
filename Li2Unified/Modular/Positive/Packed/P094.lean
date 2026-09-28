module
public import Li2Unified.Modular.Positive.Packed.P093
public import Li2Unified.Modular.Positive.Packed.P072
public import Li2Unified.Modular.Base.AndreiefIntegrable
public import Mathlib.LinearAlgebra.Vandermonde
public import Li2Unified.Modular.Positive.Packed.P042
public import Li2Unified.Modular.Base.OriginalContourRational
public import Li2Unified.Modular.Base.DecayNormalization
public import Mathlib.Data.Complex.BigOperators

set_option backward.privateInPublic true

@[expose] public section

section
/-! Andréief's identity for the actual three-arm contour measure and original
positive-half numerator, before taking absolute values. -/

open Polynomial MeasureTheory Set
open scoped BigOperators
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf

def starContourDensity (n : ℕ) (v : Fin 3 × ℝ) : ℂ :=
  density v.1 v.2 *
    Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3) (point v.1 v.2)

lemma star_monomial_product (n : ℕ) (i j : Fin (2 * n)) (v : Fin 3 × ℝ) :
    point v.1 v.2 ^ i.val *
      (starContourDensity n v * point v.1 v.2 ^ j.val) =
    density v.1 v.2 * Li2.originalComplexQuotient (4 * n)
      ((Li2.D n) ^ 3 * X ^ (i.val + j.val)) (point v.1 v.2) := by
  simp only [starContourDensity, Li2.originalComplexQuotient,
    eval₂_mul, eval₂_pow, eval₂_X, pow_add, div_eq_mul_inv]
  ring

lemma integrable_star_monomial_product (n : ℕ) (i j : Fin (2 * n)) :
    Integrable (fun v : Fin 3 × ℝ => point v.1 v.2 ^ i.val *
      (starContourDensity n v * point v.1 v.2 ^ j.val)) contourMeasure := by
  simpa only [star_monomial_product] using
    actual_star_moment_integrable (4 * n)
      ((Li2.D n) ^ 3 * X ^ (i.val + j.val))

theorem Q_star_moment_det (n : ℕ) :
    (Instances.PosHalf.Q n).eval₂ (Rat.castHom ℂ) (value : ℂ) =
      (Matrix.of fun i j : Fin (2 * n) =>
        ∫ v : Fin 3 × ℝ, point v.1 v.2 ^ i.val *
          (starContourDensity n v * point v.1 v.2 ^ j.val)
          ∂contourMeasure).det := by
  have hQ : ParameterFamily.Q lambda n =
      (hankelFor (numeratorLinearMap lambda (4 * n))
        (2 * n) ((Li2.D n) ^ 3)).det := by
    rw [hankelFor_original]
    rfl
  change (eval₂RingHom (Rat.castHom ℂ) (value : ℂ)) (ParameterFamily.Q lambda n) = _
  rw [hQ, RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  change (numeratorFunctional lambda (4 * n)
    ((Li2.D n) ^ 3 * X ^ (i.val + j.val))).eval₂ (Rat.castHom ℂ) (value : ℂ) = _
  rw [actual_original_functional_star]
  unfold starMoment
  apply integral_congr_ae
  filter_upwards [] with v
  exact (star_monomial_product n i j v).symm

theorem Q_star_andreief (n : ℕ) :
    (Instances.PosHalf.Q n).eval₂ (Rat.castHom ℂ) (value : ℂ) =
      (1 / ((2 * n).factorial : ℂ)) *
        ∫ v : Fin (2 * n) → (Fin 3 × ℝ),
          (∏ k : Fin (2 * n), starContourDensity n (v k)) *
            (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
              (point (v j).1 (v j).2 - point (v i).1 (v i).2)) ^ 2
          ∂(Measure.pi fun _ : Fin (2 * n) => contourMeasure) := by
  rw [Q_star_moment_det]
  haveI : SigmaFinite (volume.restrict (Ioi (0 : ℝ))) :=
    Measure.sigmaFinite_of_le volume Measure.restrict_le_self
  haveI : SigmaFinite contourMeasure := by
    unfold contourMeasure
    infer_instance
  refine (MeasureAndreief.andreief (μ := contourMeasure)
    (fun i : Fin (2 * n) => fun v : Fin 3 × ℝ => point v.1 v.2 ^ i.val)
    (fun i : Fin (2 * n) => fun v : Fin 3 × ℝ =>
      starContourDensity n v * point v.1 v.2 ^ i.val)
    (integrable_star_monomial_product n)).trans ?_
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  change ((Matrix.vandermonde (fun i : Fin (2 * n) => point (v i).1 (v i).2)).transpose).det *
    (Matrix.of fun i j : Fin (2 * n) => starContourDensity n (v j) *
      (Matrix.vandermonde (fun k : Fin (2 * n) => point (v k).1 (v k).2)).transpose i j).det = _
  rw [Matrix.det_mul_row]
  simp only [Matrix.det_transpose, Matrix.det_vandermonde]
  ring

end
end Li2Unified.Proofs.Contour

end

section
/-! The exact positive-half normalization of the actual polynomial Q. -/

open Polynomial
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Instances.PosHalf

lemma positive_half_Qtilde_abs_scale (n : ℕ) :
    |aeval value (Qtilde n)| =
      (((Li2.Sn n ^ (2 * n) / Li2.Fn n : ℚ) : ℝ)) *
        ‖(Q n).eval₂ (Rat.castHom ℂ) (value : ℂ)‖ := by
  have hs : 0 < (((Li2.Sn n ^ (2 * n) / Li2.Fn n : ℚ) : ℝ)) := by
    exact_mod_cast Li2.Qtilde_scale_pos n
  have hq : |aeval value (Q n)| =
      ‖(Q n).eval₂ (Rat.castHom ℂ) (value : ℂ)‖ := by
    rw [Li2.originalComplexEval_ofReal, Complex.norm_real, Real.norm_eq_abs]
    rfl
  rw [← hq]
  have hC : aeval value (C (Li2.Sn n ^ (2 * n) / Li2.Fn n)) =
      (((Li2.Sn n ^ (2 * n) / Li2.Fn n : ℚ) : ℝ)) := by
    simp [aeval_def]
  rw [show Qtilde n = C (Li2.Sn n ^ (2 * n) / Li2.Fn n) * Q n by rfl,
    map_mul, hC, abs_mul, abs_of_pos hs]

end
end Li2Unified.Proofs.Contour

end

section
/-! The actual positive-half determinant integral is bounded by the
star partition function, with the original factorial and normalization. -/

open Polynomial MeasureTheory Set
open scoped BigOperators
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic
open Li2Unified.Instances.PosHalf Li2Unified.ParameterFamily

private lemma star_vandermonde_integrand_norm (n : ℕ)
    (v : Fin (2 * n) → (Fin 3 × ℝ)) :
    ‖(∏ k : Fin (2 * n), starContourDensity n (v k)) *
      (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
        (point (v j).1 (v j).2 - point (v i).1 (v i).2)) ^ 2‖ =
      ‖(Matrix.of fun i j : Fin (2 * n) =>
        point (v j).1 (v j).2 ^ i.val).det‖ ^ 2 *
      (∏ k : Fin (2 * n), ‖density (v k).1 (v k).2 *
        Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3)
          (point (v k).1 (v k).2)‖) := by
  have hv : (Matrix.of fun i j : Fin (2 * n) =>
      point (v j).1 (v j).2 ^ i.val).det =
      ∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
        (point (v j).1 (v j).2 - point (v i).1 (v i).2) := by
    change ((Matrix.vandermonde
      (fun j : Fin (2 * n) => point (v j).1 (v j).2)).transpose).det = _
    rw [Matrix.det_transpose, Matrix.det_vandermonde]
  rw [hv, norm_mul, norm_pow, norm_prod]
  simp only [starContourDensity]
  ring

theorem integrable_star_vandermonde (n : ℕ) :
    Integrable (fun v : Fin (2 * n) → (Fin 3 × ℝ) =>
      (∏ k : Fin (2 * n), starContourDensity n (v k)) *
        (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
          (point (v j).1 (v j).2 - point (v i).1 (v i).2)) ^ 2)
      (Measure.pi fun _ : Fin (2 * n) => contourMeasure) := by
  haveI : SigmaFinite (volume.restrict (Ioi (0 : ℝ))) :=
    Measure.sigmaFinite_of_le volume Measure.restrict_le_self
  haveI : SigmaFinite contourMeasure := by
    unfold contourMeasure
    infer_instance
  have h := Li2.Andreief.integrable_det_mul_det
    (μ := contourMeasure)
    (fun i : Fin (2 * n) => fun v : Fin 3 × ℝ => point v.1 v.2 ^ i.val)
    (fun i : Fin (2 * n) => fun v : Fin 3 × ℝ =>
      starContourDensity n v * point v.1 v.2 ^ i.val)
    (integrable_star_monomial_product n)
  refine h.congr ?_
  filter_upwards [] with v
  change ((Matrix.vandermonde
    (fun i : Fin (2 * n) => point (v i).1 (v i).2)).transpose).det *
    (Matrix.of fun i j : Fin (2 * n) => starContourDensity n (v j) *
      (Matrix.vandermonde
        (fun k : Fin (2 * n) => point (v k).1 (v k).2)).transpose i j).det = _
  rw [Matrix.det_mul_row]
  simp only [Matrix.det_transpose, Matrix.det_vandermonde]
  ring

theorem star_partition_integrable (n : ℕ) :
    Integrable (fun v : Fin (2 * n) → (Fin 3 × ℝ) =>
      ‖(Matrix.of fun i j : Fin (2 * n) =>
        point (v j).1 (v j).2 ^ i.val).det‖ ^ 2 *
      (∏ k : Fin (2 * n), ‖density (v k).1 (v k).2 *
        Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3)
          (point (v k).1 (v k).2)‖))
      (Measure.pi fun _ : Fin (2 * n) => contourMeasure) := by
  simpa only [star_vandermonde_integrand_norm] using
    (integrable_star_vandermonde n).norm

theorem Q_star_partition_bound (n : ℕ) :
    ‖(Instances.PosHalf.Q n).eval₂ (Rat.castHom ℂ) (value : ℂ)‖ ≤
      (1 / ((2 * n).factorial : ℝ)) * starPartition n := by
  have hnorm := congrArg (fun z : ℂ => ‖z‖) (Q_star_andreief n)
  dsimp only at hnorm
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast] at hnorm
  rw [hnorm]
  refine (mul_le_mul_of_nonneg_left
    (norm_integral_le_integral_norm
      (μ := Measure.pi fun _ : Fin (2 * n) => contourMeasure)
      (fun v : Fin (2 * n) → (Fin 3 × ℝ) =>
        (∏ k : Fin (2 * n), starContourDensity n (v k)) *
          (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i,
            (point (v j).1 (v j).2 - point (v i).1 (v i).2)) ^ 2))
    (by positivity : (0 : ℝ) ≤ 1 / ((2 * n).factorial : ℝ))).trans_eq ?_
  congr 1
  unfold starPartition
  apply integral_congr_ae
  filter_upwards [] with v
  exact star_vandermonde_integrand_norm n v

theorem actual_Qtilde_star_bound (n : ℕ) :
    |aeval value (Instances.PosHalf.Qtilde n)| ≤
      (((Li2.Sn n ^ (2 * n) / Li2.Fn n : ℚ) : ℝ) /
        ((2 * n).factorial : ℝ)) * starPartition n := by
  have hs : 0 < ((Li2.Sn n : ℝ) ^ (2 * n) / (Li2.Fn n : ℝ)) := by
    exact_mod_cast Li2.Qtilde_scale_pos n
  rw [positive_half_Qtilde_abs_scale]
  have hQ := mul_le_mul_of_nonneg_left (Q_star_partition_bound n) hs.le
  simpa only [Rat.cast_div, Rat.cast_pow] using
    (hQ.trans_eq (by ring :
      ((Li2.Sn n : ℝ) ^ (2 * n) / (Li2.Fn n : ℝ)) *
        ((1 / ((2 * n).factorial : ℝ)) * starPartition n) =
      (((Li2.Sn n : ℝ) ^ (2 * n) / (Li2.Fn n : ℝ)) /
        ((2 * n).factorial : ℝ)) * starPartition n))

end
end Li2Unified.Proofs.Contour

end


end
