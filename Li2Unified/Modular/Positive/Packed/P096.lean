module
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Algebra.BigOperators.Intervals
public import Li2Unified.Modular.Base.AndreiefIntegrable
public import Li2Unified.Modular.Base.Andreief
public import Li2Unified.Modular.Base.OriginalContourFiniteRectangle
public import Li2Unified.Modular.Base.OriginalContourHorizontalTails
public import Li2Unified.Modular.Base.OriginalContourRightActual
public import Li2Unified.Modular.Base.OriginalContourResidueSeries
public import Li2Unified.Modular.Base.OriginalRealDerivative
public import Li2Unified.Modular.Base.Gram
public import Li2Unified.Modular.Base.DecayNormalization
public import Mathlib.Data.Complex.BigOperators
public import Li2Unified.Modular.Positive.Packed.P073
public import Li2Unified.Modular.Positive.Packed.P095

set_option backward.privateInPublic true

@[expose] public section

section
/-! The exact complex Vandermonde scaling for mixed star-contour configurations. -/

open Polynomial MeasureTheory
open scoped BigOperators
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

def scaledPoint (n : ℕ) (b : Fin 3) (y : ℝ) : ℂ :=
  point b ((n : ℝ) * y) / (n : ℂ)

lemma point_eq_nat_mul_scaledPoint (n : ℕ) (hn : 1 ≤ n)
    (b : Fin 3) (y : ℝ) :
    point b ((n : ℝ) * y) = (n : ℂ) * scaledPoint n b y := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  unfold scaledPoint
  exact (mul_div_cancel₀ _ hn0).symm

theorem star_vandermonde_norm_sq_scale (h n : ℕ)
    (x : Fin h → ℂ) :
    ‖(Matrix.of fun i j : Fin h => ((n : ℂ) * x j) ^ i.val).det‖ ^ 2 =
      (n : ℝ) ^ (h * (h - 1)) *
        ‖(Matrix.of fun i j : Fin h => (x j) ^ i.val).det‖ ^ 2 := by
  have hm : Matrix.vandermonde (fun i : Fin h => (n : ℂ) * x i) =
      Matrix.of (fun i j : Fin h =>
        (n : ℂ) ^ j.val * Matrix.vandermonde x i j) := by
    ext i j
    simp only [Matrix.vandermonde_apply, Matrix.of_apply, mul_pow]
  have hd : (Matrix.vandermonde (fun i : Fin h => (n : ℂ) * x i)).det =
      (n : ℂ) ^ (∑ j : Fin h, j.val) * (Matrix.vandermonde x).det := by
    rw [hm, Matrix.det_mul_row, Finset.prod_pow_eq_pow_sum]
  have hcount : (∑ j : Fin h, j.val) * 2 = h * (h - 1) := by
    have hs := Finset.sum_range_id_mul_two h
    rw [← Fin.sum_univ_eq_sum_range] at hs
    exact hs
  have hsquare := congrArg (fun z : ℂ => ‖z‖ ^ 2) hd
  rw [norm_mul, norm_pow, mul_pow, ← pow_mul, hcount] at hsquare
  have hnorm : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  rw [hnorm] at hsquare
  change ‖((Matrix.vandermonde (fun i : Fin h => (n : ℂ) * x i)).transpose).det‖ ^ 2 =
    (n : ℝ) ^ (h * (h - 1)) * ‖((Matrix.vandermonde x).transpose).det‖ ^ 2
  simpa only [Matrix.det_transpose] using! hsquare

theorem star_vandermonde_point_scale (n : ℕ) (hn : 1 ≤ n)
    (v : Fin (2 * n) → Fin 3 × ℝ) :
    ‖(Matrix.of fun i j : Fin (2 * n) =>
        (point (v j).1 ((n : ℝ) * (v j).2)) ^ i.val).det‖ ^ 2 =
      (n : ℝ) ^ ((2 * n) * (2 * n - 1)) *
        ‖(Matrix.of fun i j : Fin (2 * n) =>
          (scaledPoint n (v j).1 (v j).2) ^ i.val).det‖ ^ 2 := by
  simp_rw [point_eq_nat_mul_scaledPoint n hn]
  exact star_vandermonde_norm_sq_scale (2 * n) n
    (fun j => scaledPoint n (v j).1 (v j).2)

end
end Li2Unified.Proofs.Contour

end

section
/-! The three scaled stars are a common half-step translation of the
unshifted ray and the two imaginary half-lines. -/

namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

lemma scaledPoint_ray (n : ℕ) (hn : 1 ≤ n) (y : ℝ) :
    scaledPoint n ⟨0, by decide⟩ y =
      (1 / 2 : ℂ) / (n : ℂ) + (y : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  unfold scaledPoint
  rw [point_ray]
  push_cast
  field_simp

lemma scaledPoint_up (n : ℕ) (hn : 1 ≤ n) (y : ℝ) :
    scaledPoint n ⟨1, by decide⟩ y =
      (1 / 2 : ℂ) / (n : ℂ) + (y : ℂ) * Complex.I := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  unfold scaledPoint
  rw [point_up]
  unfold Li2.originalContourPoint
  push_cast
  field_simp

lemma scaledPoint_down (n : ℕ) (hn : 1 ≤ n) (y : ℝ) :
    scaledPoint n ⟨2, by decide⟩ y =
      (1 / 2 : ℂ) / (n : ℂ) - (y : ℂ) * Complex.I := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  unfold scaledPoint
  rw [point_down]
  unfold Li2.originalContourPoint
  push_cast
  field_simp
  ring

end
end Li2Unified.Proofs.Contour

end

section
/-! The common half-step shift disappears from every logarithmic pair kernel. -/

namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

lemma scaledPoint_sub_shift (n : ℕ) (hn : 1 ≤ n)
    (b : Fin 3) (y : ℝ) :
    scaledPoint n b y - (1 / 2 : ℂ) / (n : ℂ) =
      point b y - (1 / 2 : ℂ) := by
  fin_cases b
  · rw [scaledPoint_ray n hn, point_ray]
    push_cast
    ring
  · rw [scaledPoint_up n hn, point_up]
    unfold Li2.originalContourPoint
    ring
  · rw [scaledPoint_down n hn, point_down]
    unfold Li2.originalContourPoint
    push_cast
    ring

theorem scaledPoint_pair_difference (n : ℕ) (hn : 1 ≤ n)
    (b c : Fin 3) (y s : ℝ) :
    scaledPoint n b y - scaledPoint n c s = point b y - point c s := by
  have hb := scaledPoint_sub_shift n hn b y
  have hc := scaledPoint_sub_shift n hn c s
  calc
    scaledPoint n b y - scaledPoint n c s =
        (scaledPoint n b y - (1 / 2 : ℂ) / (n : ℂ)) -
          (scaledPoint n c s - (1 / 2 : ℂ) / (n : ℂ)) := by ring
    _ = (point b y - (1 / 2 : ℂ)) -
          (point c s - (1 / 2 : ℂ)) := by rw [hb, hc]
    _ = point b y - point c s := by ring

end
end Li2Unified.Proofs.Contour

end

section
open scoped BigOperators
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HalfAnalytic
open Li2Unified.Instances.PosHalf.LayerComparison
open Li2Unified.Proofs.Contour

/-- The common translation centers the three rescaled arms at the origin. -/
def starAxisPoint (v : Fin 3 × ℝ) : ℂ := point v.1 v.2 - (1/2:ℂ)

lemma star_scaled_axis_difference (n : ℕ) (hn : 1 ≤ n)
    (u v : Fin 3 × ℝ) :
    scaledPoint n u.1 u.2 - scaledPoint n v.1 v.2 =
      starAxisPoint u - starAxisPoint v := by
  rw [scaledPoint_pair_difference n hn]
  unfold starAxisPoint
  ring

/-- The actual rescaled Vandermonde, conditional only on the independent
discrete logarithmic energy estimate. -/
theorem star_vandermonde_discrete_energy (n : ℕ) (hn : 1 ≤ n)
    (v : Fin (2*n) → Fin 3 × ℝ)
    (henergy : Function.Injective (fun i => starAxisPoint (v i)) →
      2 * (∑ i : Fin (2*n),
        ∑ j ∈ Finset.Ioi i,
          Real.log ‖starAxisPoint (v j) - starAxisPoint (v i)‖) ≤
        4*(n:ℝ) * (∑ i : Fin (2*n), comparisonPotential (starAxisPoint (v i))) -
          4*(n:ℝ)^2 * comparisonEnergy +
          2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) :
    ‖(Matrix.of fun i j : Fin (2*n) =>
      scaledPoint n (v j).1 (v j).2 ^ i.val).det‖ ^ 2 ≤
      Real.exp (4*(n:ℝ) *
          (∑ i : Fin (2*n), comparisonPotential (starAxisPoint (v i))) -
        4*(n:ℝ)^2 * comparisonEnergy +
        2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) := by
  apply complex_vandermonde_bound
  intro hx
  have haxis : Function.Injective (fun i => starAxisPoint (v i)) := by
    intro i j hij
    apply hx
    have hdiff := star_scaled_axis_difference n hn (v i) (v j)
    apply sub_eq_zero.mp
    rw [hdiff]
    exact sub_eq_zero.mpr hij
  calc
    2 * (∑ i : Fin (2*n), ∑ j ∈ Finset.Ioi i,
        Real.log ‖scaledPoint n (v j).1 (v j).2 -
          scaledPoint n (v i).1 (v i).2‖) =
      2 * (∑ i : Fin (2*n), ∑ j ∈ Finset.Ioi i,
        Real.log ‖starAxisPoint (v j) - starAxisPoint (v i)‖) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [star_scaled_axis_difference n hn]
    _ ≤ _ := henergy haxis

/-- Restore the exact scale factor from the original point Vandermonde. -/
theorem star_vandermonde_original_energy (n : ℕ) (hn : 1 ≤ n)
    (v : Fin (2*n) → Fin 3 × ℝ)
    (henergy : Function.Injective (fun i => starAxisPoint (v i)) →
      2 * (∑ i : Fin (2*n),
        ∑ j ∈ Finset.Ioi i,
          Real.log ‖starAxisPoint (v j) - starAxisPoint (v i)‖) ≤
        4*(n:ℝ) * (∑ i : Fin (2*n), comparisonPotential (starAxisPoint (v i))) -
          4*(n:ℝ)^2 * comparisonEnergy +
          2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) :
    ‖(Matrix.of fun i j : Fin (2*n) =>
      point (v j).1 ((n:ℝ)*(v j).2) ^ i.val).det‖ ^ 2 ≤
      (n:ℝ)^((2*n)*(2*n-1)) *
        Real.exp (4*(n:ℝ) *
            (∑ i : Fin (2*n), comparisonPotential (starAxisPoint (v i))) -
          4*(n:ℝ)^2 * comparisonEnergy +
          2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) := by
  rw [star_vandermonde_point_scale n hn v]
  exact mul_le_mul_of_nonneg_left
    (star_vandermonde_discrete_energy n hn v henergy) (by positivity)

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.star_scaled_axis_difference
#print axioms Li2Unified.Proofs.Arithmetic.star_vandermonde_discrete_energy
#print axioms Li2Unified.Proofs.Arithmetic.star_vandermonde_original_energy

end


end
