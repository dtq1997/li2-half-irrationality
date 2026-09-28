module
public import Li2Unified.Modular.Positive.Packed.P073
public import Li2Unified.Modular.Positive.Packed.P094
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Complex.BigOperators

set_option backward.privateInPublic true

@[expose] public section

section
open MeasureTheory
open scoped BigOperators
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

/-- Change variables on the actual finite product measure, using only almost-everywhere
strong measurability of the partition density. -/
theorem star_integral_scale_pi (h : ℕ) (c : ℝ) (hc : 0 < c)
    (f : (Fin h → Fin 3 × ℝ) → ℝ)
    (hf : Integrable f (Measure.pi fun _ : Fin h => contourMeasure)) :
    (∫ v, f v ∂(Measure.pi fun _ : Fin h => contourMeasure)) =
      c ^ h * (∫ v, f (fun i => Proofs.Measure.starScale c (v i))
        ∂(Measure.pi fun _ : Fin h => contourMeasure)) := by
  have hm : Measurable (fun v : Fin h → Fin 3 × ℝ =>
      fun i => Proofs.Measure.starScale c (v i)) := by
    unfold Proofs.Measure.starScale
    fun_prop
  have hmap : Measure.map (fun v : Fin h → Fin 3 × ℝ =>
      fun i => Proofs.Measure.starScale c (v i))
      (Measure.pi fun _ : Fin h => contourMeasure) ≪
      (Measure.pi fun _ : Fin h => contourMeasure) := by
    rw [Proofs.Measure.starScale_pi_map h c hc]
    exact Measure.smul_absolutelyContinuous
  have hi := integral_map hm.aemeasurable (hf.aestronglyMeasurable.mono_ac hmap)
    (μ := Measure.pi fun _ : Fin h => contourMeasure)
  rw [Proofs.Measure.starScale_pi_map h c hc, integral_smul_measure] at hi
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal (inv_nonneg.mpr hc.le),
    smul_eq_mul] at hi
  rw [← hi, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc.ne', one_pow, one_mul]

/-- The exact original integrand, before any analytic majorization. -/
def starPartitionDensity (n : ℕ) (v : Fin (2*n) → Fin 3 × ℝ) : ℝ :=
  ‖(Matrix.of fun i j : Fin (2*n) =>
      point (v j).1 (v j).2 ^ i.val).det‖ ^ 2 *
    (∏ i : Fin (2*n), ‖density (v i).1 (v i).2 *
      Li2.originalComplexQuotient (4*n) ((Li2.D n)^3)
        (point (v i).1 (v i).2)‖)

theorem starPartition_scaled (n : ℕ) (hn : 1 ≤ n) :
    starPartition n = (n:ℝ) ^ (2*n) *
      (∫ v : Fin (2*n) → Fin 3 × ℝ,
        starPartitionDensity n
          (fun i => Proofs.Measure.starScale (n:ℝ) (v i))
        ∂(Measure.pi fun _ : Fin (2*n) => contourMeasure)) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  exact star_integral_scale_pi (2*n) (n:ℝ) hnpos
    (starPartitionDensity n) (by
      simpa only [starPartitionDensity] using
        Proofs.Contour.star_partition_integrable n)

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.star_integral_scale_pi
#print axioms Li2Unified.Proofs.Arithmetic.starPartition_scaled

end

section
open scoped BigOperators
namespace Li2Unified.Proofs.Arithmetic
noncomputable section

theorem complex_vandermonde_norm_sq_eq_exp {h : ℕ} (x : Fin h → ℂ)
    (hx : Function.Injective x) :
    ‖(Matrix.of fun i j : Fin h => (x j)^i.val).det‖^2 =
      Real.exp (2*(∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log ‖x j-x i‖)) := by
  have hfactor {i j : Fin h} (hij : j ∈ Finset.Ioi i) : ‖x j-x i‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    apply sub_ne_zero.mpr
    intro he
    exact (ne_of_gt (Finset.mem_Ioi.mp hij)) (hx he)
  have hrow (i : Fin h) : (∏ j ∈ Finset.Ioi i, ‖x j-x i‖) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j hj => hfactor hj)
  have hprod : (∏ i : Fin h, ∏ j ∈ Finset.Ioi i, ‖x j-x i‖) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hrow i)
  have hlog : Real.log (∏ i : Fin h, ∏ j ∈ Finset.Ioi i, ‖x j-x i‖) =
      ∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log ‖x j-x i‖ := by
    rw [Real.log_prod (fun i _ => hrow i)]
    apply Finset.sum_congr rfl
    intro i _
    exact Real.log_prod (fun j hj => hfactor hj)
  change ‖((Matrix.vandermonde x).transpose).det‖^2 = _
  rw [Matrix.det_transpose, Matrix.det_vandermonde]
  simp_rw [norm_prod]
  rw [← hlog]
  have he := Real.exp_log (sq_pos_of_ne_zero hprod)
  rw [Real.log_pow] at he
  norm_num only [Nat.cast_ofNat] at he
  exact he.symm

theorem complex_vandermonde_zero_of_not_injective {h : ℕ} (x : Fin h → ℂ)
    (hx : ¬ Function.Injective x) :
    (Matrix.of fun i j : Fin h => (x j)^i.val).det = 0 := by
  change ((Matrix.vandermonde x).transpose).det = 0
  rw [Matrix.det_transpose]
  by_contra hn
  exact hx (Matrix.det_vandermonde_ne_zero_iff.mp hn)

theorem complex_vandermonde_bound {h : ℕ} (x : Fin h → ℂ) (B : ℝ)
    (hB : Function.Injective x →
      2*(∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log ‖x j-x i‖) ≤ B) :
    ‖(Matrix.of fun i j : Fin h => (x j)^i.val).det‖^2 ≤ Real.exp B := by
  by_cases hx : Function.Injective x
  · rw [complex_vandermonde_norm_sq_eq_exp x hx]
    exact Real.exp_le_exp.mpr (hB hx)
  · rw [complex_vandermonde_zero_of_not_injective x hx, norm_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact (Real.exp_pos B).le

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.complex_vandermonde_norm_sq_eq_exp
#print axioms Li2Unified.Proofs.Arithmetic.complex_vandermonde_zero_of_not_injective
#print axioms Li2Unified.Proofs.Arithmetic.complex_vandermonde_bound

end


end
