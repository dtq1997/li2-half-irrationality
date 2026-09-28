module
public import Li2Unified.Modular.Positive.Packed.P042
public import Li2Unified.Modular.Positive.Packed.P071
public import Li2Unified.Modular.Base.OriginalContourResidueSeries

set_option backward.privateInPublic true

@[expose] public section

section
/-! The residue series of the positive-half upper kernel is the literal
`numeratorFunctional` at the positive-half value. -/

open Polynomial Filter
open scoped Topology BigOperators
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf

lemma positive_residueTerm_ofReal (d : ℕ) (F : ℚ[X])
    (m : ℕ) (hm : 0 < m) :
    (1 / 2 : ℂ) ^ m * deriv (Li2.originalContourG d F) (m : ℂ) =
      (((1 / 2 : ℝ) ^ m *
        deriv (fun y : ℝ => y * Li2.originalRealQuotient d F y) (m : ℝ) : ℝ) : ℂ) := by
  have hbase : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [Complex.ofReal_mul, Complex.ofReal_pow, hbase]
  congr 1
  simpa only [Complex.ofReal_natCast] using!
    (Li2.originalContourG_deriv_ofReal d F (x := (m : ℝ)) (by exact_mod_cast hm))

theorem hasSum_positive_residues (d : ℕ) (F : ℚ[X]) :
    HasSum (fun k : ℕ => (1 / 2 : ℂ) ^ (k + 1) *
      deriv (Li2.originalContourG d F) ((k + 1 : ℕ) : ℂ))
      (((numeratorFunctional lambda d F).eval₂ (Rat.castHom ℝ) value : ℝ) : ℂ) := by
  have hr : HasSum
      (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1) *
        deriv (fun y : ℝ => y * Li2.originalRealQuotient d F y) ((k : ℝ) + 1))
      ((numeratorFunctional lambda d F).eval₂ (Rat.castHom ℝ) value) := by
    rw [value, numeratorFunctional_real_derivative_series lambda lambda_abs_lt_one
      lambda_nonzero]
    simpa only [lambda, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using!
      (summable_originalRealQuotient_derivative lambda lambda_abs_lt_one d F).hasSum
  have hc := Complex.hasSum_ofReal.mpr hr
  apply hc.congr_fun
  intro k
  simpa only [Nat.cast_add, Nat.cast_one] using!
    positive_residueTerm_ofReal d F (k + 1) (by omega)

theorem numeratorFunctional_positive_complex_derivative_series (d : ℕ) (F : ℚ[X]) :
    (numeratorFunctional lambda d F).eval₂ (Rat.castHom ℂ) (value : ℂ) =
      ∑' k : ℕ, (1 / 2 : ℂ) ^ (k + 1) *
        deriv (Li2.originalContourG d F) ((k + 1 : ℕ) : ℂ) := by
  rw [Li2.originalComplexEval_ofReal]
  exact (hasSum_positive_residues d F).tsum_eq.symm

theorem tendsto_positive_residueSum (d : ℕ) (F : ℚ[X]) :
    Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.Icc 1 N,
        (1 / 2 : ℂ) ^ m * deriv (Li2.originalContourG d F) (m : ℂ)) atTop
      (𝓝 ((numeratorFunctional lambda d F).eval₂ (Rat.castHom ℂ) (value : ℂ))) := by
  have he :
      (fun N : ℕ => ∑ m ∈ Finset.Icc 1 N,
        (1 / 2 : ℂ) ^ m * deriv (Li2.originalContourG d F) (m : ℂ)) =
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        (1 / 2 : ℂ) ^ (k + 1) *
          deriv (Li2.originalContourG d F) ((k + 1 : ℕ) : ℂ)) := by
    funext N
    exact Li2.original_sum_Icc_one_eq_sum_range_succ _ N
  rw [he, Li2.originalComplexEval_ofReal]
  exact (hasSum_positive_residues d F).tendsto_sum_nat

end
end Li2Unified.Proofs.Contour

end


end
