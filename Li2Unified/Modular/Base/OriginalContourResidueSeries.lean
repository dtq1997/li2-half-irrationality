module
public import Li2Unified.Modular.Base.OriginalContourCompensated
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option backward.privateInPublic true

@[expose] public section

open Polynomial Filter
open scoped Topology BigOperators
namespace Li2
noncomputable section

lemma originalContourG_ofReal (d : ℕ) (F : ℚ[X]) (x : ℝ) :
    originalContourG d F (x : ℂ) = ((x * originalRealQuotient d F x : ℝ) : ℂ) := by
  unfold originalContourG
  rw [originalComplexQuotient_ofReal, Complex.ofReal_mul]

/-- The literal complex derivative agrees with the proved real derivative. -/
lemma originalContourG_deriv_ofReal (d : ℕ) (F : ℚ[X]) {x : ℝ} (hx : 0 < x) :
    deriv (originalContourG d F) (x : ℂ) =
      ((deriv (fun y : ℝ => y * originalRealQuotient d F y) x : ℝ) : ℂ) := by
  have hz : 0 < (x : ℂ).re := by simpa only [Complex.ofReal_re] using hx
  have hc := (analyticAt_originalContourG d F hz).differentiableAt.hasDerivAt.comp_ofReal
  have hc' : HasDerivAt
      (fun y : ℝ => ((y * originalRealQuotient d F y : ℝ) : ℂ))
      (deriv (originalContourG d F) (x : ℂ)) x := by
    simpa only [originalContourG_ofReal] using hc
  have hr : HasDerivAt
      (fun y : ℝ => ((y * originalRealQuotient d F y : ℝ) : ℂ))
      ((deriv (fun y : ℝ => y * originalRealQuotient d F y) x : ℝ) : ℂ) x :=
    (originalRealQuotient_hasDerivAt d F hx).differentiableAt.hasDerivAt.ofReal_comp
  exact hc'.unique hr

lemma originalContour_residueTerm_ofReal (d : ℕ) (F : ℚ[X])
    (m : ℕ) (hm : 0 < m) :
    (-1 / 2 : ℂ) ^ m * deriv (originalContourG d F) (m : ℂ) =
      (((-1 / 2 : ℝ) ^ m *
        deriv (fun y : ℝ => y * originalRealQuotient d F y) (m : ℝ) : ℝ) : ℂ) := by
  have hbase : ((-1 / 2 : ℝ) : ℂ) = (-1 / 2 : ℂ) := by norm_num
  rw [Complex.ofReal_mul, Complex.ofReal_pow, hbase]
  congr 1
  simpa only [Complex.ofReal_natCast] using
    (originalContourG_deriv_ofReal d F (x := (m : ℝ)) (by exact_mod_cast hm))

theorem hasSum_originalContour_residues (d : ℕ) (F : ℚ[X]) :
    HasSum (fun k : ℕ => (-1 / 2 : ℂ) ^ (k + 1) *
      deriv (originalContourG d F) ((k + 1 : ℕ) : ℂ))
      (((numeratorFunctional d F).eval₂ (Rat.castHom ℝ) li2NegHalf : ℝ) : ℂ) := by
  have hr : HasSum
      (fun k : ℕ => (-1 / 2 : ℝ) ^ (k + 1) *
        deriv (fun y : ℝ => y * originalRealQuotient d F y) ((k : ℝ) + 1))
      ((numeratorFunctional d F).eval₂ (Rat.castHom ℝ) li2NegHalf) := by
    rw [numeratorFunctional_real_derivative_series]
    exact (summable_originalRealQuotient_derivative d F).hasSum
  have hc := Complex.hasSum_ofReal.mpr hr
  apply hc.congr_fun
  intro k
  simpa only [Nat.cast_add, Nat.cast_one] using
    originalContour_residueTerm_ofReal d F (k + 1) (by omega)

theorem numeratorFunctional_complex_derivative_series (d : ℕ) (F : ℚ[X]) :
    (numeratorFunctional d F).eval₂ (Rat.castHom ℂ) (li2NegHalf : ℂ) =
      ∑' k : ℕ, (-1 / 2 : ℂ) ^ (k + 1) *
        deriv (originalContourG d F) ((k + 1 : ℕ) : ℂ) := by
  rw [originalComplexEval_ofReal]
  exact (hasSum_originalContour_residues d F).tsum_eq.symm

lemma original_sum_Icc_one_eq_sum_range_succ {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, f m) = ∑ k ∈ Finset.range N, f (k + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  simpa only [Nat.add_sub_cancel, Nat.add_comm 1] using
    (Finset.sum_Ico_eq_sum_range f 1 (N + 1))

theorem tendsto_originalContour_residueSum (d : ℕ) (F : ℚ[X]) :
    Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.Icc 1 N,
        (-1 / 2 : ℂ) ^ m * deriv (originalContourG d F) (m : ℂ)) atTop
      (𝓝 (((numeratorFunctional d F).eval₂ (Rat.castHom ℝ) li2NegHalf : ℝ) : ℂ)) := by
  have he :
      (fun N : ℕ => ∑ m ∈ Finset.Icc 1 N,
        (-1 / 2 : ℂ) ^ m * deriv (originalContourG d F) (m : ℂ)) =
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        (-1 / 2 : ℂ) ^ (k + 1) * deriv (originalContourG d F) ((k + 1 : ℕ) : ℂ)) := by
    funext N
    exact original_sum_Icc_one_eq_sum_range_succ _ N
  rw [he]
  exact (hasSum_originalContour_residues d F).tendsto_sum_nat

theorem tendsto_originalContour_residueSum_entry (n : ℕ) (i j : Fin (2 * n)) :
    Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.Icc 1 N, (-1 / 2 : ℂ) ^ m *
        deriv (originalContourG (4 * n) (numerator n (i.val + j.val))) (m : ℂ)) atTop
      (𝓝 ((A n i j : ℂ) + (li2NegHalf : ℂ) * (B n i j : ℂ))) := by
  have he :
      (((numeratorFunctional (4 * n) (numerator n (i.val + j.val))).eval₂
        (Rat.castHom ℝ) li2NegHalf : ℝ) : ℂ) =
      (A n i j : ℂ) + (li2NegHalf : ℂ) * (B n i j : ℂ) := by
    rw [numeratorFunctional_entry]
    simp only [eval₂_add, eval₂_C, eval₂_mul, eval₂_X, Rat.coe_castHom,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ratCast, A, B]
  have h := tendsto_originalContour_residueSum (4 * n) (numerator n (i.val + j.val))
  rw [he] at h
  exact h

end
end Li2

end
