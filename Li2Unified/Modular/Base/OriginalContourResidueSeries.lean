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

lemma original_sum_Icc_one_eq_sum_range_succ {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, f m) = ∑ k ∈ Finset.range N, f (k + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  simpa only [Nat.add_sub_cancel, Nat.add_comm 1] using
    (Finset.sum_Ico_eq_sum_range f 1 (N + 1))

end
end Li2

end
