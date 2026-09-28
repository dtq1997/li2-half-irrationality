module
public import Li2Unified.Modular.Base.OriginalContourResidue
public import Li2Unified.Modular.Base.OriginalContourRational
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option backward.privateInPublic true

@[expose] public section

open Polynomial Filter Set
open scoped Topology BigOperators
namespace Li2
noncomputable section

lemma D_eval₂_complex_ne_zero_of_re_pos (d : ℕ) {z : ℂ} (hz : 0 < z.re) :
    (D d).eval₂ (Rat.castHom ℂ) z ≠ 0 := by
  rw [D_eval₂_complex_product]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj he
  have hp : 0 < (z + (j : ℂ)).re := by
    simpa only [Complex.add_re, Complex.natCast_re] using
      add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg j)
  have heR : (z + (j : ℂ)).re = 0 := by
    simpa only [Complex.zero_re] using congrArg Complex.re he
  exact (ne_of_gt hp) heR

lemma analyticAt_originalComplexEval (F : ℚ[X]) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => F.eval₂ (Rat.castHom ℂ) w) z := by
  simpa only [Polynomial.eval₂_eq_eval_map] using
    ((F.map (Rat.castHom ℂ)).differentiable.analyticAt z)

lemma analyticAt_originalComplexQuotient (d : ℕ) (F : ℚ[X])
    {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (originalComplexQuotient d F) z := by
  exact (analyticAt_originalComplexEval F z).div
    (analyticAt_originalComplexEval (D d) z)
    (D_eval₂_complex_ne_zero_of_re_pos d hz)

def originalContourG (d : ℕ) (F : ℚ[X]) (z : ℂ) : ℂ :=
  z * originalComplexQuotient d F z

lemma analyticAt_originalContourG (d : ℕ) (F : ℚ[X])
    {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (originalContourG d F) z := by
  exact analyticAt_id.mul (analyticAt_originalComplexQuotient d F hz)

lemma analyticAt_originalContourG_deriv (d : ℕ) (F : ℚ[X])
    {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (deriv (originalContourG d F)) z :=
  (analyticAt_originalContourG d F hz).deriv

lemma analyticAt_complex_dslope {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) : AnalyticAt ℂ (dslope f c) c := by
  obtain ⟨s, hs, hfs⟩ := hf.exists_mem_nhds_analyticOnNhd
  exact ((Complex.differentiableOn_dslope hs).2 hfs.differentiableOn).analyticAt hs

/-- Analytic extension after removing the simple principal part. -/
def originalKernelCompensated (m : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  dslope (fun w : ℂ => originalKernelRegularized m w * f w) (m : ℂ) z

lemma analyticAt_originalKernelCompensated (m : ℕ) (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f (m : ℂ)) :
    AnalyticAt ℂ (originalKernelCompensated m f) (m : ℂ) := by
  exact analyticAt_complex_dslope ((analyticAt_originalKernelRegularized m).mul hf)

lemma originalKernelCompensated_eq (m : ℕ) (f : ℂ → ℂ)
    {z : ℂ} (hz : z ≠ (m : ℂ)) :
    originalKernelCompensated m f z = originalContourKernel z * f z -
      ((-1 / 2 : ℂ) ^ m * f (m : ℂ)) / (z - (m : ℂ)) := by
  unfold originalKernelCompensated
  rw [dslope_of_ne _ hz, slope_def_field]
  change (originalKernelRegularized m z * f z -
    originalKernelRegularized m (m : ℂ) * f (m : ℂ)) / (z - (m : ℂ)) = _
  rw [originalKernelRegularized_eq m z hz, originalKernelRegularized_nat]
  field_simp [sub_ne_zero.mpr hz] <;> ring

lemma originalKernelCompensated_nat (m : ℕ) (f : ℂ → ℂ) :
    originalKernelCompensated m f (m : ℂ) =
      deriv (fun w : ℂ => originalKernelRegularized m w * f w) (m : ℂ) := by
  exact dslope_same _ _

lemma originalKernelCompensated_eventuallyEq (m : ℕ) (f : ℂ → ℂ) :
    originalKernelCompensated m f =ᶠ[𝓝[≠] (m : ℂ)]
      (fun z : ℂ => originalContourKernel z * f z -
        ((-1 / 2 : ℂ) ^ m * f (m : ℂ)) / (z - (m : ℂ))) := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact originalKernelCompensated_eq m f hz

def originalContourDerivativeCompensated (d : ℕ) (F : ℚ[X]) (m : ℕ) : ℂ → ℂ :=
  originalKernelCompensated m (deriv (originalContourG d F))

lemma analyticAt_originalContourDerivativeCompensated (d : ℕ) (F : ℚ[X])
    (m : ℕ) (hm : 0 < m) :
    AnalyticAt ℂ (originalContourDerivativeCompensated d F m) (m : ℂ) := by
  apply analyticAt_originalKernelCompensated
  apply analyticAt_originalContourG_deriv
  simpa only [Complex.natCast_re] using (show (0 : ℝ) < (m : ℝ) by exact_mod_cast hm)

lemma originalContourDerivativeCompensated_eq (d : ℕ) (F : ℚ[X]) (m : ℕ)
    {z : ℂ} (hz : z ≠ (m : ℂ)) :
    originalContourDerivativeCompensated d F m z =
      originalContourKernel z * deriv (originalContourG d F) z -
        ((-1 / 2 : ℂ) ^ m * deriv (originalContourG d F) (m : ℂ)) /
          (z - (m : ℂ)) :=
  originalKernelCompensated_eq m (deriv (originalContourG d F)) hz

/-- Local extension near m after subtracting all finite principal parts. -/
def originalKernelFiniteLocalRemainder (S : Finset ℕ) (m : ℕ)
    (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  originalKernelCompensated m f z -
    ∑ j ∈ S.erase m, ((-1 / 2 : ℂ) ^ j * f (j : ℂ)) / (z - (j : ℂ))

lemma analyticAt_originalKernelFiniteLocalRemainder (S : Finset ℕ) (m : ℕ)
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f (m : ℂ)) :
    AnalyticAt ℂ (originalKernelFiniteLocalRemainder S m f) (m : ℂ) := by
  apply (analyticAt_originalKernelCompensated m f hf).sub
  apply (S.erase m).analyticAt_fun_sum
  intro j hj
  apply analyticAt_const.div (analyticAt_id.sub analyticAt_const)
  apply sub_ne_zero.mpr
  have hmj : m ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
  change (m : ℂ) ≠ (j : ℂ)
  exact_mod_cast hmj

lemma originalKernelFiniteLocalRemainder_eq (S : Finset ℕ) (m : ℕ)
    (f : ℂ → ℂ) (hm : m ∈ S) {z : ℂ} (hz : z ≠ (m : ℂ)) :
    originalKernelFiniteLocalRemainder S m f z =
      originalContourKernel z * f z -
        ∑ j ∈ S, ((-1 / 2 : ℂ) ^ j * f (j : ℂ)) / (z - (j : ℂ)) := by
  rw [originalKernelFiniteLocalRemainder, originalKernelCompensated_eq m f hz,
    ← Finset.add_sum_erase S
      (fun j => ((-1 / 2 : ℂ) ^ j * f (j : ℂ)) / (z - (j : ℂ))) hm]
  ring

lemma analyticAt_originalContourFiniteLocalRemainder (d : ℕ) (F : ℚ[X])
    (S : Finset ℕ) (m : ℕ) (hm : 0 < m) :
    AnalyticAt ℂ
      (originalKernelFiniteLocalRemainder S m (deriv (originalContourG d F))) (m : ℂ) := by
  apply analyticAt_originalKernelFiniteLocalRemainder
  apply analyticAt_originalContourG_deriv
  simpa only [Complex.natCast_re] using (show (0 : ℝ) < (m : ℝ) by exact_mod_cast hm)

end
end Li2

end
