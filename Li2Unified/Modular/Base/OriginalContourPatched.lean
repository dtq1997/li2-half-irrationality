module
public import Li2Unified.Modular.Base.OriginalContourCompensated
public import Li2Unified.Modular.Base.RectangleResidueFinite
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

set_option backward.privateInPublic true

@[expose] public section

open Polynomial Filter Set MeasureTheory
open scoped Topology BigOperators Interval
namespace Li2
noncomputable section

def originalKernelFiniteRawRemainder (S : Finset ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  originalContourKernel z * f z -
    ∑ m ∈ S, ((-1 / 2 : ℂ) ^ m * f (m : ℂ)) / (z - (m : ℂ))

/-- Only the values at the listed poles are changed. -/
def originalKernelFinitePatchedRemainder (S : Finset ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  originalKernelFiniteRawRemainder S f z +
    ∑ m ∈ S, if z = (m : ℂ) then
      originalKernelFiniteLocalRemainder S m f z - originalKernelFiniteRawRemainder S f z
      else 0

lemma originalKernelFinitePatchedRemainder_eq_raw (S : Finset ℕ) (f : ℂ → ℂ)
    {z : ℂ} (hz : ∀ m ∈ S, z ≠ (m : ℂ)) :
    originalKernelFinitePatchedRemainder S f z = originalKernelFiniteRawRemainder S f z := by
  unfold originalKernelFinitePatchedRemainder
  have hs : (∑ m ∈ S, if z = (m : ℂ) then
      originalKernelFiniteLocalRemainder S m f z - originalKernelFiniteRawRemainder S f z
      else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    exact if_neg (hz m hm)
  rw [hs, add_zero]

lemma originalKernelFinitePatchedRemainder_nat (S : Finset ℕ) (f : ℂ → ℂ)
    (m : ℕ) (hm : m ∈ S) :
    originalKernelFinitePatchedRemainder S f (m : ℂ) =
      originalKernelFiniteLocalRemainder S m f (m : ℂ) := by
  unfold originalKernelFinitePatchedRemainder
  rw [Finset.sum_eq_single_of_mem m hm]
  · rw [if_pos rfl]
    ring
  · intro j hj hjm
    have hne : (m : ℂ) ≠ (j : ℂ) := by exact_mod_cast Ne.symm hjm
    exact if_neg hne

lemma originalKernelFinitePatchedRemainder_eventuallyEq_raw (S : Finset ℕ)
    (f : ℂ → ℂ) {z : ℂ} (hz : ∀ m ∈ S, z ≠ (m : ℂ)) :
    originalKernelFinitePatchedRemainder S f =ᶠ[𝓝 z] originalKernelFiniteRawRemainder S f := by
  have he : ∀ᶠ w : ℂ in 𝓝 z, ∀ m ∈ S, w ≠ (m : ℂ) :=
    (Filter.eventually_all_finset S).mpr (fun m hm => eventually_ne_nhds (hz m hm))
  filter_upwards [he] with w hw
  exact originalKernelFinitePatchedRemainder_eq_raw S f hw

lemma originalKernelFinitePatchedRemainder_eventuallyEq_local (S : Finset ℕ)
    (f : ℂ → ℂ) (m : ℕ) (hm : m ∈ S) :
    originalKernelFinitePatchedRemainder S f =ᶠ[𝓝 (m : ℂ)]
      originalKernelFiniteLocalRemainder S m f := by
  have he : ∀ᶠ z : ℂ in 𝓝 (m : ℂ), ∀ j ∈ S.erase m, z ≠ (j : ℂ) := by
    apply (Filter.eventually_all_finset (S.erase m)).mpr
    intro j hj
    apply eventually_ne_nhds
    exact_mod_cast Ne.symm (Finset.ne_of_mem_erase hj)
  filter_upwards [he] with z hz
  by_cases hzm : z = (m : ℂ)
  · subst z
    exact originalKernelFinitePatchedRemainder_nat S f m hm
  · have hn : ∀ j ∈ S, z ≠ (j : ℂ) := by
      intro j hj
      by_cases hjm : j = m
      · simpa only [hjm] using hzm
      · exact hz j (Finset.mem_erase.mpr ⟨hjm, hj⟩)
    rw [originalKernelFinitePatchedRemainder_eq_raw S f hn,
      originalKernelFiniteLocalRemainder_eq S m f hm hzm]
    rfl

lemma analyticAt_originalKernelFinitePatchedRemainder_nat (S : Finset ℕ)
    (f : ℂ → ℂ) (m : ℕ) (hm : m ∈ S) (hf : AnalyticAt ℂ f (m : ℂ)) :
    AnalyticAt ℂ (originalKernelFinitePatchedRemainder S f) (m : ℂ) :=
  (analyticAt_originalKernelFiniteLocalRemainder S m f hf).congr
    (originalKernelFinitePatchedRemainder_eventuallyEq_local S f m hm).symm

lemma analyticAt_originalContourKernel_of_sin_ne_zero {z : ℂ}
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    AnalyticAt ℂ originalContourKernel z := by
  have hn : Differentiable ℂ (fun w : ℂ => (Real.pi : ℂ) * originalContourPower w) := by
    unfold originalContourPower
    fun_prop
  have hs : Differentiable ℂ (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) := by
    fun_prop
  exact (hn.analyticAt z).div (hs.analyticAt z) hz

lemma analyticAt_originalKernelFinitePatchedRemainder_off_poles (S : Finset ℕ)
    (f : ℂ → ℂ) {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hs : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    AnalyticAt ℂ (originalKernelFinitePatchedRemainder S f) z := by
  have hn : ∀ m ∈ S, z ≠ (m : ℂ) := by
    intro m hm he
    subst z
    exact hs (originalContour_sin_nat m)
  have hr : AnalyticAt ℂ (originalKernelFiniteRawRemainder S f) z := by
    apply ((analyticAt_originalContourKernel_of_sin_ne_zero hs).mul hf).sub
    apply S.analyticAt_fun_sum
    intro m hm
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (hn m hm))
  exact hr.congr (originalKernelFinitePatchedRemainder_eventuallyEq_raw S f hn).symm

lemma originalContour_sineZero_in_Icc (N : ℕ) {z : ℂ}
    (hz : 0 < z.re) (hzN : z.re < (N : ℝ) + 1)
    (hs : Complex.sin ((Real.pi : ℂ) * z) = 0) :
    ∃ m ∈ Finset.Icc 1 N, z = (m : ℂ) := by
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hzk : z = (k : ℂ) := by
    apply mul_left_cancel₀ hpi
    exact hk.trans (mul_comm _ _)
  have hkR : (0 : ℝ) < (k : ℝ) := by
    simpa only [hzk, Complex.intCast_re] using hz
  have hkpos : 0 < k := by exact_mod_cast hkR
  let m : ℕ := k.toNat
  have hmk : (m : ℤ) = k := Int.toNat_of_nonneg hkpos.le
  have hmkC : (m : ℂ) = (k : ℂ) := by exact_mod_cast hmk
  have hzm : z = (m : ℂ) := hzk.trans hmkC.symm
  have hmR : (0 : ℝ) < (m : ℝ) := by
    simpa only [hzm, Complex.natCast_re] using hz
  have hmpos : 0 < m := by exact_mod_cast hmR
  have hmNR : (m : ℝ) < ((N + 1 : ℕ) : ℝ) := by
    simpa only [hzm, Complex.natCast_re, Nat.cast_add, Nat.cast_one] using hzN
  have hmN : m < N + 1 := by exact_mod_cast hmNR
  exact ⟨m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hzm⟩

lemma rectangle_continuousOn_horizontal_intervalIntegrable
    {h : ℂ → ℂ} {a b : ℂ}
    (hh : ContinuousOn h ([[a.re, b.re]] ×ℂ [[a.im, b.im]]))
    {c : ℝ} (hc : c ∈ [[a.im, b.im]]) :
    IntervalIntegrable (fun x : ℝ => h ((x : ℂ) + (c : ℂ) * Complex.I))
      volume a.re b.re := by
  have hp : Continuous (fun x : ℝ => (x : ℂ) + (c : ℂ) * Complex.I) := by fun_prop
  apply ContinuousOn.intervalIntegrable
  apply hh.comp hp.continuousOn
  intro x hx
  simpa [Complex.mem_reProdIm] using And.intro hx hc

lemma rectangle_continuousOn_vertical_intervalIntegrable
    {h : ℂ → ℂ} {a b : ℂ}
    (hh : ContinuousOn h ([[a.re, b.re]] ×ℂ [[a.im, b.im]]))
    {c : ℝ} (hc : c ∈ [[a.re, b.re]]) :
    IntervalIntegrable (fun y : ℝ => h ((c : ℂ) + (y : ℂ) * Complex.I))
      volume a.im b.im := by
  have hp : Continuous (fun y : ℝ => (c : ℂ) + (y : ℂ) * Complex.I) := by fun_prop
  apply ContinuousOn.intervalIntegrable
  apply hh.comp hp.continuousOn
  intro y hy
  simpa [Complex.mem_reProdIm] using And.intro hc hy

end
end Li2

end
