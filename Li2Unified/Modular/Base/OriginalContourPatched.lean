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

def originalContourPatchedRemainder (d : ℕ) (F : ℚ[X]) (N : ℕ) : ℂ → ℂ :=
  originalKernelFinitePatchedRemainder (Finset.Icc 1 N) (deriv (originalContourG d F))

lemma analyticAt_originalContourPatchedRemainder (d : ℕ) (F : ℚ[X]) (N : ℕ)
    {z : ℂ} (hz : 0 < z.re) (hzN : z.re < (N : ℝ) + 1) :
    AnalyticAt ℂ (originalContourPatchedRemainder d F N) z := by
  by_cases hs : Complex.sin ((Real.pi : ℂ) * z) = 0
  · obtain ⟨m, hm, rfl⟩ := originalContour_sineZero_in_Icc N hz hzN hs
    exact analyticAt_originalKernelFinitePatchedRemainder_nat _ _ m hm
      (analyticAt_originalContourG_deriv d F hz)
  · exact analyticAt_originalKernelFinitePatchedRemainder_off_poles _ _
      (analyticAt_originalContourG_deriv d F hz) hs

lemma continuousOn_originalContourPatchedRemainder_rectangle
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (a b : ℂ)
    (ha : 0 < min a.re b.re) (hb : max a.re b.re < (N : ℝ) + 1) :
    ContinuousOn (originalContourPatchedRemainder d F N)
      ([[a.re, b.re]] ×ℂ [[a.im, b.im]]) := by
  intro z hz
  have hzr : min a.re b.re ≤ z.re ∧ z.re ≤ max a.re b.re := hz.1
  exact (analyticAt_originalContourPatchedRemainder d F N
    (lt_of_lt_of_le ha hzr.1) (lt_of_le_of_lt hzr.2 hb)).continuousAt.continuousWithinAt

lemma differentiableAt_originalContourPatchedRemainder_rectangle
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (a b : ℂ)
    (ha : 0 < min a.re b.re) (hb : max a.re b.re < (N : ℝ) + 1)
    {z : ℂ}
    (hz : z ∈ Set.Ioo (min a.re b.re) (max a.re b.re) ×ℂ
      Set.Ioo (min a.im b.im) (max a.im b.im)) :
    DifferentiableAt ℂ (originalContourPatchedRemainder d F N) z := by
  exact (analyticAt_originalContourPatchedRemainder d F N
    (lt_trans ha hz.1.1) (lt_trans hz.1.2 hb)).differentiableAt

lemma boundaryIntegral_originalContourPatchedRemainder_eq_zero
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (a b : ℂ)
    (ha : 0 < min a.re b.re) (hb : max a.re b.re < (N : ℝ) + 1) :
    Complex.boundaryIntegral (originalContourPatchedRemainder d F N) a b = 0 := by
  apply Complex.boundaryIntegral_eq_zero_of_diffOn (s := ∅) Set.countable_empty
  · exact continuousOn_originalContourPatchedRemainder_rectangle d F N a b ha hb
  · intro z hz
    exact differentiableAt_originalContourPatchedRemainder_rectangle d F N a b ha hb hz.1

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

lemma intervalIntegrable_originalContourPatchedRemainder_rectangle_edges
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (a b : ℂ)
    (ha : 0 < min a.re b.re) (hb : max a.re b.re < (N : ℝ) + 1) :
    IntervalIntegrable
      (fun x : ℝ => originalContourPatchedRemainder d F N (x + a.im * Complex.I))
      volume a.re b.re ∧
    IntervalIntegrable
      (fun x : ℝ => originalContourPatchedRemainder d F N (x + b.im * Complex.I))
      volume a.re b.re ∧
    IntervalIntegrable
      (fun y : ℝ => originalContourPatchedRemainder d F N (b.re + y * Complex.I))
      volume a.im b.im ∧
    IntervalIntegrable
      (fun y : ℝ => originalContourPatchedRemainder d F N (a.re + y * Complex.I))
      volume a.im b.im := by
  have hc := continuousOn_originalContourPatchedRemainder_rectangle d F N a b ha hb
  exact ⟨rectangle_continuousOn_horizontal_intervalIntegrable hc left_mem_uIcc,
    rectangle_continuousOn_horizontal_intervalIntegrable hc right_mem_uIcc,
    rectangle_continuousOn_vertical_intervalIntegrable hc right_mem_uIcc,
    rectangle_continuousOn_vertical_intervalIntegrable hc left_mem_uIcc⟩

def originalContourPatchedIntegrand (d : ℕ) (F : ℚ[X]) (N : ℕ) (z : ℂ) : ℂ :=
  (∑ m ∈ Finset.Icc 1 N,
    ((-1 / 2 : ℂ) ^ m * deriv (originalContourG d F) (m : ℂ)) * (z - (m : ℂ))⁻¹) +
    originalContourPatchedRemainder d F N z

lemma originalContourPatchedIntegrand_eq_off_poles
    (d : ℕ) (F : ℚ[X]) (N : ℕ) {z : ℂ}
    (hz : ∀ m ∈ Finset.Icc 1 N, z ≠ (m : ℂ)) :
    originalContourPatchedIntegrand d F N z =
      originalContourKernel z * deriv (originalContourG d F) z := by
  unfold originalContourPatchedIntegrand originalContourPatchedRemainder
  rw [originalKernelFinitePatchedRemainder_eq_raw _ _ hz]
  unfold originalKernelFiniteRawRemainder
  simp only [div_eq_mul_inv]
  ring

lemma originalContourPatchedIntegrand_eq_on_rectangle_boundary
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (a b : ℂ)
    (hre : ∀ m ∈ Finset.Icc 1 N, (m : ℝ) ∈ Set.Ioo a.re b.re)
    (hbot : a.im < 0) (htop : 0 < b.im) {z : ℂ}
    (hz : z.re = a.re ∨ z.re = b.re ∨ z.im = a.im ∨ z.im = b.im) :
    originalContourPatchedIntegrand d F N z =
      originalContourKernel z * deriv (originalContourG d F) z := by
  apply originalContourPatchedIntegrand_eq_off_poles
  intro m hm he
  have hmR := hre m hm
  rw [he] at hz
  simp only [Complex.natCast_re, Complex.natCast_im] at hz
  rcases hz with h | h | h | h <;> linarith [hmR.1, hmR.2]

end
end Li2

end
