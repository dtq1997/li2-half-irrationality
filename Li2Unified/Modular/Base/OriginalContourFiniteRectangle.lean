module
public import Li2Unified.Modular.Base.OriginalContourPatched

set_option backward.privateInPublic true

@[expose] public section

open Polynomial MeasureTheory
open scoped BigOperators
namespace Li2
noncomputable section

lemma boundaryIntegral_congr_four_edges (f g : ℂ → ℂ) (a b : ℂ)
    (hb : ∀ x : ℝ, f (x + a.im * Complex.I) = g (x + a.im * Complex.I))
    (ht : ∀ x : ℝ, f (x + b.im * Complex.I) = g (x + b.im * Complex.I))
    (hr : ∀ y : ℝ, f (b.re + y * Complex.I) = g (b.re + y * Complex.I))
    (hl : ∀ y : ℝ, f (a.re + y * Complex.I) = g (a.re + y * Complex.I)) :
    Complex.boundaryIntegral f a b = Complex.boundaryIntegral g a b := by
  unfold Complex.boundaryIntegral
  rw [funext hb, funext ht, funext hr, funext hl]

theorem boundaryIntegral_originalContourKernel_mul_deriv
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (a b : ℂ)
    (ha : 0 < min a.re b.re) (hb : max a.re b.re < (N : ℝ) + 1)
    (hre : ∀ m ∈ Finset.Icc 1 N, (m : ℝ) ∈ Set.Ioo a.re b.re)
    (hbot : a.im < 0) (htop : 0 < b.im) :
    Complex.boundaryIntegral
      (fun z : ℂ => originalContourKernel z * deriv (originalContourG d F) z) a b =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ∑ m ∈ Finset.Icc 1 N, (-1 / 2 : ℂ) ^ m * deriv (originalContourG d F) (m : ℂ) := by
  let c : ℕ → ℂ := fun m => (-1 / 2 : ℂ) ^ m * deriv (originalContourG d F) (m : ℂ)
  let pp : ℂ → ℂ := fun z => ∑ m ∈ Finset.Icc 1 N, c m * (z - (m : ℂ))⁻¹
  let r : ℂ → ℂ := originalContourPatchedRemainder d F N
  have hreC : ∀ m ∈ Finset.Icc 1 N, (m : ℂ).re ∈ Set.Ioo a.re b.re := by
    simpa only [Complex.natCast_re] using hre
  have himC : ∀ m ∈ Finset.Icc 1 N, (m : ℂ).im ∈ Set.Ioo a.im b.im := by
    intro m hm
    simpa only [Complex.natCast_im] using! And.intro hbot htop
  have hpb (m : ℕ) (hm : m ∈ Finset.Icc 1 N) : IntervalIntegrable
      (fun x : ℝ => c m * ((x : ℂ) + a.im * Complex.I - (m : ℂ))⁻¹)
      volume a.re b.re :=
    ((rectangleKernel_continuous_horizontal (p := (m : ℂ))
      (ne_of_lt (himC m hm).1)).intervalIntegrable _ _).const_mul _
  have hpt (m : ℕ) (hm : m ∈ Finset.Icc 1 N) : IntervalIntegrable
      (fun x : ℝ => c m * ((x : ℂ) + b.im * Complex.I - (m : ℂ))⁻¹)
      volume a.re b.re :=
    ((rectangleKernel_continuous_horizontal (p := (m : ℂ))
      (ne_of_gt (himC m hm).2)).intervalIntegrable _ _).const_mul _
  have hpr (m : ℕ) (hm : m ∈ Finset.Icc 1 N) : IntervalIntegrable
      (fun y : ℝ => c m * (b.re + (y : ℂ) * Complex.I - (m : ℂ))⁻¹)
      volume a.im b.im :=
    ((rectangleKernel_continuous_vertical (p := (m : ℂ))
      (ne_of_gt (hreC m hm).2)).intervalIntegrable _ _).const_mul _
  have hpl (m : ℕ) (hm : m ∈ Finset.Icc 1 N) : IntervalIntegrable
      (fun y : ℝ => c m * (a.re + (y : ℂ) * Complex.I - (m : ℂ))⁻¹)
      volume a.im b.im :=
    ((rectangleKernel_continuous_vertical (p := (m : ℂ))
      (ne_of_lt (hreC m hm).1)).intervalIntegrable _ _).const_mul _
  have hsb : IntervalIntegrable (fun x : ℝ => pp (x + a.im * Complex.I))
      volume a.re b.re := by
    convert IntervalIntegrable.sum (Finset.Icc 1 N) hpb using 1
    ext x
    simp only [pp, Finset.sum_apply]
  have hst : IntervalIntegrable (fun x : ℝ => pp (x + b.im * Complex.I))
      volume a.re b.re := by
    convert IntervalIntegrable.sum (Finset.Icc 1 N) hpt using 1
    ext x
    simp only [pp, Finset.sum_apply]
  have hsr : IntervalIntegrable (fun y : ℝ => pp (b.re + y * Complex.I))
      volume a.im b.im := by
    convert IntervalIntegrable.sum (Finset.Icc 1 N) hpr using 1
    ext x
    simp only [pp, Finset.sum_apply]
  have hsl : IntervalIntegrable (fun y : ℝ => pp (a.re + y * Complex.I))
      volume a.im b.im := by
    convert IntervalIntegrable.sum (Finset.Icc 1 N) hpl using 1
    ext x
    simp only [pp, Finset.sum_apply]
  obtain ⟨hrb, hrt, hrr, hrl⟩ :=
    intervalIntegrable_originalContourPatchedRemainder_rectangle_edges d F N a b ha hb
  have hrzero : Complex.boundaryIntegral r a b = 0 :=
    boundaryIntegral_originalContourPatchedRemainder_eq_zero d F N a b ha hb
  have heq : Complex.boundaryIntegral (originalContourPatchedIntegrand d F N) a b =
      Complex.boundaryIntegral
        (fun z : ℂ => originalContourKernel z * deriv (originalContourG d F) z) a b := by
    apply boundaryIntegral_congr_four_edges
    · intro x
      apply originalContourPatchedIntegrand_eq_on_rectangle_boundary d F N a b hre hbot htop
      exact Or.inr (Or.inr (Or.inl (by simp)))
    · intro x
      apply originalContourPatchedIntegrand_eq_on_rectangle_boundary d F N a b hre hbot htop
      exact Or.inr (Or.inr (Or.inr (by simp)))
    · intro y
      apply originalContourPatchedIntegrand_eq_on_rectangle_boundary d F N a b hre hbot htop
      exact Or.inr (Or.inl (by simp))
    · intro y
      apply originalContourPatchedIntegrand_eq_on_rectangle_boundary d F N a b hre hbot htop
      exact Or.inl (by simp)
  calc
    Complex.boundaryIntegral
        (fun z : ℂ => originalContourKernel z * deriv (originalContourG d F) z) a b =
        Complex.boundaryIntegral (fun z => pp z + r z) a b := heq.symm
    _ = Complex.boundaryIntegral pp a b + Complex.boundaryIntegral r a b :=
      Complex.boundaryIntegral_add pp r a b hsb hrb hst hrt hsr hrr hsl hrl
    _ = (2 * (Real.pi : ℂ) * Complex.I) * ∑ m ∈ Finset.Icc 1 N, c m := by
      rw [hrzero, add_zero]
      exact boundaryIntegral_finset_simplePoles (Finset.Icc 1 N)
        (fun m : ℕ => (m : ℂ)) c a b hreC himC

/-- Finite counterclockwise rectangle identity for the original kernel and quotient. -/
theorem originalContour_finiteRectangle
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (hN : 1 ≤ N) (T : ℝ) (hT : 0 < T) :
    Complex.boundaryIntegral
      (fun z : ℂ => originalContourKernel z * deriv (originalContourG d F) z)
      (originalContourPoint (-T)) ((N : ℂ) + originalContourPoint T) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ∑ m ∈ Finset.Icc 1 N, (-1 / 2 : ℂ) ^ m * deriv (originalContourG d F) (m : ℂ) := by
  have hRe (y : ℝ) : (originalContourPoint y).re = (1 / 2 : ℝ) := by
    simp only [originalContourPoint, Complex.add_re, Complex.div_ofNat_re,
      Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hIm (y : ℝ) : (originalContourPoint y).im = y := by
    simp only [originalContourPoint, Complex.add_im, Complex.div_ofNat_im,
      Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hbRe : ((N : ℂ) + originalContourPoint T).re = (N : ℝ) + 1 / 2 := by
    rw [Complex.add_re, Complex.natCast_re, hRe]
  have hbIm : ((N : ℂ) + originalContourPoint T).im = T := by
    rw [Complex.add_im, Complex.natCast_im, hIm, zero_add]
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  apply boundaryIntegral_originalContourKernel_mul_deriv d F N
    (originalContourPoint (-T)) ((N : ℂ) + originalContourPoint T)
  · rw [hRe, hbRe]
    exact lt_min (by norm_num) (by linarith)
  · rw [hRe, hbRe]
    exact max_lt (by linarith) (by linarith)
  · intro m hm
    rw [hRe, hbRe]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmN : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    constructor <;> linarith
  · rw [hIm]
    linarith
  · rw [hbIm]
    exact hT

end
end Li2

end
