module
public import Li2Unified.Modular.Positive.Packed.P074
public import Li2Unified.Modular.Base.OriginalContourFiniteRectangle
public import Li2Unified.Modular.Base.OriginalContourHorizontalTails

set_option backward.privateInPublic true

@[expose] public section

section
/-! Finite residue identity for the actual positive-half upper kernel and quotient. -/

open Polynomial MeasureTheory Set
open scoped BigOperators Interval
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

lemma upperPatchedIntegrand_eq_on_rectangle_boundary
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (a b : ℂ)
    (ha : 0 < min a.re b.re) (hb : max a.re b.re < (N : ℝ) + 1)
    (hre : ∀ m ∈ Finset.Icc 1 N, (m : ℝ) ∈ Set.Ioo a.re b.re)
    (hbot : a.im < 0) (htop : 0 < b.im) {z : ℂ}
    (hz : z.re = a.re ∨ z.re = b.re ∨ z.im = a.im ∨ z.im = b.im) :
    upperPatchedIntegrand d F N z =
      (power z * kappaPlus z) * deriv (Li2.originalContourG d F) z := by
  have hpoles : ∀ m ∈ Finset.Icc 1 N, z ≠ (m : ℂ) := by
    intro m hm he
    have hmR := hre m hm
    rw [he] at hz
    simp only [Complex.natCast_re, Complex.natCast_im] at hz
    rcases hz with h | h | h | h <;> linarith [hmR.1, hmR.2]
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    by_cases him : z.im = 0
    · have hzre : z.re = a.re ∨ z.re = b.re := by
        rcases hz with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact False.elim (by rw [him] at h; linarith)
        · exact False.elim (by rw [him] at h; linarith)
      have hzpos : 0 < z.re := by
        rcases hzre with h | h <;> rw [h] <;> linarith [lt_min_iff.mp ha]
      have hzN : z.re < (N : ℝ) + 1 := by
        rcases hzre with h | h <;> rw [h] <;> linarith [max_lt_iff.mp hb]
      intro hs
      obtain ⟨m, hm, hzm⟩ := Li2.originalContour_sineZero_in_Icc N hzpos hzN hs
      exact hpoles m hm hzm
    · exact Li2.originalContour_sin_ne_zero_of_im_ne_zero him
  exact upperPatchedIntegrand_eq_off_poles d F N hpoles hsin

lemma upperMultiplier_nat_residue (m : ℕ) :
    (-1 / 2 : ℂ) ^ m * upperMultiplier (m : ℂ) =
      (1 / 2 : ℂ) ^ m / (2 * (Real.pi : ℂ) * Complex.I) := by
  unfold upperMultiplier
  rw [show (Real.pi : ℂ) * Complex.I * (m : ℂ) =
      (m : ℂ) * ((Real.pi : ℂ) * Complex.I) by ring]
  rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  calc
    (-1 / 2 : ℂ) ^ m * ((-1 : ℂ) ^ m /
        (2 * (Real.pi : ℂ) * Complex.I)) =
        (((-1 / 2 : ℂ) ^ m * (-1 : ℂ) ^ m) /
          (2 * (Real.pi : ℂ) * Complex.I)) := by ring
    _ = _ := by rw [← mul_pow]; norm_num

theorem boundaryIntegral_upperKernel_mul_deriv
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (a b : ℂ)
    (ha : 0 < min a.re b.re) (hb : max a.re b.re < (N : ℝ) + 1)
    (hre : ∀ m ∈ Finset.Icc 1 N, (m : ℝ) ∈ Set.Ioo a.re b.re)
    (hbot : a.im < 0) (htop : 0 < b.im) :
    Complex.boundaryIntegral
      (fun z : ℂ => (power z * kappaPlus z) *
        deriv (Li2.originalContourG d F) z) a b =
      ∑ m ∈ Finset.Icc 1 N,
        (1 / 2 : ℂ) ^ m * deriv (Li2.originalContourG d F) (m : ℂ) := by
  let c : ℕ → ℂ := fun m => (-1 / 2 : ℂ) ^ m *
    (upperMultiplier (m : ℂ) * deriv (Li2.originalContourG d F) (m : ℂ))
  let pp : ℂ → ℂ := fun z => ∑ m ∈ Finset.Icc 1 N, c m * (z - (m : ℂ))⁻¹
  let r : ℂ → ℂ := upperPatchedRemainder d F N
  have hreC : ∀ m ∈ Finset.Icc 1 N, (m : ℂ).re ∈ Set.Ioo a.re b.re := by
    simpa only [Complex.natCast_re] using hre
  have himC : ∀ m ∈ Finset.Icc 1 N, (m : ℂ).im ∈ Set.Ioo a.im b.im := by
    intro m hm
    simpa only [Complex.natCast_im] using And.intro hbot htop
  have hpb (m : ℕ) (hm : m ∈ Finset.Icc 1 N) : IntervalIntegrable
      (fun x : ℝ => c m * ((x : ℂ) + a.im * Complex.I - (m : ℂ))⁻¹)
      volume a.re b.re :=
    ((Li2.rectangleKernel_continuous_horizontal (p := (m : ℂ))
      (ne_of_lt (himC m hm).1)).intervalIntegrable _ _).const_mul _
  have hpt (m : ℕ) (hm : m ∈ Finset.Icc 1 N) : IntervalIntegrable
      (fun x : ℝ => c m * ((x : ℂ) + b.im * Complex.I - (m : ℂ))⁻¹)
      volume a.re b.re :=
    ((Li2.rectangleKernel_continuous_horizontal (p := (m : ℂ))
      (ne_of_gt (himC m hm).2)).intervalIntegrable _ _).const_mul _
  have hpr (m : ℕ) (hm : m ∈ Finset.Icc 1 N) : IntervalIntegrable
      (fun y : ℝ => c m * (b.re + (y : ℂ) * Complex.I - (m : ℂ))⁻¹)
      volume a.im b.im :=
    ((Li2.rectangleKernel_continuous_vertical (p := (m : ℂ))
      (ne_of_gt (hreC m hm).2)).intervalIntegrable _ _).const_mul _
  have hpl (m : ℕ) (hm : m ∈ Finset.Icc 1 N) : IntervalIntegrable
      (fun y : ℝ => c m * (a.re + (y : ℂ) * Complex.I - (m : ℂ))⁻¹)
      volume a.im b.im :=
    ((Li2.rectangleKernel_continuous_vertical (p := (m : ℂ))
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
  have hc := upperPatchedRemainder_continuousOn_rectangle d F N a b ha hb
  have hrb : IntervalIntegrable (fun x : ℝ => r (x + a.im * Complex.I))
      volume a.re b.re := Li2.rectangle_continuousOn_horizontal_intervalIntegrable hc left_mem_uIcc
  have hrt : IntervalIntegrable (fun x : ℝ => r (x + b.im * Complex.I))
      volume a.re b.re := Li2.rectangle_continuousOn_horizontal_intervalIntegrable hc right_mem_uIcc
  have hrr : IntervalIntegrable (fun y : ℝ => r (b.re + y * Complex.I))
      volume a.im b.im := Li2.rectangle_continuousOn_vertical_intervalIntegrable hc right_mem_uIcc
  have hrl : IntervalIntegrable (fun y : ℝ => r (a.re + y * Complex.I))
      volume a.im b.im := Li2.rectangle_continuousOn_vertical_intervalIntegrable hc left_mem_uIcc
  have hrzero : Complex.boundaryIntegral r a b = 0 :=
    upperPatchedRemainder_boundaryIntegral_eq_zero d F N a b ha hb
  have heq : Complex.boundaryIntegral (upperPatchedIntegrand d F N) a b =
      Complex.boundaryIntegral
        (fun z : ℂ => (power z * kappaPlus z) *
          deriv (Li2.originalContourG d F) z) a b := by
    apply Li2.boundaryIntegral_congr_four_edges
    · intro x
      apply upperPatchedIntegrand_eq_on_rectangle_boundary d F N a b ha hb hre hbot htop
      exact Or.inr (Or.inr (Or.inl (by simp)))
    · intro x
      apply upperPatchedIntegrand_eq_on_rectangle_boundary d F N a b ha hb hre hbot htop
      exact Or.inr (Or.inr (Or.inr (by simp)))
    · intro y
      apply upperPatchedIntegrand_eq_on_rectangle_boundary d F N a b ha hb hre hbot htop
      exact Or.inr (Or.inl (by simp))
    · intro y
      apply upperPatchedIntegrand_eq_on_rectangle_boundary d F N a b ha hb hre hbot htop
      exact Or.inl (by simp)
  have hcvalue (m : ℕ) :
      (2 * (Real.pi : ℂ) * Complex.I) * c m =
        (1 / 2 : ℂ) ^ m * deriv (Li2.originalContourG d F) (m : ℂ) := by
    have hden : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    dsimp [c]
    calc
      (2 * (Real.pi : ℂ) * Complex.I) *
          ((-1 / 2 : ℂ) ^ m *
            (upperMultiplier (m : ℂ) * deriv (Li2.originalContourG d F) (m : ℂ))) =
          (2 * (Real.pi : ℂ) * Complex.I) *
            (((-1 / 2 : ℂ) ^ m * upperMultiplier (m : ℂ)) *
              deriv (Li2.originalContourG d F) (m : ℂ)) := by ring
      _ = _ := by rw [upperMultiplier_nat_residue]; field_simp [hden]
  calc
    Complex.boundaryIntegral
        (fun z : ℂ => (power z * kappaPlus z) *
          deriv (Li2.originalContourG d F) z) a b =
        Complex.boundaryIntegral (fun z => pp z + r z) a b := by
          rw [← heq]
          rfl
    _ = Complex.boundaryIntegral pp a b + Complex.boundaryIntegral r a b :=
      Complex.boundaryIntegral_add pp r a b hsb hrb hst hrt hsr hrr hsl hrl
    _ = ∑ m ∈ Finset.Icc 1 N,
          (1 / 2 : ℂ) ^ m * deriv (Li2.originalContourG d F) (m : ℂ) := by
      rw [hrzero, add_zero]
      rw [Li2.boundaryIntegral_finset_simplePoles (Finset.Icc 1 N)
        (fun m : ℕ => (m : ℂ)) c a b hreC himC]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      exact hcvalue m

/-- Genuine finite upper rectangle, enclosing exactly the integers `1,…,N`. -/
theorem upper_finiteRectangle
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (hN : 1 ≤ N) (T : ℝ) (hT : 0 < T) :
    Complex.boundaryIntegral
      (fun z : ℂ => (power z * kappaPlus z) *
        deriv (Li2.originalContourG d F) z)
      (Li2.originalContourPoint (-T)) ((N : ℂ) + Li2.originalContourPoint T) =
      ∑ m ∈ Finset.Icc 1 N,
        (1 / 2 : ℂ) ^ m * deriv (Li2.originalContourG d F) (m : ℂ) := by
  have hRe (y : ℝ) : (Li2.originalContourPoint y).re = (1 / 2 : ℝ) := by
    simp only [Li2.originalContourPoint, Complex.add_re, Complex.div_ofNat_re,
      Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hIm (y : ℝ) : (Li2.originalContourPoint y).im = y := by
    simp only [Li2.originalContourPoint, Complex.add_im, Complex.div_ofNat_im,
      Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hbRe : ((N : ℂ) + Li2.originalContourPoint T).re = (N : ℝ) + 1 / 2 := by
    rw [Complex.add_re, Complex.natCast_re, hRe]
  have hbIm : ((N : ℂ) + Li2.originalContourPoint T).im = T := by
    rw [Complex.add_im, Complex.natCast_im, hIm, zero_add]
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  apply boundaryIntegral_upperKernel_mul_deriv d F N
    (Li2.originalContourPoint (-T)) ((N : ℂ) + Li2.originalContourPoint T)
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
end Li2Unified.Proofs.Contour

end


end
