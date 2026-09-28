module
public import Li2Unified.Modular.Base.OriginalContourFiniteRectangle
public import Li2Unified.Modular.Base.OriginalContourHorizontalTails
public import Li2Unified.Modular.Base.OriginalContourRightActual
public import Li2Unified.Modular.Base.OriginalContourResidueSeries

set_option backward.privateInPublic true

@[expose] public section

open Polynomial MeasureTheory Filter
open scoped Topology BigOperators
namespace Li2
noncomputable section

def originalContourVerticalSegment (d : ℕ) (F : ℚ[X]) (N : ℕ) (T : ℝ) : ℂ :=
  ∫ y : ℝ in (-T)..T,
    originalContourKernel ((N : ℂ) + originalContourPoint y) *
      deriv (originalContourG d F) ((N : ℂ) + originalContourPoint y)

def originalContourVerticalIntegral (d : ℕ) (F : ℚ[X]) (N : ℕ) : ℂ :=
  ∫ y : ℝ, originalContourKernel ((N : ℂ) + originalContourPoint y) *
    deriv (originalContourG d F) ((N : ℂ) + originalContourPoint y)

lemma tendsto_originalContourVerticalSegment (d : ℕ) (F : ℚ[X]) (N : ℕ) :
    Tendsto (originalContourVerticalSegment d F N) atTop
      (𝓝 (originalContourVerticalIntegral d F N)) := by
  simpa only [originalContourVerticalSegment, originalContourVerticalIntegral] using
    (MeasureTheory.intervalIntegral_tendsto_integral
      (integrable_originalRightKernel_mul_G_deriv d F N)
      (tendsto_neg_atTop_atBot : Tendsto (fun T : ℝ => -T) atTop atBot)
      (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop))

lemma originalContour_rectangle_decomposition (d : ℕ) (F : ℚ[X]) (N : ℕ) (T : ℝ) :
    Complex.boundaryIntegral
      (fun z : ℂ => originalContourKernel z * deriv (originalContourG d F) z)
      (originalContourPoint (-T)) ((N : ℂ) + originalContourPoint T) =
      originalContourHorizontalIntegral d F N (-T) -
        originalContourHorizontalIntegral d F N T +
        Complex.I * originalContourVerticalSegment d F N T -
        Complex.I * originalContourVerticalSegment d F 0 T := by
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
  have hright (y : ℝ) :
      (((N : ℝ) + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I =
        (N : ℂ) + originalContourPoint y := by
    simp only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat, originalContourPoint]
    ring
  have hleft (y : ℝ) :
      ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I =
        ((0 : ℕ) : ℂ) + originalContourPoint y := by norm_num [originalContourPoint]
  simp only [Complex.boundaryIntegral, hRe, hIm, hbRe, hbIm, smul_eq_mul]
  simp_rw [hright, hleft]
  rfl

theorem tendsto_originalContour_rectangle_height
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (hN : 1 ≤ N) :
    Tendsto
      (fun T : ℝ => Complex.boundaryIntegral
        (fun z : ℂ => originalContourKernel z * deriv (originalContourG d F) z)
        (originalContourPoint (-T)) ((N : ℂ) + originalContourPoint T))
      atTop (𝓝 (Complex.I * originalContourVerticalIntegral d F N -
        Complex.I * originalContourVerticalIntegral d F 0)) := by
  have hbottom := tendsto_originalContourHorizontalIntegral_neg_atTop d F N hN
  have htop := tendsto_originalContourHorizontalIntegral_atTop d F N hN
  have hright := (tendsto_originalContourVerticalSegment d F N).const_mul Complex.I
  have hleft := (tendsto_originalContourVerticalSegment d F 0).const_mul Complex.I
  simpa only [originalContour_rectangle_decomposition, sub_zero, zero_add] using
    (((hbottom.sub htop).add hright).sub hleft)

theorem originalContour_vertical_difference_eq_residueSum
    (d : ℕ) (F : ℚ[X]) (N : ℕ) (hN : 1 ≤ N) :
    originalContourVerticalIntegral d F N - originalContourVerticalIntegral d F 0 =
      (2 * (Real.pi : ℂ)) * ∑ m ∈ Finset.Icc 1 N,
          (-1 / 2 : ℂ) ^ m * deriv (originalContourG d F) (m : ℂ) := by
  have hc : Tendsto
      (fun _ : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * ∑ m ∈ Finset.Icc 1 N,
          (-1 / 2 : ℂ) ^ m * deriv (originalContourG d F) (m : ℂ)) atTop
      (𝓝 ((2 * (Real.pi : ℂ) * Complex.I) * ∑ m ∈ Finset.Icc 1 N,
          (-1 / 2 : ℂ) ^ m * deriv (originalContourG d F) (m : ℂ))) := tendsto_const_nhds
  have heq :
      (fun T : ℝ => Complex.boundaryIntegral
        (fun z : ℂ => originalContourKernel z * deriv (originalContourG d F) z)
        (originalContourPoint (-T)) ((N : ℂ) + originalContourPoint T)) =ᶠ[atTop]
      (fun _ : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * ∑ m ∈ Finset.Icc 1 N,
          (-1 / 2 : ℂ) ^ m * deriv (originalContourG d F) (m : ℂ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact originalContour_finiteRectangle d F N hN T hT
  have he := tendsto_nhds_unique_of_eventuallyEq
    (tendsto_originalContour_rectangle_height d F N hN) hc heq
  apply mul_left_cancel₀ Complex.I_ne_zero
  calc
    Complex.I * (originalContourVerticalIntegral d F N - originalContourVerticalIntegral d F 0) =
        Complex.I * originalContourVerticalIntegral d F N -
          Complex.I * originalContourVerticalIntegral d F 0 := by ring
    _ = (2 * (Real.pi : ℂ) * Complex.I) * ∑ m ∈ Finset.Icc 1 N,
          (-1 / 2 : ℂ) ^ m * deriv (originalContourG d F) (m : ℂ) := he
    _ = Complex.I * ((2 * (Real.pi : ℂ)) * ∑ m ∈ Finset.Icc 1 N,
          (-1 / 2 : ℂ) ^ m * deriv (originalContourG d F) (m : ℂ)) := by ring

theorem neg_originalContourVerticalIntegral_zero_eq_functional (d : ℕ) (F : ℚ[X]) :
    -originalContourVerticalIntegral d F 0 = (2 * (Real.pi : ℂ)) *
      (((numeratorFunctional d F).eval₂ (Rat.castHom ℝ) li2NegHalf : ℝ) : ℂ) := by
  have hr : Tendsto (originalContourVerticalIntegral d F) atTop (𝓝 0) := by
    simpa only [originalContourVerticalIntegral] using
      originalRightKernel_G_deriv_integral_tendsto_zero d F
  have hl : Tendsto
      (fun N : ℕ => originalContourVerticalIntegral d F N - originalContourVerticalIntegral d F 0)
      atTop (𝓝 (-originalContourVerticalIntegral d F 0)) := by
    simpa only [zero_sub] using
      hr.sub (tendsto_const_nhds (x := originalContourVerticalIntegral d F 0))
  have hs := (tendsto_originalContour_residueSum d F).const_mul (2 * (Real.pi : ℂ))
  apply tendsto_nhds_unique_of_eventuallyEq hl hs
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact originalContour_vertical_difference_eq_residueSum d F N hN

theorem numeratorFunctional_eq_neg_originalContour_integral (d : ℕ) (F : ℚ[X]) :
    (numeratorFunctional d F).eval₂ (Rat.castHom ℂ) (li2NegHalf : ℂ) =
      -(∫ y : ℝ, originalContourKernel (originalContourPoint y) *
        deriv (originalContourG d F) (originalContourPoint y)) / (2 * (Real.pi : ℂ)) := by
  rw [originalComplexEval_ofReal]
  have hpi : 2 * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
      (by exact_mod_cast Real.pi_ne_zero : (Real.pi : ℂ) ≠ 0)
  apply (eq_div_iff hpi).mpr
  calc
    _ = (2 * (Real.pi : ℂ)) *
        (((numeratorFunctional d F).eval₂ (Rat.castHom ℝ) li2NegHalf : ℝ) : ℂ) := mul_comm _ _
    _ = -originalContourVerticalIntegral d F 0 :=
      (neg_originalContourVerticalIntegral_zero_eq_functional d F).symm
    _ = _ := by simp only [originalContourVerticalIntegral, Nat.cast_zero, zero_add]

theorem numeratorFunctional_eq_originalContourWeight_integral (d : ℕ) (F : ℚ[X]) :
    (numeratorFunctional d F).eval₂ (Rat.castHom ℂ) (li2NegHalf : ℂ) =
      ∫ y : ℝ, originalContourWeight y * originalComplexQuotient d F (originalContourPoint y) := by
  rw [numeratorFunctional_eq_neg_originalContour_integral]
  exact (integral_originalContourWeight_mul_quotient_eq_neg_kernel d F).symm

theorem originalContourEntry_eq_weight_integral (n : ℕ) (i j : Fin (2 * n)) :
    (A n i j : ℂ) + (li2NegHalf : ℂ) * (B n i j : ℂ) =
      ∫ y : ℝ, originalContourWeight y *
        originalComplexQuotient (4 * n) (numerator n (i.val + j.val)) (originalContourPoint y) := by
  have h := numeratorFunctional_eq_originalContourWeight_integral (4 * n) (numerator n (i.val + j.val))
  rw [numeratorFunctional_entry] at h
  simpa only [eval₂_add, eval₂_C, eval₂_mul, eval₂_X, Rat.coe_castHom, A, B] using h

theorem originalContourEntry_eq_weight_integral_explicit (n : ℕ) (i j : Fin (2 * n)) :
    (A n i j : ℂ) + (li2NegHalf : ℂ) * (B n i j : ℂ) =
      ∫ y : ℝ, originalContourWeight y *
        (originalContourPoint y ^ (i.val + j.val) *
          ((D n).eval₂ (Rat.castHom ℂ) (originalContourPoint y)) ^ 3 /
          (D (4 * n)).eval₂ (Rat.castHom ℂ) (originalContourPoint y)) := by
  simpa only [originalComplexQuotient_numerator] using originalContourEntry_eq_weight_integral n i j

end
end Li2

end
