module
public import Li2Unified.Modular.Positive.Packed.P078
public import Li2Unified.Modular.Positive.Packed.P075
public import Li2Unified.Modular.Positive.Packed.P076
public import Li2Unified.Modular.Positive.Packed.P077
public import Li2Unified.Modular.Positive.Packed.P073
public import Li2Unified.Modular.Base.OriginalContourFiniteRectangle

set_option backward.privateInPublic true

@[expose] public section

section
/-! The right side also vanishes on the diagonal rectangles `T=N`. -/

open Polynomial Filter
open scoped Topology
namespace Li2Unified.Proofs.Contour
noncomputable section

theorem upperRightIntegral_diagonal_tendsto_zero (d : ℕ) (F : ℚ[X]) :
    Tendsto (fun N : ℕ => upperRightIntegral d F N (N : ℝ)) atTop (𝓝 0) := by
  let C : ℝ := Li2.originalCoefficientNormSum (Li2.originalContourGDerivativeNumerator d F)
  let k : ℕ := (Li2.originalContourGDerivativeNumerator d F).natDegree
  have hC : 0 ≤ C := Li2.originalRightCoefficientNormSum_nonneg _
  have hdecay := Li2.originalRightDecay_tendsto_zero (k + 1)
  have hlim : Tendsto (fun N : ℕ =>
      (2 * C * 2 ^ k) * ((1 + (N : ℝ)) ^ (k + 1) * (1 / 2 : ℝ) ^ N))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using! hdecay.const_mul (2 * C * 2 ^ k)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [] with N
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hshift : 1 + (N : ℝ) + (N : ℝ) ≤ 2 * (1 + (N : ℝ)) := by linarith
  have hpow : (1 + (N : ℝ) + (N : ℝ)) ^ k ≤
      (2 * (1 + (N : ℝ))) ^ k :=
    pow_le_pow_left₀ (by positivity) hshift k
  calc
    ‖upperRightIntegral d F N (N : ℝ)‖ ≤
        (2 * (N : ℝ)) * ((1 / 2 : ℝ) ^ N * C *
          (1 + (N : ℝ) + (N : ℝ)) ^ k) :=
      upperRightIntegral_norm_le d F N (N : ℝ) hN
    _ ≤ (2 * (1 + (N : ℝ))) * ((1 / 2 : ℝ) ^ N * C *
          (2 * (1 + (N : ℝ))) ^ k) := by
      gcongr
      linarith
    _ = (2 * C * 2 ^ k) *
        ((1 + (N : ℝ)) ^ (k + 1) * (1 / 2 : ℝ) ^ N) := by
      rw [mul_pow, pow_succ]
      ring

end
end Li2Unified.Proofs.Contour

end

section
/-! The finite upper rectangle gives the original numerator functional as the
limit of its lower horizontal side minus its left vertical side. -/

open Polynomial MeasureTheory Filter
open scoped Topology BigOperators Interval
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic Li2Unified.Instances.PosHalf
open Li2Unified.ParameterFamily

def upperBottomIntegral (d : ℕ) (F : ℚ[X]) (N : ℕ) (T : ℝ) : ℂ :=
  ∫ x : ℝ in (1 / 2)..((N : ℝ) + 1 / 2),
    (power ((x : ℂ) - (T : ℂ) * Complex.I) *
      kappaPlus ((x : ℂ) - (T : ℂ) * Complex.I)) *
      deriv (Li2.originalContourG d F) ((x : ℂ) - (T : ℂ) * Complex.I)

def upperLeftIntegral (d : ℕ) (F : ℚ[X]) (T : ℝ) : ℂ :=
  ∫ y : ℝ in (-T)..T,
    (power (point ⟨1, by decide⟩ y) *
      kappaPlus (point ⟨1, by decide⟩ y)) *
      deriv (Li2.originalContourG d F) (point ⟨1, by decide⟩ y)

theorem upper_finiteRectangle_four_edges (d : ℕ) (F : ℚ[X])
    (N : ℕ) (hN : 1 ≤ N) (T : ℝ) (hT : 0 < T) :
    upperBottomIntegral d F N T - upperTopIntegral d F N T +
      Complex.I * upperRightIntegral d F N T -
      Complex.I * upperLeftIntegral d F T =
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
  have h := upper_finiteRectangle d F N hN T hT
  unfold Complex.boundaryIntegral at h
  simp only [hRe, hIm, hbRe, hbIm] at h
  have hright (y : ℝ) :
      (((N : ℝ) + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I =
        (N : ℂ) + point ⟨1, by decide⟩ y := by
    simp only [point, reduceIte]
    push_cast
    ring
  have hleft (y : ℝ) :
      (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
        point ⟨1, by decide⟩ y := by
    simp only [point, reduceIte]
    push_cast
    ring
  have hbottom (x : ℝ) :
      (x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I =
        (x : ℂ) - (T : ℂ) * Complex.I := by
    push_cast
    ring
  simpa only [upperBottomIntegral, upperTopIntegral, upperRightIntegral,
    upperLeftIntegral, hright, hleft, hbottom, smul_eq_mul,
    sub_eq_add_neg] using! h

theorem upper_diagonal_boundary_limit (d : ℕ) (F : ℚ[X]) :
    Tendsto (fun N : ℕ => upperBottomIntegral d F N (N : ℝ) -
        Complex.I * upperLeftIntegral d F (N : ℝ)) atTop
      (𝓝 ((numeratorFunctional lambda d F).eval₂ (Rat.castHom ℂ) (value : ℂ))) := by
  have hseries := tendsto_positive_residueSum d F
  have htop := upperTopIntegral_diagonal_tendsto_zero d F
  have hright := upperRightIntegral_diagonal_tendsto_zero d F
  have hlim : Tendsto (fun N : ℕ =>
      (∑ m ∈ Finset.Icc 1 N,
        (1 / 2 : ℂ) ^ m * deriv (Li2.originalContourG d F) (m : ℂ)) +
        upperTopIntegral d F N (N : ℝ) -
        Complex.I * upperRightIntegral d F N (N : ℝ)) atTop
      (𝓝 ((numeratorFunctional lambda d F).eval₂ (Rat.castHom ℂ) (value : ℂ))) := by
    simpa only [add_zero, mul_zero, sub_zero] using!
      (hseries.add htop).sub (tendsto_const_nhds.mul hright)
  apply (tendsto_congr' _).mpr hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have h := upper_finiteRectangle_four_edges d F N hN (N : ℝ) hNR
  linear_combination h

end
end Li2Unified.Proofs.Contour

end

section
/-! Cauchy shift for the pole-free kernel `power * G'` in the right half-plane. -/

open Polynomial MeasureTheory Set
open scoped BigOperators Interval
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

def plainIntegrand (d : ℕ) (F : ℚ[X]) (z : ℂ) : ℂ :=
  power z * deriv (Li2.originalContourG d F) z

lemma plainIntegrand_analyticAt (d : ℕ) (F : ℚ[X]) {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (plainIntegrand d F) z := by
  have hp : AnalyticAt ℂ power z := by
    have h : Differentiable ℂ power := by unfold power; fun_prop
    exact h.analyticAt z
  exact hp.mul (Li2.analyticAt_originalContourG_deriv d F hz)

lemma plain_boundaryIntegral_eq_zero (d : ℕ) (F : ℚ[X]) (a b : ℂ)
    (ha : 0 < min a.re b.re) :
    Complex.boundaryIntegral (plainIntegrand d F) a b = 0 := by
  apply Complex.boundaryIntegral_eq_zero_of_diffOn (s := ∅) Set.countable_empty
  · intro z hz
    have hzr : min a.re b.re ≤ z.re := hz.1.1
    exact (plainIntegrand_analyticAt d F (lt_of_lt_of_le ha hzr)).continuousAt.continuousWithinAt
  · intro z hz
    have hzr : min a.re b.re < z.re := hz.1.1.1
    exact (plainIntegrand_analyticAt d F (lt_trans ha hzr)).differentiableAt

def plainBottomIntegral (d : ℕ) (F : ℚ[X]) (N : ℕ) (T : ℝ) : ℂ :=
  ∫ x : ℝ in (1 / 2)..((N : ℝ) + 1 / 2),
    plainIntegrand d F ((x : ℂ) - (T : ℂ) * Complex.I)

def plainRealIntegral (d : ℕ) (F : ℚ[X]) (N : ℕ) : ℂ :=
  ∫ x : ℝ in (1 / 2)..((N : ℝ) + 1 / 2), plainIntegrand d F (x : ℂ)

def plainRightIntegral (d : ℕ) (F : ℚ[X]) (N : ℕ) (T : ℝ) : ℂ :=
  ∫ y : ℝ in (-T)..0,
    plainIntegrand d F ((N : ℂ) + point ⟨1, by decide⟩ y)

def plainLowerLeftIntegral (d : ℕ) (F : ℚ[X]) (T : ℝ) : ℂ :=
  ∫ y : ℝ in (-T)..0, plainIntegrand d F (point ⟨1, by decide⟩ y)

theorem plain_finiteRectangle_four_edges (d : ℕ) (F : ℚ[X])
    (N : ℕ) (T : ℝ) :
    plainBottomIntegral d F N T - plainRealIntegral d F N +
      Complex.I * plainRightIntegral d F N T -
      Complex.I * plainLowerLeftIntegral d F T = 0 := by
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
  have hbRe : ((N : ℂ) + Li2.originalContourPoint 0).re = (N : ℝ) + 1 / 2 := by
    rw [Complex.add_re, Complex.natCast_re, hRe]
  have hbIm : ((N : ℂ) + Li2.originalContourPoint 0).im = 0 := by
    rw [Complex.add_im, Complex.natCast_im, hIm, zero_add]
  have hzero : Complex.boundaryIntegral (plainIntegrand d F)
      (Li2.originalContourPoint (-T)) ((N : ℂ) + Li2.originalContourPoint 0) = 0 := by
    apply plain_boundaryIntegral_eq_zero
    rw [hRe, hbRe]
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    exact lt_min (by norm_num) (by linarith)
  unfold Complex.boundaryIntegral at hzero
  simp only [hRe, hIm, hbRe, hbIm] at hzero
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hzero
  have hright (y : ℝ) :
      (((N : ℝ) + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I =
        (N : ℂ) + point ⟨1, by decide⟩ y := by
    simp only [point, reduceIte]
    push_cast
    ring
  have hleft (y : ℝ) :
      (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
        point ⟨1, by decide⟩ y := by
    simp only [point, reduceIte]
    push_cast
    ring
  have hbottom (x : ℝ) :
      (x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I =
        (x : ℂ) - (T : ℂ) * Complex.I := by
    push_cast
    ring
  simpa only [plainBottomIntegral, plainRealIntegral, plainRightIntegral,
    plainLowerLeftIntegral, hright, hleft, hbottom, plainIntegrand,
    smul_eq_mul, sub_eq_add_neg] using! hzero

end
end Li2Unified.Proofs.Contour

end


end
