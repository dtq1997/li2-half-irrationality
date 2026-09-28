module
public import Li2Unified.Modular.Positive.Packed.P182
public import Li2Unified.Modular.Positive.Packed.P069
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

set_option backward.privateInPublic true

@[expose] public section

section
/-! An actual bounded angular parameterization of each comparison-measure
layer, with its exact density/Jacobian normalization. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy

def starLayerCurve (s : StarLayer) (θ : ℝ) : ℂ :=
  segmentCurve ((s.left : ℂ) * s.direction)
    ((s.right : ℂ) * s.direction) θ

def starLayerAngularDensity (s : StarLayer) : ℝ :=
  (s.density : ℝ) * (s.right - s.left) / (2 * Real.pi)

lemma starLayerCurve_on (s : StarLayer) {θ : ℝ}
    (hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi)) :
    starLayerCurve s θ =
      (((s.right - s.left) / (2 * Real.pi) * θ + s.left : ℝ) : ℂ) *
        s.direction := by
  unfold starLayerCurve
  rw [segmentCurve_on _ _ hθ]
  simp only [Complex.real_smul]
  push_cast
  ring

lemma continuous_starLayerCurve (s : StarLayer) :
    Continuous (starLayerCurve s) :=
  continuous_segmentCurve _ _

lemma starLayerCurve_norm_le (s : StarLayer) (hs : s.Valid)
    (θ : ℝ) : ‖starLayerCurve s θ‖ ≤ (s.radius : ℝ) := by
  have h := segmentCurve_norm_le
    ((s.left : ℂ) * s.direction) ((s.right : ℂ) * s.direction) θ
  change ‖starLayerCurve s θ‖ ≤ _ at h
  have hr : (0 : ℝ) ≤ s.radius := by exact_mod_cast hs.1
  have hleft : |s.left| ≤ (s.radius : ℝ) := by
    cases hv : s.vertical <;>
      simp [StarLayer.left, hv, abs_of_nonneg hr] <;> exact_mod_cast hs.1
  have hright : |s.right| ≤ (s.radius : ℝ) := by
    simp [StarLayer.right, abs_of_nonneg hr]
  have hdir : ‖s.direction‖ = 1 := by
    cases hv : s.vertical <;> simp [StarLayer.direction, hv]
  have hna : ‖(s.left : ℂ) * s.direction‖ ≤ (s.radius : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hdir, mul_one]
    exact hleft
  have hnb : ‖(s.right : ℂ) * s.direction‖ ≤ (s.radius : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hdir, mul_one]
    exact hright
  exact h.trans (max_le hna hnb)

theorem starLayer_angular_integral (s : StarLayer) (f : ℂ → ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      starLayerAngularDensity s * f (starLayerCurve s θ)) =
      (s.density : ℝ) * ∫ x in s.left..s.right,
        f ((x : ℂ) * s.direction) := by
  have hT : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hpoint (θ : ℝ) (hθ : θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi)) :
      starLayerCurve s θ =
        (((s.right - s.left) / (2 * Real.pi) * θ + s.left : ℝ) : ℂ) *
          s.direction :=
    starLayerCurve_on s (by simpa only [uIcc_of_le hT] using hθ)
  calc
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      starLayerAngularDensity s * f (starLayerCurve s θ)) =
      starLayerAngularDensity s *
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          f ((((s.right - s.left) / (2 * Real.pi) * θ + s.left : ℝ) : ℂ) *
            s.direction)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ hθ
      dsimp only
      rw [hpoint θ hθ]
    _ = _ := by
      unfold starLayerAngularDensity
      exact angular_density_integral
        (fun x : ℝ => f ((x : ℂ) * s.direction))
        s.left s.right (s.density : ℝ)

theorem starLayerAngularDensity_mass (s : StarLayer) :
    (∫ _θ in (0 : ℝ)..2 * Real.pi,
      starLayerAngularDensity s) = (s.mass : ℝ) := by
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hm : (s.density : ℝ) * (s.right - s.left) = (s.mass : ℝ) := by
    cases hv : s.vertical <;> simp [StarLayer.right, StarLayer.left,
      StarLayer.mass, hv] <;> ring
  unfold starLayerAngularDensity
  field_simp [Real.pi_ne_zero]
  nlinarith only [hm]

end
end Li2Unified.Proofs.Contour

end

section
/- Port of Apery/Gaussian.lean (source SHA256 0cf5a66486f68b8786c9bada90ce0ef7ba5b7d90a7748d4d2ddafc85593ea3c3)
from mo271/Zeta5 by Moritz Firsching (https://github.com/mo271/Zeta5, commit f19a1960609f7d38e7b63fd2acb05e6f60a7b741), Apache-2.0; see licenses/LICENSE-Zeta5.txt.
Only the namespace was changed. -/

/-!
# Gaussian identity and Fubini helpers for the logarithmic energy

* `integral_gaussian_sub` : `∫ x, exp (-b (x - c)²) = √(π/b)`;
* `gaussian_conv` : the completing-the-square identity
  `∫ u : ℂ, exp (-2s‖z-u‖²) exp (-2s‖w-u‖²) = π/(4s) exp (-s‖z-w‖²)`;
* `intervalIntegral_swap_of_continuous` : Fubini for interval integrals of continuous functions.
-/

open MeasureTheory Set Real

namespace Li2Unified.ParameterFamily.Energy


#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "Gaussian: imports loaded"
  out.flush

lemma integral_gaussian_sub {b : ℝ} (c : ℝ) :
    ∫ x : ℝ, Real.exp (-b * (x - c) ^ 2) = Real.sqrt (π / b) := by
  rw [integral_sub_right_eq_self (fun x => Real.exp (-b * x ^ 2)) c]
  exact integral_gaussian b

lemma integrable_gaussian_sub {b : ℝ} (hb : 0 < b) (c : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-b * (x - c) ^ 2)) := by
  have := (integrable_exp_neg_mul_sq hb).comp_sub_right c
  simpa using this

/-- Completing the square in one variable. -/
lemma sq_add_sq_eq (a b x : ℝ) :
    (a - x) ^ 2 + (b - x) ^ 2 = 2 * (x - (a + b) / 2) ^ 2 + (a - b) ^ 2 / 2 := by ring

lemma gaussian_conv_one (s a b : ℝ) :
    ∫ x : ℝ, Real.exp (-(2 * s) * (a - x) ^ 2) * Real.exp (-(2 * s) * (b - x) ^ 2) =
      Real.sqrt (π / (4 * s)) * Real.exp (-s * (a - b) ^ 2) := by
  have : ∀ x : ℝ, Real.exp (-(2 * s) * (a - x) ^ 2) * Real.exp (-(2 * s) * (b - x) ^ 2) =
      Real.exp (-(4 * s) * (x - (a + b) / 2) ^ 2) * Real.exp (-s * (a - b) ^ 2) := by
    intro x
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [this]
  rw [integral_mul_const, integral_gaussian_sub]


#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "Gaussian: real convolution complete"
  out.flush

/-- The norm squared on `ℂ` in terms of real and imaginary parts. -/
lemma normSq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- The completing-the-square identity on `ℂ`. -/
lemma gaussian_conv {s : ℝ} (hs : 0 < s) (z w : ℂ) :
    ∫ u : ℂ, Real.exp (-(2 * s) * ‖z - u‖ ^ 2) * Real.exp (-(2 * s) * ‖w - u‖ ^ 2) =
      π / (4 * s) * Real.exp (-s * ‖z - w‖ ^ 2) := by
  have h := Complex.volume_preserving_equiv_real_prod
  have key : ∀ u : ℂ, Real.exp (-(2 * s) * ‖z - u‖ ^ 2) * Real.exp (-(2 * s) * ‖w - u‖ ^ 2) =
      (Real.exp (-(2 * s) * (z.re - u.re) ^ 2) * Real.exp (-(2 * s) * (w.re - u.re) ^ 2)) *
      (Real.exp (-(2 * s) * (z.im - u.im) ^ 2) * Real.exp (-(2 * s) * (w.im - u.im) ^ 2)) := by
    intro u
    rw [normSq_eq, normSq_eq]
    simp only [Complex.sub_re, Complex.sub_im]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  simp_rw [key]
  have e := h.integral_comp' (fun p : ℝ × ℝ =>
      (Real.exp (-(2 * s) * (z.re - p.1) ^ 2) * Real.exp (-(2 * s) * (w.re - p.1) ^ 2)) *
      (Real.exp (-(2 * s) * (z.im - p.2) ^ 2) * Real.exp (-(2 * s) * (w.im - p.2) ^ 2)))
  simp only [Complex.measurableEquivRealProd_apply] at e
  rw [e, Measure.volume_eq_prod]
  rw [integral_prod_mul (fun x : ℝ => Real.exp (-(2 * s) * (z.re - x) ^ 2) * Real.exp (-(2 * s) * (w.re - x) ^ 2))
    (fun y : ℝ => Real.exp (-(2 * s) * (z.im - y) ^ 2) * Real.exp (-(2 * s) * (w.im - y) ^ 2)),
    gaussian_conv_one s _ _, gaussian_conv_one s _ _, normSq_eq]
  simp only [Complex.sub_re, Complex.sub_im]
  rw [mul_mul_mul_comm, ← Real.sqrt_mul (by positivity), ← Real.exp_add, ← sq,
    Real.sqrt_sq (by positivity)]
  congr 2
  ring


#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "Gaussian: complex convolution complete"
  out.flush

/-- Fubini for interval integrals of a continuous function of two variables. -/
lemma intervalIntegral_swap_of_continuous {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  refine IntegrableOn.mono_set ?_ (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hf.continuousOn


#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "Gaussian: Fubini complete"
  out.flush

end Li2Unified.ParameterFamily.Energy

end


end
