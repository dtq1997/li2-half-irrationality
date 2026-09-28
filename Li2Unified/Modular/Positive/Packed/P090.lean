module
public import Li2Unified.Modular.Positive.Packed.P089
public import Li2Unified.Modular.Positive.Packed.P082
public import Li2Unified.Modular.Positive.Packed.P078
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.privateInPublic true

@[expose] public section

section
/-! The three finite integration-by-parts densities are the literal star densities. -/

open Polynomial MeasureTheory
open scoped Interval
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

def rayDensityFinite (d : ℕ) (F : ℚ[X]) (N : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..(N : ℝ),
    density ⟨0, by decide⟩ t *
      Li2.originalComplexQuotient d F (point ⟨0, by decide⟩ t)

def upDensityFinite (d : ℕ) (F : ℚ[X]) (T : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..T,
    density ⟨1, by decide⟩ t *
      Li2.originalComplexQuotient d F (point ⟨1, by decide⟩ t)

def downDensityFinite (d : ℕ) (F : ℚ[X]) (T : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..T,
    density ⟨2, by decide⟩ t *
      Li2.originalComplexQuotient d F (point ⟨2, by decide⟩ t)

lemma rayDensityFinite_eq (d : ℕ) (F : ℚ[X]) (N : ℕ) :
    rayDensityFinite d F N =
      (Real.log 2 : ℂ) *
        (∫ x in (1 / 2 : ℝ)..((N : ℝ) + 1 / 2),
          power (x : ℂ) * Li2.originalContourG d F (x : ℂ)) := by
  let f : ℝ → ℂ := fun x =>
    (Real.log 2 : ℂ) * (power (x : ℂ) * Li2.originalContourG d F (x : ℂ))
  have hshift := intervalIntegral.integral_comp_add_left
    (a := (0 : ℝ)) (b := (N : ℝ)) f (1 / 2 : ℝ)
  have hleft : rayDensityFinite d F N =
      ∫ t in (0 : ℝ)..(N : ℝ), f (1 / 2 + t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [rayDensityFinite, f, density, point]
    rw [Li2.originalContourG]
    push_cast
    ring
  calc
    rayDensityFinite d F N = ∫ t in (0 : ℝ)..(N : ℝ), f (1 / 2 + t) := hleft
    _ = ∫ x in (1 / 2 : ℝ)..((N : ℝ) + 1 / 2), f x := by
      simpa only [add_zero, zero_add, add_comm] using! hshift
    _ = _ := by
      simpa only [f] using!
        (intervalIntegral.integral_const_mul (a := (1 / 2 : ℝ))
          (b := (N : ℝ) + 1 / 2) (μ := volume)
          (Real.log 2 : ℂ)
          (fun x : ℝ => power (x : ℂ) * Li2.originalContourG d F (x : ℂ)))

lemma upDensityFinite_eq (d : ℕ) (F : ℚ[X]) (T : ℝ) :
    upDensityFinite d F T =
      ∫ y in (0 : ℝ)..T,
        (deriv (fun z => power z * kappaPlus z) (Li2.originalContourPoint y) *
          Complex.I) * Li2.originalContourG d F (Li2.originalContourPoint y) := by
  apply intervalIntegral.integral_congr
  intro y hy
  dsimp [upDensityFinite, density, point, Li2.originalContourPoint]
  rw [Li2.originalContourG]
  ring

lemma downDensityFinite_eq (d : ℕ) (F : ℚ[X]) (T : ℝ) :
    downDensityFinite d F T =
      -(∫ y in (-T)..(0 : ℝ),
        (deriv (fun z => power z * kappaMinus z) (Li2.originalContourPoint y) *
          Complex.I) * Li2.originalContourG d F (Li2.originalContourPoint y)) := by
  let f : ℝ → ℂ := fun y =>
    (deriv (fun z => power z * kappaMinus z) (Li2.originalContourPoint y) *
      Complex.I) * Li2.originalContourG d F (Li2.originalContourPoint y)
  have hneg := intervalIntegral.integral_comp_neg
    (a := (0 : ℝ)) (b := T) f
  have hpoint : downDensityFinite d F T =
      -(∫ t in (0 : ℝ)..T, f (-t)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [downDensityFinite, density, f, point, Li2.originalContourPoint]
    rw [Li2.originalContourG]
    push_cast
    ring
  rw [hpoint, hneg]
  simpa only [f, neg_zero]

end
end Li2Unified.Proofs.Contour

end

section
/-! Polynomial factors cannot defeat the exponential decay of either
vertical star kernel. This is the kernel part of the infinite boundary terms. -/

open Filter
open scoped Topology
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

private lemma polynomial_exponential_decay (k : ℕ) :
    Tendsto (fun T : ℝ => T ^ k * Real.exp (-(2 * Real.pi) * T))
      atTop (𝓝 0) := by
  simpa only [Real.rpow_natCast] using!
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (k : ℝ) (2 * Real.pi) (by positivity)

lemma upper_kernel_polynomial_decay (k : ℕ) :
    Tendsto (fun T : ℝ => (T : ℂ) ^ k *
      kappaPlus (point ⟨1, by decide⟩ T)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (polynomial_exponential_decay k)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  have hp : 0 ≤ T ^ k := pow_nonneg hT _
  calc
    ‖(T : ℂ) ^ k * kappaPlus (point ⟨1, by decide⟩ T)‖ =
        T ^ k * ‖kappaPlus (point ⟨1, by decide⟩ T)‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hT]
    _ ≤ T ^ k * Real.exp (-2 * Real.pi * T) :=
      mul_le_mul_of_nonneg_left (kappaPlus_upper_norm_le T) hp
    _ = T ^ k * Real.exp (-(2 * Real.pi) * T) := by ring

lemma lower_kernel_polynomial_decay (k : ℕ) :
    Tendsto (fun T : ℝ => (T : ℂ) ^ k *
      kappaMinus (point ⟨2, by decide⟩ T)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (polynomial_exponential_decay k)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  have hp : 0 ≤ T ^ k := pow_nonneg hT _
  calc
    ‖(T : ℂ) ^ k * kappaMinus (point ⟨2, by decide⟩ T)‖ =
        T ^ k * ‖kappaMinus (point ⟨2, by decide⟩ T)‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hT]
    _ ≤ T ^ k * Real.exp (-2 * Real.pi * T) :=
      mul_le_mul_of_nonneg_left (kappaMinus_lower_norm_le T) hp
    _ = T ^ k * Real.exp (-(2 * Real.pi) * T) := by ring

end
end Li2Unified.Proofs.Contour

end


end
