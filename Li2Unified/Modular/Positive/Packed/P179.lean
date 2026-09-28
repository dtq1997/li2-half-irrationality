module
public import Li2Unified.Modular.Positive.Packed.P163
public import Li2Unified.Modular.Positive.Packed.P176
public import Li2Unified.Modular.Positive.Packed.P178
public import Li2Unified.Modular.Positive.Packed.P108
public import Li2Unified.Modular.Positive.Packed.P109
public import Li2Unified.Modular.Base.OriginalContourIntegrable

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Potential.CompactAffine
open Li2Unified.Proofs.Potential.KernelReflectionSelf
noncomputable section

theorem half_ray_compact (x : ℝ) (hx : 0 ≤ x ∧ x ≤ (18 : ℝ)) :
    Li2Unified.Stage0.HalfAnalytic.psiRay x ≤ (19/10 : ℝ) := by
  have hx' : x ∈ Set.Icc (qZero.toRat : ℝ) ((⟨18, 1⟩ : QPair).toRat : ℝ) := by
    simpa [qZero, QPair.toRat] using! hx
  have h := checkAll_cover_sound_of_lt halfRayBoxes_checked halfRayBoxes_cover
    (by norm_num [qZero, QPair.toRat]) hx'
  rw [halfRayTerms_actual x hx.1] at h
  norm_num [QPair.toRat] at h ⊢
  exact h

theorem half_up_compact (x : ℝ) (hx : 0 ≤ x ∧ x ≤ (2 : ℝ)) :
    Li2Unified.Stage0.HalfAnalytic.psiUp x ≤ (19/10 : ℝ) := by
  have hx' : x ∈ Set.Icc (qZero.toRat : ℝ) ((⟨2, 1⟩ : QPair).toRat : ℝ) := by
    simpa [qZero, QPair.toRat] using! hx
  have h := checkAll_cover_sound_of_lt halfUpBoxes_checked halfUpBoxes_cover
    (by norm_num [qZero, QPair.toRat]) hx'
  rw [halfUpTerms_actual x hx.1] at h
  norm_num [QPair.toRat] at h ⊢
  exact h

end
end Li2Unified.Proofs.Potential.CompactAffine

#print axioms Li2Unified.Proofs.Potential.CompactAffine.half_ray_compact
#print axioms Li2Unified.Proofs.Potential.CompactAffine.half_up_compact

end

section
namespace Li2Unified.Instances.PosHalf.GeneratedPotential
noncomputable section

/-- Exact affine certificates cover the full compact interval. -/
theorem ray_compact (x : ℝ) (hx : 0 ≤ x ∧ x ≤ (18/1:ℝ)) :
    Li2Unified.Stage0.HalfAnalytic.psiRay x ≤ (19/10:ℝ) := by
  exact Li2Unified.Proofs.Potential.CompactAffine.half_ray_compact x (by simpa only [div_one] using! hx)

/-- Exact affine certificates cover the full compact interval. -/
theorem vertical_compact (x : ℝ) (hx : 0 ≤ x ∧ x ≤ (2/1:ℝ)) :
    Li2Unified.Stage0.HalfAnalytic.psiUp x ≤ (19/10:ℝ) := by
  exact Li2Unified.Proofs.Potential.CompactAffine.half_up_compact x (by simpa only [div_one] using! hx)
end
end Li2Unified.Instances.PosHalf.GeneratedPotential

end

section
open MeasureTheory Set
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HalfAnalytic
open Li2Unified.Proofs.Potential
open Li2Unified.Instances.PosHalf.GeneratedPotential
open Li2Unified.Instances.PosHalf.LayerComparison
open Li2Unified.ParameterFamily.Energy

/-- The potential on each of the three arms before the small ray displacement. -/
def starArmPsi (b : Fin 3) (y : ℝ) : ℝ :=
  if b.val = 0 then psiRay y else if b.val = 1 then psiUp y else psiDown y

private lemma ray_spatial_bounds (y : ℝ) (hy : 0 ≤ y) :
    psiRay y ≤ 19/10 ∧ psiRay y ≤ 19/10+9/5-y/10 := by
  by_cases h18 : y ≤ 18
  · have h := ray_compact y ⟨hy, by norm_num at h18 ⊢; exact h18⟩
    constructor <;> linarith
  · have h := actual_ray_tail_linear y (by linarith)
    constructor <;> linarith

private lemma up_spatial_bounds (y : ℝ) (hy : 0 ≤ y) :
    psiUp y ≤ 19/10 ∧ psiUp y ≤ 19/10+9/5-y/10 := by
  by_cases h2 : y ≤ 2
  · have h := vertical_compact y ⟨hy, by norm_num at h2 ⊢; exact h2⟩
    constructor <;> linarith
  · have h := actual_up_tail_linear y (by linarith)
    constructor <;> linarith

theorem starArm_spatial_bounds (b : Fin 3) (y : ℝ) (hy : 0 ≤ y) :
    starArmPsi b y ≤ 19/10 ∧ starArmPsi b y ≤ 19/10+9/5-y/10 := by
  fin_cases b
  · simpa [starArmPsi] using! ray_spatial_bounds y hy
  · simpa [starArmPsi] using! up_spatial_bounds y hy
  · simpa [starArmPsi, psi_reflection] using! up_spatial_bounds y hy

theorem starArm_exp_majorant (n : ℕ) (hn : 1 ≤ n)
    (b : Fin 3) (y : ℝ) (hy : 0 ≤ y) :
    (1+y)^6 * Real.exp ((n:ℝ)*starArmPsi b y) ≤
      Real.exp ((n:ℝ)*(19/10:ℝ)) *
        (Real.exp (9/5:ℝ) * ((1+|y|)^6 * Real.exp (-|y|/10))) := by
  obtain ⟨hS, hlin⟩ := starArm_spatial_bounds b y hy
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hprod := mul_nonneg (show (0:ℝ) ≤ (n:ℝ)-1 by linarith)
    (show (0:ℝ) ≤ 19/10-starArmPsi b y by linarith)
  have he : (n:ℝ)*starArmPsi b y ≤
      (n:ℝ)*(19/10:ℝ)+9/5-y/10 := by nlinarith
  have hpow : 0 ≤ (1+y)^6 := by positivity
  calc
    (1+y)^6 * Real.exp ((n:ℝ)*starArmPsi b y) ≤
        (1+y)^6 * Real.exp ((n:ℝ)*(19/10:ℝ)+9/5-y/10) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hpow
    _ = Real.exp ((n:ℝ)*(19/10:ℝ)) *
        (Real.exp (9/5:ℝ) * ((1+|y|)^6 * Real.exp (-|y|/10))) := by
      rw [abs_of_nonneg hy]
      rw [show (n:ℝ)*(19/10:ℝ)+9/5-y/10 =
        (n:ℝ)*(19/10:ℝ)+(9/5-y/10) by ring, Real.exp_add]
      rw [show (9/5:ℝ)-y/10 = 9/5+(-y/10) by ring, Real.exp_add]
      ring

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.starArm_spatial_bounds
#print axioms Li2Unified.Proofs.Arithmetic.starArm_exp_majorant

end

end
