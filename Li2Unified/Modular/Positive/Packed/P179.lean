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
    simpa [qZero, QPair.toRat] using hx
  have h := checkAll_cover_sound_of_lt halfRayBoxes_checked halfRayBoxes_cover
    (by norm_num [qZero, QPair.toRat]) hx'
  rw [halfRayTerms_actual x hx.1] at h
  norm_num [QPair.toRat] at h ⊢
  exact h

theorem half_up_compact (x : ℝ) (hx : 0 ≤ x ∧ x ≤ (2 : ℝ)) :
    Li2Unified.Stage0.HalfAnalytic.psiUp x ≤ (19/10 : ℝ) := by
  have hx' : x ∈ Set.Icc (qZero.toRat : ℝ) ((⟨2, 1⟩ : QPair).toRat : ℝ) := by
    simpa [qZero, QPair.toRat] using hx
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
  exact Li2Unified.Proofs.Potential.CompactAffine.half_ray_compact x (by simpa only [div_one] using hx)

/-- Exact affine certificates cover the full compact interval. -/
theorem vertical_compact (x : ℝ) (hx : 0 ≤ x ∧ x ≤ (2/1:ℝ)) :
    Li2Unified.Stage0.HalfAnalytic.psiUp x ≤ (19/10:ℝ) := by
  exact Li2Unified.Proofs.Potential.CompactAffine.half_up_compact x (by simpa only [div_one] using hx)
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
  · simpa [starArmPsi] using ray_spatial_bounds y hy
  · simpa [starArmPsi] using up_spatial_bounds y hy
  · simpa [starArmPsi, psi_reflection] using up_spatial_bounds y hy

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

private def rayFormula (y : ℝ) : ℝ :=
  4*Real.log 4-1 + 3*(logPrimitive (1+y)-logPrimitive y) -
    (logPrimitive (4+y)-logPrimitive y) - y*Real.log 2 +
      4*comparisonPotential (y:ℂ)

private def upFormula (y : ℝ) : ℝ :=
  4*Real.log 4-1 + 3*perpendicularSlice 1 y-perpendicularSlice 4 y -
    2*Real.pi*y + 4*comparisonPotential ((y:ℂ)*Complex.I)

private lemma rayFormula_eq (y : ℝ) : rayFormula y = psiRay y := by
  unfold rayFormula psiRay Vray
  rw [baseRay_eq_primitives]

private lemma upFormula_eq (y : ℝ) (hy : 0 ≤ y) : upFormula y = psiUp y := by
  unfold upFormula psiUp Vvertical
  rw [baseVertical_eq_primitives y hy, abs_of_nonneg hy]

private lemma measurable_rayFormula : Measurable rayFormula := by
  have hlog : Measurable logPrimitive := continuous_logPrimitive.measurable
  have hpot : Measurable comparisonPotential := measurable_comparisonPotential
  unfold rayFormula
  fun_prop

private lemma measurable_upFormula : Measurable upFormula := by
  have hp1 : Measurable (perpendicularSlice 1) :=
    (continuous_perpendicularSlice (by norm_num : (0:ℝ)<1)).measurable
  have hp4 : Measurable (perpendicularSlice 4) :=
    (continuous_perpendicularSlice (by norm_num : (0:ℝ)<4)).measurable
  have hpot : Measurable comparisonPotential := measurable_comparisonPotential
  unfold upFormula
  fun_prop

private def armFormula (b : Fin 3) (y : ℝ) : ℝ :=
  if b.val = 0 then rayFormula y else upFormula y

private lemma measurable_armFormula (b : Fin 3) : Measurable (armFormula b) := by
  by_cases hb : b.val = 0
  · have he : armFormula b = rayFormula := by
      funext y
      simp [armFormula, hb]
    rw [he]
    exact measurable_rayFormula
  · have he : armFormula b = upFormula := by
      funext y
      simp [armFormula, hb]
    rw [he]
    exact measurable_upFormula

private lemma armFormula_ae_eq (b : Fin 3) :
    starArmPsi b =ᵐ[volume.restrict (Ioi (0:ℝ))] armFormula b := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  by_cases hb0 : b.val = 0
  · simp [starArmPsi, armFormula, hb0, rayFormula_eq]
  · by_cases hb1 : b.val = 1
    · simp [starArmPsi, armFormula, hb0, hb1, upFormula_eq y hy.le]
    · simp [starArmPsi, armFormula, hb0, hb1, psi_reflection,
        upFormula_eq y hy.le]

def starSpatialIntegrand (n : ℕ) (b : Fin 3) (y : ℝ) : ℝ :=
  (1+y)^6 * Real.exp ((n:ℝ)*starArmPsi b y)

private lemma starSpatialIntegrand_ae (n : ℕ) (b : Fin 3) :
    AEStronglyMeasurable (starSpatialIntegrand n b)
      (volume.restrict (Ioi (0:ℝ))) := by
  have hm : Measurable (fun y : ℝ =>
      (1+y)^6 * Real.exp ((n:ℝ)*armFormula b y)) := by
    have hf := measurable_armFormula b
    fun_prop
  have he : starSpatialIntegrand n b =ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun y : ℝ => (1+y)^6 * Real.exp ((n:ℝ)*armFormula b y)) := by
    filter_upwards [armFormula_ae_eq b] with y hy
    simp only [starSpatialIntegrand, hy]
  exact hm.aestronglyMeasurable.congr he.symm

private def spatialMajorant (y : ℝ) : ℝ :=
  Real.exp (9/5:ℝ) * ((1+|y|)^6 * Real.exp (-|y|/10))

private lemma integrable_spatialMajorant : Integrable spatialMajorant := by
  convert (Li2.original_integrable_one_add_abs_pow_exp 6
    (by norm_num : (0:ℝ)<1/10)).const_mul (Real.exp (9/5:ℝ)) using 1
  funext y
  unfold spatialMajorant
  congr 2
  ring

theorem starArm_integral_bound (n : ℕ) (hn : 1 ≤ n) (b : Fin 3) :
    IntegrableOn (starSpatialIntegrand n b) (Ioi (0:ℝ)) ∧
      (∫ y in Ioi (0:ℝ), starSpatialIntegrand n b y) ≤
        Real.exp ((n:ℝ)*(19/10:ℝ)) *
          (∫ y in Ioi (0:ℝ), spatialMajorant y) := by
  have hM : IntegrableOn (fun y : ℝ =>
      Real.exp ((n:ℝ)*(19/10:ℝ)) * spatialMajorant y) (Ioi (0:ℝ)) :=
    (integrable_spatialMajorant.const_mul _).integrableOn
  have hF : IntegrableOn (starSpatialIntegrand n b) (Ioi (0:ℝ)) := by
    apply hM.mono' (starSpatialIntegrand_ae n b)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      unfold starSpatialIntegrand
      positivity)]
    simpa only [spatialMajorant, starSpatialIntegrand] using
      starArm_exp_majorant n hn b y hy.le
  refine ⟨hF, ?_⟩
  have hle : (∫ y in Ioi (0:ℝ), starSpatialIntegrand n b y) ≤
      ∫ y in Ioi (0:ℝ),
        Real.exp ((n:ℝ)*(19/10:ℝ)) * spatialMajorant y := by
    apply integral_mono_ae hF hM
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simpa only [spatialMajorant, starSpatialIntegrand] using
      starArm_exp_majorant n hn b y hy.le
  simpa only [integral_const_mul] using hle

/-- Sum of the three actual spatial integrals. -/
def starSpatialIntegral (n : ℕ) : ℝ :=
  ∑ b : Fin 3, ∫ y in Ioi (0:ℝ), starSpatialIntegrand n b y

/-- A single constant controls every spatial integral at the exact exponent `19/10`. -/
theorem starSpatialIntegral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      starSpatialIntegral n ≤ C * Real.exp ((n:ℝ)*(19/10:ℝ)) := by
  let C₀ : ℝ := ∫ y in Ioi (0:ℝ), spatialMajorant y
  have hC₀ : 0 ≤ C₀ := by
    exact integral_nonneg (fun y => by unfold spatialMajorant; positivity)
  refine ⟨3*C₀+1, by linarith, ?_⟩
  intro n hn
  have hsum : starSpatialIntegral n ≤
      ∑ _b : Fin 3, Real.exp ((n:ℝ)*(19/10:ℝ))*C₀ := by
    unfold starSpatialIntegral
    apply Finset.sum_le_sum
    intro b _
    exact (starArm_integral_bound n hn b).2
  have hs : (∑ _b : Fin 3, Real.exp ((n:ℝ)*(19/10:ℝ))*C₀) =
      3*(Real.exp ((n:ℝ)*(19/10:ℝ))*C₀) := by simp
  rw [hs] at hsum
  have he := Real.exp_pos ((n:ℝ)*(19/10:ℝ))
  nlinarith

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.starArm_spatial_bounds
#print axioms Li2Unified.Proofs.Arithmetic.starArm_exp_majorant
#print axioms Li2Unified.Proofs.Arithmetic.starArm_integral_bound
#print axioms Li2Unified.Proofs.Arithmetic.starSpatialIntegral_bound

end


end
