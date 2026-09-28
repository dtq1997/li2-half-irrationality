module
public import Li2Unified.Modular.Positive.Packed.P195
public import Li2Unified.Modular.Positive.Packed.P193
public import Li2Unified.Modular.Positive.Packed.P185
public import Li2Unified.Modular.Positive.Packed.P194
public import Li2Unified.Modular.Positive.Packed.P189
public import Li2Unified.Modular.Base.CirclePairLog

set_option backward.privateInPublic true

@[expose] public section

section
/-! Actual profile pair integrals are symmetric, with Fubini justified by the
joint L1 theorem for all four circle/layer pair types. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy

theorem starProfilePair_symmetric (h : ℕ) (x : Fin h → ℂ)
    {ε : ℝ} (hε : 0 < ε) (k l : starProfileIndex h) :
    weightedPairInt (starProfileDensity h) (starProfileCurve h x ε)
      (fun z w : ℂ => Real.log ‖z - w‖) k l =
    weightedPairInt (starProfileDensity h) (starProfileCurve h x ε)
      (fun z w : ℂ => Real.log ‖z - w‖) l k := by
  let F : ℝ → ℝ → ℝ := fun θ φ =>
    starProfileDensity h k θ * starProfileDensity h l φ *
      Real.log ‖starProfileCurve h x ε k θ - starProfileCurve h x ε l φ‖
  have hT : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  change (∫ θ in (0 : ℝ)..2 * Real.pi,
      ∫ φ in (0 : ℝ)..2 * Real.pi, F θ φ) = _
  calc
    _ = ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ θ in (0 : ℝ)..2 * Real.pi, F θ φ := by
      simpa only [F, intervalIntegral.integral_of_le hT] using
        (MeasureTheory.integral_integral_swap
          (f := F)
          (integrable_starProfilePairKernel h x hε k l))
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro φ _
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only [F]
      rw [norm_sub_rev]
      ring

end
end Li2Unified.Proofs.Contour

end

section
open MeasureTheory Set
namespace Li2Unified.Proofs.Measure
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Proofs.Contour
open Li2Unified.Instances.PosHalf.LayerComparison

def starProfilePair (h : ℕ) (x : Fin h → ℂ) (ε : ℝ)
    (k l : starProfileIndex h) : ℝ :=
  weightedPairInt (starProfileDensity h) (starProfileCurve h x ε)
    (fun z w : ℂ => Real.log ‖z - w‖) k l

theorem starProfileBlock_none_none (h : ℕ) (x : Fin h → ℂ) (ε : ℝ) :
    starProfileBlock (2 * Real.pi) (starProfilePair h x ε) none none =
      comparisonEnergy := by
  let F : Fin layerData.length → Fin layerData.length → ℝ → ℝ := fun j k θ =>
    ∫ φ in (0 : ℝ)..2 * Real.pi,
      starLayerAngularDensity (layerData.get j) *
        starLayerAngularDensity (layerData.get k) *
          Real.log ‖starLayerCurve (layerData.get j) θ -
            starLayerCurve (layerData.get k) φ‖
  have hT : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hP (j k : Fin layerData.length) :
      starProfilePair h x ε (.inr j) (.inr k) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, F j k θ := rfl
  have houter (j k : Fin layerData.length) :
      IntervalIntegrable (F j k) volume 0 (2 * Real.pi) := by
    have hi := (integrable_angularLayerPairKernel
      (List.get_mem layerData j) (List.get_mem layerData k)).integral_prod_left
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
    simpa only [F, μcirc, angularLayerPairKernel,
      intervalIntegral.integral_of_le hT] using hi
  have hrow (j : Fin layerData.length) (θ : ℝ) :
      (∑ k : Fin layerData.length, F j k θ) =
        starLayerAngularDensity (layerData.get j) *
          comparisonPotential (starLayerCurve (layerData.get j) θ) := by
    dsimp only [F]
    simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
    rw [← Finset.mul_sum]
    congr 1
    simpa only [intervalIntegral.integral_const_mul] using
      star_comparisonPotential_angular (starLayerCurve (layerData.get j) θ)
  dsimp only [starProfileBlock]
  simp_rw [hP]
  calc
    (∑ j : Fin layerData.length, ∑ k : Fin layerData.length,
      ∫ θ in (0 : ℝ)..2 * Real.pi, F j k θ) =
        ∑ j : Fin layerData.length,
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            ∑ k : Fin layerData.length, F j k θ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (intervalIntegral.integral_finset_sum (f := fun k => F j k)
        (fun k _ => houter j k)).symm
    _ = comparisonEnergy := by
      simp_rw [hrow]
      exact star_comparisonEnergy_angular

theorem starProfileBlock_circle_self (h : ℕ) (x : Fin h → ℂ) {ε : ℝ}
    (hε : 0 < ε) (i : Fin h) :
    starProfileBlock (2 * Real.pi) (starProfilePair h x ε) (some i) (some i) =
      (2 * Real.pi)^2 * Real.log ε := by
  have hcircle := Li2.circle_pair_log_self (x i) hε
  have hpair : starProfilePair h x ε (.inl i) (.inl i) =
      (2 * Real.pi)⁻¹ ^ 2 *
        (∫ θ in (0 : ℝ)..2 * Real.pi, ∫ φ in (0 : ℝ)..2 * Real.pi,
          Real.log ‖circleMap (x i) ε θ - circleMap (x i) ε φ‖) := by
    simp only [starProfilePair, weightedPairInt, starProfileDensity,
      starProfileCurve, Sum.elim_inl,
      intervalIntegral.integral_const_mul]
    ring
  simp only [starProfileBlock, hpair, hcircle]
  field_simp [Real.pi_ne_zero]

theorem starProfileBlock_circle_lower (h : ℕ) (x : Fin h → ℂ) {ε : ℝ}
    (hε : 0 < ε) (i j : Fin h) (hij : x i ≠ x j) :
    (2 * Real.pi)^2 * Real.log ‖x j - x i‖ ≤
      starProfileBlock (2 * Real.pi) (starProfilePair h x ε) (some i) (some j) := by
  have hcircle := Li2.circle_pair_log_lower (x i) (x j) hε hij
  have hpair : starProfilePair h x ε (.inl i) (.inl j) =
      (2 * Real.pi)⁻¹ ^ 2 *
        (∫ θ in (0 : ℝ)..2 * Real.pi, ∫ φ in (0 : ℝ)..2 * Real.pi,
          Real.log ‖circleMap (x i) ε θ - circleMap (x j) ε φ‖) := by
    simp only [starProfilePair, weightedPairInt, starProfileDensity,
      starProfileCurve, Sum.elim_inl,
      intervalIntegral.integral_const_mul]
    ring
  have hscale : (2 * Real.pi)^2 * ((2 * Real.pi)⁻¹ ^ 2) = 1 := by
    field_simp [Real.pi_ne_zero]
  rw [starProfileBlock, hpair]
  simpa only [← mul_assoc, hscale, one_mul, norm_sub_rev] using hcircle

#print axioms starProfileBlock_none_none
#print axioms starProfileBlock_circle_self
#print axioms starProfileBlock_circle_lower

end
end Li2Unified.Proofs.Measure

end


end
