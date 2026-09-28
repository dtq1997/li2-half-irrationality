module
public import Li2Unified.Modular.Positive.Packed.P187
public import Li2Unified.Modular.Positive.Packed.P194
public import Li2Unified.Modular.Positive.Packed.P189
public import Li2Unified.Modular.Base.CirclePairLog
public import Li2Unified.Modular.Positive.Packed.P185
public import Li2Unified.Modular.Positive.Packed.P193

set_option backward.privateInPublic true

@[expose] public section

section
/-! Every ordered pair in the actual finite circle/layer signed profile has a
jointly integrable weighted logarithmic kernel. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

theorem integrable_starProfilePairKernel (h : ℕ) (x : Fin h → ℂ)
    {ε : ℝ} (hε : 0 < ε) (k l : starProfileIndex h) :
    Integrable (fun p : ℝ × ℝ =>
      starProfileDensity h k p.1 * starProfileDensity h l p.2 *
        Real.log ‖starProfileCurve h x ε k p.1 -
          starProfileCurve h x ε l p.2‖) (μcirc.prod μcirc) := by
  cases k with
  | inl i =>
      cases l with
      | inl j =>
          have hi := (Li2.integrable_circle_pair_log (x i) (x j) hε).const_mul
            ((2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹)
          simpa only [starProfileDensity, starProfileCurve] using! hi
      | inr j =>
          simpa only [starProfileDensity, starProfileCurve, circleLayerPairKernel]
            using! integrable_circleLayerPairKernel (x i) ε
              (List.get_mem layerData j)
  | inr i =>
      cases l with
      | inl j =>
          have hi := (integrable_circleLayerPairKernel (x j) ε
            (List.get_mem layerData i)).swap
          apply hi.congr
          exact Filter.Eventually.of_forall (fun p => by
            change (2 * Real.pi)⁻¹ * starLayerAngularDensity (layerData.get i) *
                Real.log ‖circleMap (x j) ε p.2 - starLayerCurve (layerData.get i) p.1‖ =
              starLayerAngularDensity (layerData.get i) * (2 * Real.pi)⁻¹ *
                Real.log ‖starLayerCurve (layerData.get i) p.1 - circleMap (x j) ε p.2‖
            rw [norm_sub_rev]
            ring)
      | inr j =>
          simpa only [starProfileDensity, starProfileCurve, angularLayerPairKernel]
            using! integrable_angularLayerPairKernel
              (List.get_mem layerData i) (List.get_mem layerData j)

end
end Li2Unified.Proofs.Contour

end

section
/-! Logarithmic energy for nonconstant curve densities.
The product-log integrability and pairwise a.e. noncollision hypotheses are
explicit. Actual curve/measure applications must establish them separately. -/
open MeasureTheory Set Real intervalIntegral Filter Topology
namespace Li2Unified.ParameterFamily.Energy
noncomputable section
variable {ι : Type*}

lemma weightedPairInt_eq_prod (ρ : ι → ℝ → ℝ) (γ : ι → ℝ → ℂ)
    (f : ℂ → ℂ → ℝ) (k l : ι)
    (hf : Integrable (fun p : ℝ × ℝ => ρ k p.1 * ρ l p.2 * f (γ k p.1) (γ l p.2))
      (μcirc.prod μcirc)) :
    weightedPairInt ρ γ f k l =
      ∫ p : ℝ × ℝ, ρ k p.1 * ρ l p.2 * f (γ k p.1) (γ l p.2) ∂(μcirc.prod μcirc) := by
  unfold weightedPairInt
  rw [integral_prod _ hf, intervalIntegral.integral_of_le (by positivity)]
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*π)]

lemma integrable_weighted_log_of_integrable {ρ : ι → ℝ → ℝ} (γ : ι → ℝ → ℂ)
    {C : ℝ} (hρ : ∀ k, Continuous (ρ k)) (hρ0 : ∀ k θ, 0 ≤ ρ k θ)
    (hC : 0 ≤ C) (hρC : ∀ k θ, ρ k θ ≤ C) (k l : ι)
    (hint : Integrable (fun p : ℝ × ℝ => Real.log ‖γ k p.1-γ l p.2‖) (μcirc.prod μcirc)) :
    Integrable (fun p : ℝ × ℝ => ρ k p.1 * ρ l p.2 * Real.log ‖γ k p.1-γ l p.2‖)
      (μcirc.prod μcirc) := by
  refine hint.bdd_mul (c := C^2)
    (((hρ k).comp continuous_fst).mul ((hρ l).comp continuous_snd)).aestronglyMeasurable ?_
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ0 k p.1) (hρ0 l p.2))]
  simpa only [pow_two] using! mul_le_mul (hρC k p.1) (hρC l p.2) (hρ0 l p.2) hC

lemma tendsto_weightedPairInt_Ltr {ρ : ι → ℝ → ℝ} {γ : ι → ℝ → ℂ}
    (hρ : ∀ k, Continuous (ρ k)) (hγ : ∀ k, Continuous (γ k)) (k l : ι)
    (hint : Integrable (fun p : ℝ × ℝ => ρ k p.1 * ρ l p.2 * Real.log ‖γ k p.1-γ l p.2‖)
      (μcirc.prod μcirc))
    (hae : ∀ᵐ p ∂(μcirc.prod μcirc), γ k p.1 ≠ γ l p.2) :
    Tendsto (fun n : ℕ => weightedPairInt ρ γ
      (fun z w => Ltr (1/((n:ℝ)+1)) ((n:ℝ)+1) ‖z-w‖) k l)
      atTop (𝓝 (weightedPairInt ρ γ (fun z w => Real.log ‖z-w‖) k l)) := by
  have hn : ∀ n : ℕ, (0:ℝ) < 1/((n:ℝ)+1) := fun n => by positivity
  have hn' : ∀ n : ℕ, 1/((n:ℝ)+1) ≤ (n:ℝ)+1 := fun n => by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hcont (n : ℕ) : Continuous fun p : ℝ × ℝ => ρ k p.1 * ρ l p.2 *
      Ltr (1/((n:ℝ)+1)) ((n:ℝ)+1) ‖γ k p.1-γ l p.2‖ :=
    (((hρ k).comp continuous_fst).mul ((hρ l).comp continuous_snd)).mul
      ((continuous_Ltr (hn n) (hn' n)).comp (by fun_prop))
  rw [weightedPairInt_eq_prod ρ γ _ k l hint]
  have he (n : ℕ) : weightedPairInt ρ γ
      (fun z w => Ltr (1/((n:ℝ)+1)) ((n:ℝ)+1) ‖z-w‖) k l =
      ∫ p : ℝ × ℝ, ρ k p.1 * ρ l p.2 *
        Ltr (1/((n:ℝ)+1)) ((n:ℝ)+1) ‖γ k p.1-γ l p.2‖ ∂(μcirc.prod μcirc) :=
    weightedPairInt_eq_prod ρ γ _ k l (integrable_of_continuous_torus (hcont n))
  simp_rw [he]
  refine tendsto_integral_of_dominated_convergence
    (fun p => |ρ k p.1 * ρ l p.2 * Real.log ‖γ k p.1-γ l p.2‖|)
    (fun n => (hcont n).aestronglyMeasurable) hint.abs ?_ ?_
  · intro n
    filter_upwards [hae] with p hp
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_Ltr_le (hn n) (hn' n) (norm_pos_iff.mpr (sub_ne_zero.mpr hp)))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · filter_upwards [hae] with p hp
    exact (tendsto_Ltr (norm_pos_iff.mpr (sub_ne_zero.mpr hp))).const_mul _

theorem weighted_energy_log_nonpos [Fintype ι] {s : ι → ℝ}
    {ρ : ι → ℝ → ℝ} {γ : ι → ℝ → ℂ} {C R : ℝ}
    (hρ : ∀ k, Continuous (ρ k)) (hγ : ∀ k, Continuous (γ k))
    (hρ0 : ∀ k θ, 0 ≤ ρ k θ) (hC : 0 ≤ C) (hρC : ∀ k θ, ρ k θ ≤ C)
    (hR : ∀ k θ, ‖γ k θ‖ ≤ R) (hmass : ∑ k, s k*densityMass ρ k = 0)
    (hint : ∀ k l, Integrable (fun p : ℝ × ℝ =>
      ρ k p.1 * ρ l p.2 * Real.log ‖γ k p.1-γ l p.2‖) (μcirc.prod μcirc))
    (hae : ∀ k l, ∀ᵐ p ∂(μcirc.prod μcirc), γ k p.1 ≠ γ l p.2) :
    weightedEnergy s ρ γ (fun z w => Real.log ‖z-w‖) ≤ 0 := by
  have hn : ∀ n : ℕ, (0:ℝ) < 1/((n:ℝ)+1) := fun n => by positivity
  have hn' : ∀ n : ℕ, 1/((n:ℝ)+1) ≤ (n:ℝ)+1 := fun n => by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hle (n : ℕ) : weightedEnergy s ρ γ
      (fun z w => Ltr (1/((n:ℝ)+1)) ((n:ℝ)+1) ‖z-w‖) ≤ 0 :=
    weighted_energy_Ltr_nonpos hρ hγ hρ0 hC hρC hR hmass (hn n) (hn' n)
  have hlim : Tendsto (fun n : ℕ => weightedEnergy s ρ γ
      (fun z w => Ltr (1/((n:ℝ)+1)) ((n:ℝ)+1) ‖z-w‖))
      atTop (𝓝 (weightedEnergy s ρ γ (fun z w => Real.log ‖z-w‖))) := by
    unfold weightedEnergy
    refine tendsto_finset_sum _ fun k _ => tendsto_finset_sum _ fun l _ => ?_
    exact (tendsto_weightedPairInt_Ltr hρ hγ k l (hint k l) (hae k l)).const_mul _
  exact le_of_tendsto' hlim hle

end
end Li2Unified.ParameterFamily.Energy

end

section
/-! Conditional negative logarithmic energy for the actual finite family of
particle circles and all 36 comparison layers. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy

theorem starProfileEnergy_nonpos (h : ℕ) (x : Fin h → ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    weightedEnergy (starProfileSign h) (starProfileDensity h)
      (starProfileCurve h x ε) (fun z w : ℂ => Real.log ‖z - w‖) ≤ 0 := by
  exact weighted_energy_log_nonpos
    (s := starProfileSign h)
    (ρ := starProfileDensity h)
    (γ := starProfileCurve h x ε)
    (C := starProfileDensityBound h)
    (R := starProfileCurveBound h x ε)
    (continuous_starProfileDensity h)
    (continuous_starProfileCurve h x ε)
    (starProfileDensity_nonneg h)
    (starProfileDensityBound_nonneg h)
    (starProfileDensity_le h)
    (starProfileCurve_norm_le h x ε)
    (starProfile_zero_mass h)
    (integrable_starProfilePairKernel h x hε)
    (starProfile_ae_ne h x hε)

end
end Li2Unified.Proofs.Contour

end

section
/-! Compress the actual 36-layer negative profile into one Option block while
preserving its nonpositive logarithmic energy. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Proofs.Measure

theorem starProfileBlock_energy_nonpos {h : ℕ} (hh : 0 < h)
    (x : Fin h → ℂ) {ε : ℝ} (hε : 0 < ε) :
    let P : starProfileIndex h → starProfileIndex h → ℝ :=
      fun k l => weightedPairInt (starProfileDensity h)
        (starProfileCurve h x ε) (fun z w : ℂ => Real.log ‖z - w‖) k l
    let E := starProfileBlock (2 * Real.pi) P
    let w : Option (Fin h) → ℝ := fun k => match k with
      | none => -1 | some _ => 1 / ((h : ℝ) * (2 * Real.pi))
    (∑ k : Option (Fin h), ∑ l : Option (Fin h),
      w k * w l * E k l) ≤ 0 := by
  let P : starProfileIndex h → starProfileIndex h → ℝ :=
    fun k l => weightedPairInt (starProfileDensity h)
      (starProfileCurve h x ε) (fun z w : ℂ => Real.log ‖z - w‖) k l
  have hT : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hb := starProfileBlock_energy hh (2 * Real.pi) hT P
  have he := starProfileEnergy_nonpos h x hε
  dsimp only [weightedEnergy, starProfileSign, P] at he
  dsimp only [P] at hb ⊢
  exact hb.le.trans (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) he)

end
end Li2Unified.Proofs.Contour

end


end
