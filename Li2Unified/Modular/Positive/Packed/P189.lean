module
public import Li2Unified.Modular.Positive.Packed.P188
public import Li2Unified.Modular.Positive.Packed.P183
public import Li2Unified.Modular.Positive.Packed.P186

set_option backward.privateInPublic true

@[expose] public section

section
/-! Truncated energy for nonconstant nonnegative curve densities.
The zero-mass premise uses the actual density integrals, not just the sum
of scalar coefficients. Angular measure remains unnormalized. -/
open MeasureTheory Set Real intervalIntegral
namespace Li2Unified.ParameterFamily.Energy
noncomputable section
variable {ι : Type*}

def densityMass (ρ : ι → ℝ → ℝ) (k : ι) : ℝ := ∫ θ in (0:ℝ)..2*π, ρ k θ

def weightedPairInt (ρ : ι → ℝ → ℝ) (γ : ι → ℝ → ℂ)
    (f : ℂ → ℂ → ℝ) (k l : ι) : ℝ :=
  ∫ θ in (0:ℝ)..2*π, ∫ φ in (0:ℝ)..2*π, ρ k θ * ρ l φ * f (γ k θ) (γ l φ)

def weightedEnergy [Fintype ι] (s : ι → ℝ) (ρ : ι → ℝ → ℝ)
    (γ : ι → ℝ → ℂ) (f : ℂ → ℂ → ℝ) : ℝ :=
  ∑ k, ∑ l, s k * s l * weightedPairInt ρ γ f k l

lemma weightedPairInt_const (ρ : ι → ℝ → ℝ) (γ : ι → ℝ → ℂ) (c : ℝ) (k l : ι) :
    weightedPairInt ρ γ (fun _ _ => c) k l = c * densityMass ρ k * densityMass ρ l := by
  unfold weightedPairInt densityMass
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
  ring

lemma continuous_weightedGk {ρ : ι → ℝ → ℝ} {γ : ι → ℝ → ℂ}
    (hρ : ∀ k, Continuous (ρ k)) (hγ : ∀ k, Continuous (γ k)) (k l : ι) :
    Continuous fun t => weightedGk ρ γ t k l := by
  unfold weightedGk
  apply continuous_parametric_intervalIntegral_of_continuous'
  apply continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

lemma weightedPairInt_Ltr {ρ : ι → ℝ → ℝ} {γ : ι → ℝ → ℂ}
    (hρ : ∀ k, Continuous (ρ k)) (hγ : ∀ k, Continuous (γ k))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k l : ι) :
    weightedPairInt ρ γ (fun z w => Ltr a b ‖z-w‖) k l =
      (1/2) * ∫ t in a..b,
        (Real.exp (-t) * densityMass ρ k * densityMass ρ l - weightedGk ρ γ t k l) / t := by
  have hrep (θ φ : ℝ) : ρ k θ * ρ l φ * Ltr a b ‖γ k θ-γ l φ‖ =
      (1/2) * ∫ t in a..b, ρ k θ * ρ l φ *
        ((Real.exp (-t)-Real.exp (-t*‖γ k θ-γ l φ‖^2)) * (max t a)⁻¹) := by
    rw [Ltr_eq_max ha hab, intervalIntegral.integral_const_mul]
    ring
  unfold weightedPairInt
  simp_rw [hrep, intervalIntegral.integral_const_mul (1/2 : ℝ)]
  congr 1
  have hinv := continuous_inv_max ha
  have hH (θ : ℝ) : Continuous (Function.uncurry fun φ t => ρ k θ * ρ l φ *
      ((Real.exp (-t)-Real.exp (-t*‖γ k θ-γ l φ‖^2)) * (max t a)⁻¹)) := by
    have he : Continuous fun p : ℝ × ℝ =>
        Real.exp (-p.2)-Real.exp (-p.2*‖γ k θ-γ l p.1‖^2) := by fun_prop
    have hw : Continuous fun p : ℝ × ℝ => ρ k θ * ρ l p.1 := by fun_prop
    exact hw.mul (he.mul (hinv.comp continuous_snd))
  have hswap (θ : ℝ) :
      (∫ φ in (0:ℝ)..2*π, ∫ t in a..b, ρ k θ * ρ l φ *
        ((Real.exp (-t)-Real.exp (-t*‖γ k θ-γ l φ‖^2)) * (max t a)⁻¹)) =
      ∫ t in a..b, ∫ φ in (0:ℝ)..2*π, ρ k θ * ρ l φ *
        ((Real.exp (-t)-Real.exp (-t*‖γ k θ-γ l φ‖^2)) * (max t a)⁻¹) :=
    intervalIntegral_swap_of_continuous (hH θ) (by positivity) hab
  simp_rw [hswap]
  have hH2 : Continuous (Function.uncurry fun (p : ℝ × ℝ) φ => ρ k p.1 * ρ l φ *
      ((Real.exp (-p.2)-Real.exp (-p.2*‖γ k p.1-γ l φ‖^2)) * (max p.2 a)⁻¹)) := by
    have he : Continuous fun q : (ℝ × ℝ) × ℝ =>
        Real.exp (-q.1.2)-Real.exp (-q.1.2*‖γ k q.1.1-γ l q.2‖^2) := by fun_prop
    have hw : Continuous fun q : (ℝ × ℝ) × ℝ => ρ k q.1.1 * ρ l q.2 := by fun_prop
    exact hw.mul (he.mul (hinv.comp (continuous_snd.comp continuous_fst)))
  rw [intervalIntegral_swap_of_continuous
    (f := fun θ t => ∫ φ in (0:ℝ)..2*π, ρ k θ * ρ l φ *
      ((Real.exp (-t)-Real.exp (-t*‖γ k θ-γ l φ‖^2)) * (max t a)⁻¹))
    (continuous_parametric_intervalIntegral_of_continuous' hH2 0 (2*π)) (by positivity) hab]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  simp only
  simp_rw [← mul_assoc, intervalIntegral.integral_mul_const]
  rw [max_eq_left ht.1, div_eq_mul_inv]
  congr 1
  have hs (θ : ℝ) :
      (∫ φ in (0:ℝ)..2*π, ρ k θ * ρ l φ *
        (Real.exp (-t)-Real.exp (-t*‖γ k θ-γ l φ‖^2))) =
      (∫ φ in (0:ℝ)..2*π, ρ k θ * ρ l φ * Real.exp (-t)) -
        ∫ φ in (0:ℝ)..2*π, ρ k θ * ρ l φ * Real.exp (-t*‖γ k θ-γ l φ‖^2) := by
    simp_rw [mul_sub]
    exact intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
  simp_rw [hs]
  rw [intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable
        apply continuous_parametric_intervalIntegral_of_continuous'; fun_prop)
    (by apply Continuous.intervalIntegrable
        apply continuous_parametric_intervalIntegral_of_continuous'; fun_prop)]
  change weightedPairInt ρ γ (fun _ _ => Real.exp (-t)) k l - weightedGk ρ γ t k l = _
  rw [weightedPairInt_const]

theorem weighted_energy_Ltr_nonpos [Fintype ι] {s : ι → ℝ}
    {ρ : ι → ℝ → ℝ} {γ : ι → ℝ → ℂ} {C R : ℝ}
    (hρ : ∀ k, Continuous (ρ k)) (hγ : ∀ k, Continuous (γ k))
    (hρ0 : ∀ k θ, 0 ≤ ρ k θ) (hC : 0 ≤ C) (hρC : ∀ k θ, ρ k θ ≤ C)
    (hR : ∀ k θ, ‖γ k θ‖ ≤ R) (hmass : ∑ k, s k * densityMass ρ k = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    weightedEnergy s ρ γ (fun z w => Ltr a b ‖z-w‖) ≤ 0 := by
  unfold weightedEnergy
  simp_rw [weightedPairInt_Ltr hρ hγ ha hab]
  have hc (k l : ι) : ContinuousOn (fun t =>
      (Real.exp (-t)*densityMass ρ k*densityMass ρ l-weightedGk ρ γ t k l)/t) (uIcc a b) := by
    rw [uIcc_of_le hab]
    apply ContinuousOn.div (Continuous.continuousOn (by
      have := continuous_weightedGk hρ hγ k l; fun_prop)) continuousOn_id
    intro t ht
    exact (ha.trans_le ht.1).ne'
  have he : (∑ k, ∑ l, s k*s l*((1/2)*∫ t in a..b,
      (Real.exp (-t)*densityMass ρ k*densityMass ρ l-weightedGk ρ γ t k l)/t)) =
      (1/2)*∫ t in a..b, ∑ k, ∑ l, s k*s l*
        ((Real.exp (-t)*densityMass ρ k*densityMass ρ l-weightedGk ρ γ t k l)/t) := by
    rw [intervalIntegral.integral_finset_sum
      (f := fun k t => ∑ l, s k*s l*
        ((Real.exp (-t)*densityMass ρ k*densityMass ρ l-weightedGk ρ γ t k l)/t))
      (fun k _ => (continuousOn_finset_sum _ fun l _ =>
        continuousOn_const.mul (hc k l)).intervalIntegrable), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_finset_sum
      (f := fun l t => s k*s l*
        ((Real.exp (-t)*densityMass ρ k*densityMass ρ l-weightedGk ρ γ t k l)/t))
      (fun l _ => (continuousOn_const.mul (hc k l)).intervalIntegrable), Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [he]
  have hpt : ∀ t ∈ Icc a b, 0 ≤ -(∑ k, ∑ l, s k*s l*
      ((Real.exp (-t)*densityMass ρ k*densityMass ρ l-weightedGk ρ γ t k l)/t)) := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have hJ := weighted_gaussian_energy_nonneg (s := s) hρ hγ hρ0 hC hρC hR ht0
    have hA : (∑ k, ∑ l, s k*s l*(Real.exp (-t)*densityMass ρ k*densityMass ρ l)) = 0 := by
      calc
        _ = Real.exp (-t)*(∑ k, s k*densityMass ρ k)^2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => by ring
        _ = 0 := by rw [hmass]; ring
    have hsum : (∑ k, ∑ l, s k*s l*
        ((Real.exp (-t)*densityMass ρ k*densityMass ρ l-weightedGk ρ γ t k l)/t)) =
        ((∑ k, ∑ l, s k*s l*(Real.exp (-t)*densityMass ρ k*densityMass ρ l)) -
          ∑ k, ∑ l, s k*s l*weightedGk ρ γ t k l)/t := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ => by ring
    rw [hsum, hA, zero_sub, neg_nonneg]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hJ) ht0.le
  have h := intervalIntegral.integral_nonneg (μ := volume) hab hpt
  rw [intervalIntegral.integral_neg] at h
  linarith

end
end Li2Unified.ParameterFamily.Energy

end

section
/-! The actual finite signed family of `h` particle circles and the fixed 36
comparison layers. This module records its exact angular masses. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

abbrev starProfileIndex (h : ℕ) := Fin h ⊕ Fin layerData.length

def starProfileSign (h : ℕ) : starProfileIndex h → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => -(h : ℝ))

def starProfileDensity (h : ℕ) : starProfileIndex h → ℝ → ℝ :=
  Sum.elim (fun _ _ => (2 * Real.pi)⁻¹)
    (fun j _ => starLayerAngularDensity (layerData.get j))

def starProfileCurve (h : ℕ) (x : Fin h → ℂ) (ε : ℝ) :
    starProfileIndex h → ℝ → ℂ :=
  Sum.elim (fun i => circleMap (x i) ε)
    (fun j => starLayerCurve (layerData.get j))

lemma starProfileDensity_circle_mass (h : ℕ) (i : Fin h) :
    densityMass (starProfileDensity h) (Sum.inl i) = 1 := by
  simp [densityMass, starProfileDensity, intervalIntegral.integral_const]
  field_simp [Real.pi_ne_zero]

lemma starProfileDensity_layer_mass (h : ℕ) (j : Fin layerData.length) :
    densityMass (starProfileDensity h) (Sum.inr j) =
      ((layerData.get j).mass : ℝ) := by
  exact starLayerAngularDensity_mass (layerData.get j)

private lemma starLayerMass_eq_sum (ss : List StarLayer) :
    (starLayerMass ss : ℝ) = (ss.map (fun s => (s.mass : ℝ))).sum := by
  induction ss with
  | nil => simp [starLayerMass]
  | cons s ss ih => simp [starLayerMass, ih]

lemma starProfileDensity_layers_mass (h : ℕ) :
    (∑ j : Fin layerData.length,
      densityMass (starProfileDensity h) (Sum.inr j)) = 1 := by
  simp_rw [starProfileDensity_layer_mass]
  have hfn :
      (List.ofFn fun j : Fin layerData.length =>
        ((layerData.get j).mass : ℝ)) =
        layerData.map (fun s => (s.mass : ℝ)) := by
    calc
      _ = (List.ofFn layerData.get).map (fun s => (s.mass : ℝ)) := by
        simp only [List.map_ofFn]
        rfl
      _ = _ := by rw [List.ofFn_get]
  rw [← List.sum_ofFn, hfn, ← starLayerMass_eq_sum]
  exact_mod_cast layerData_mass

lemma starProfile_zero_mass (h : ℕ) :
    (∑ k : starProfileIndex h,
      starProfileSign h k * densityMass (starProfileDensity h) k) = 0 := by
  rw [Fintype.sum_sum_type]
  change (∑ i : Fin h, (1 : ℝ) *
      densityMass (starProfileDensity h) (Sum.inl i)) +
    (∑ j : Fin layerData.length, -(h : ℝ) *
      densityMass (starProfileDensity h) (Sum.inr j)) = 0
  simp_rw [starProfileDensity_circle_mass]
  simp only [one_mul]
  rw [← Finset.mul_sum, starProfileDensity_layers_mass]
  simp

end
end Li2Unified.Proofs.Contour

end


end
