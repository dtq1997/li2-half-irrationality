module
public import Li2Unified.Modular.Positive.Packed.P184

set_option backward.privateInPublic true

@[expose] public section

section
/-! Gaussian positivity for continuous bounded nonnegative densities
on finite curve families. Scalar coefficients may have either sign.
Angular measure is unnormalized; no zero-mass or logarithmic claim yet. -/
open MeasureTheory Set Real intervalIntegral
namespace Li2Unified.ParameterFamily.Energy
noncomputable section
variable {ι : Type*}

def weightedGk (ρ : ι → ℝ → ℝ) (γ : ι → ℝ → ℂ) (t : ℝ) (k l : ι) : ℝ :=
  ∫ θ in (0:ℝ)..2*π, ∫ φ in (0:ℝ)..2*π,
    ρ k θ * ρ l φ * Real.exp (-t * ‖γ k θ-γ l φ‖^2)

def weightedgk (ρ : ι → ℝ → ℝ) (γ : ι → ℝ → ℂ) (t : ℝ) (k : ι) (u : ℂ) : ℝ :=
  ∫ θ in (0:ℝ)..2*π, ρ k θ * Real.exp (-(2*t)*‖γ k θ-u‖^2)

lemma weightedgk_nonneg {ρ : ι → ℝ → ℝ} (hρ0 : ∀ k θ, 0 ≤ ρ k θ)
    (γ : ι → ℝ → ℂ) (t : ℝ) (k : ι) (u : ℂ) : 0 ≤ weightedgk ρ γ t k u :=
  intervalIntegral.integral_nonneg (by positivity) fun θ _ =>
    mul_nonneg (hρ0 k θ) (Real.exp_pos _).le

lemma continuous_weightedgk {ρ : ι → ℝ → ℝ} {γ : ι → ℝ → ℂ}
    (hρ : ∀ k, Continuous (ρ k)) (hγ : ∀ k, Continuous (γ k)) (t : ℝ) (k : ι) :
    Continuous (weightedgk ρ γ t k) := by
  unfold weightedgk
  apply continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

private lemma weighted_point_le {ρ : ι → ℝ → ℝ} {γ : ι → ℝ → ℂ} {C t : ℝ}
    (hC : 0 ≤ C) (hρC : ∀ k θ, ρ k θ ≤ C) (ht : 0 ≤ t) (k : ι) (θ : ℝ) (u : ℂ) :
    ρ k θ * Real.exp (-(2*t)*‖γ k θ-u‖^2) ≤ C := by
  have he : Real.exp (-(2*t)*‖γ k θ-u‖^2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg ‖γ k θ-u‖]
  simpa only [mul_one] using mul_le_mul (hρC k θ) he (Real.exp_pos _).le hC

lemma weightedgk_le_two_pi {ρ : ι → ℝ → ℝ} {γ : ι → ℝ → ℂ} {C : ℝ}
    (hρ : ∀ k, Continuous (ρ k)) (hγ : ∀ k, Continuous (γ k))
    (hC : 0 ≤ C) (hρC : ∀ k θ, ρ k θ ≤ C) {t : ℝ} (ht : 0 ≤ t) (k : ι) (u : ℂ) :
    weightedgk ρ γ t k u ≤ 2*π*C := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (a := 0) (b := 2*π)
    (f := fun θ => ρ k θ * Real.exp (-(2*t)*‖γ k θ-u‖^2)) (g := fun _ => C)
    (by positivity) (by apply Continuous.intervalIntegrable; fun_prop)
    intervalIntegral.intervalIntegrable_const (fun θ _ => weighted_point_le hC hρC ht k θ u)
  simpa only [weightedgk, intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h

lemma weightedgk_le_gaussian {ρ : ι → ℝ → ℝ} {γ : ι → ℝ → ℂ} {C R : ℝ}
    (hρ : ∀ k, Continuous (ρ k)) (hγ : ∀ k, Continuous (γ k))
    (hC : 0 ≤ C) (hρC : ∀ k θ, ρ k θ ≤ C) (hR : ∀ k θ, ‖γ k θ‖ ≤ R)
    {t : ℝ} (ht : 0 ≤ t) (k : ι) (u : ℂ) :
    weightedgk ρ γ t k u ≤ 2*π*C*Real.exp (2*t*R^2)*Real.exp (-t*‖u‖^2) := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (a := 0) (b := 2*π)
    (f := fun θ => ρ k θ * Real.exp (-(2*t)*‖γ k θ-u‖^2))
    (g := fun _ => C*(Real.exp (2*t*R^2)*Real.exp (-t*‖u‖^2)))
    (by positivity) (by apply Continuous.intervalIntegrable; fun_prop)
    intervalIntegral.intervalIntegrable_const (fun θ _ =>
      mul_le_mul (hρC k θ) (exp_gauss_le ht (hR k θ)) (Real.exp_pos _).le hC)
  rw [intervalIntegral.integral_const] at h
  simp only [sub_zero, smul_eq_mul] at h
  exact h.trans_eq (by ring)

lemma weightedGk_eq {ρ : ι → ℝ → ℝ} {γ : ι → ℝ → ℂ} {C R : ℝ}
    (hρ : ∀ k, Continuous (ρ k)) (hγ : ∀ k, Continuous (γ k))
    (hρ0 : ∀ k θ, 0 ≤ ρ k θ) (hC : 0 ≤ C) (hρC : ∀ k θ, ρ k θ ≤ C)
    (hR : ∀ k θ, ‖γ k θ‖ ≤ R) {t : ℝ} (ht : 0 < t) (k l : ι) :
    weightedGk ρ γ t k l =
      4*t/π * ∫ u : ℂ, weightedgk ρ γ t k u * weightedgk ρ γ t l u := by
  have hconv (z w : ℂ) : Real.exp (-t*‖z-w‖^2) =
      4*t/π * ∫ u : ℂ, Real.exp (-(2*t)*‖z-u‖^2)*Real.exp (-(2*t)*‖w-u‖^2) := by
    rw [gaussian_conv ht]
    field_simp
  have heq (θ φ : ℝ) : ρ k θ * ρ l φ * Real.exp (-t*‖γ k θ-γ l φ‖^2) =
      4*t/π * ∫ u : ℂ, (ρ k θ * Real.exp (-(2*t)*‖γ k θ-u‖^2)) *
        (ρ l φ * Real.exp (-(2*t)*‖γ l φ-u‖^2)) := by
    rw [hconv]
    calc
      _ = 4*t/π * (ρ k θ * ρ l φ * ∫ u : ℂ,
          Real.exp (-(2*t)*‖γ k θ-u‖^2)*Real.exp (-(2*t)*‖γ l φ-u‖^2)) := by ring
      _ = _ := by
        rw [← MeasureTheory.integral_const_mul]
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with u
        ring
  unfold weightedGk
  simp_rw [heq, intervalIntegral.integral_const_mul]
  congr 1
  have hinner (θ : ℝ) :
      (∫ φ in (0:ℝ)..2*π, ∫ u : ℂ,
        (ρ k θ * Real.exp (-(2*t)*‖γ k θ-u‖^2)) *
          (ρ l φ * Real.exp (-(2*t)*‖γ l φ-u‖^2))) =
      ∫ u : ℂ, (ρ k θ * Real.exp (-(2*t)*‖γ k θ-u‖^2)) * weightedgk ρ γ t l u := by
    rw [swap_interval_complex (c := t) (C := C^2*Real.exp (2*t*R^2))
      (by fun_prop) ht (by positivity)]
    · unfold weightedgk
      congr 1
      funext u
      rw [intervalIntegral.integral_const_mul]
    · intro φ _ u
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (hρ0 k θ) (Real.exp_pos _).le)
        (mul_nonneg (hρ0 l φ) (Real.exp_pos _).le))]
      calc
        _ ≤ C * (C*(Real.exp (2*t*R^2)*Real.exp (-t*‖u‖^2))) :=
          mul_le_mul (weighted_point_le hC hρC ht.le k θ u)
            (mul_le_mul (hρC l φ) (exp_gauss_le ht.le (hR l φ)) (Real.exp_pos _).le hC)
            (mul_nonneg (hρ0 l φ) (Real.exp_pos _).le) hC
        _ = _ := by ring
  simp_rw [hinner]
  rw [swap_interval_complex (c := t) (C := C^2*Real.exp (2*t*R^2)*(2*π))
    (by have := continuous_weightedgk hρ hγ t l; fun_prop) ht (by positivity)]
  · unfold weightedgk
    congr 1
    funext u
    rw [intervalIntegral.integral_mul_const]
  · intro θ _ u
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (hρ0 k θ) (Real.exp_pos _).le)
      (weightedgk_nonneg hρ0 γ t l u))]
    calc
      _ ≤ (C*(Real.exp (2*t*R^2)*Real.exp (-t*‖u‖^2))) * (2*π*C) :=
        mul_le_mul
          (mul_le_mul (hρC k θ) (exp_gauss_le ht.le (hR k θ)) (Real.exp_pos _).le hC)
          (weightedgk_le_two_pi hρ hγ hC hρC ht.le l u)
          (weightedgk_nonneg hρ0 γ t l u) (mul_nonneg hC (by positivity))
      _ = _ := by ring

theorem weighted_gaussian_energy_nonneg [Fintype ι] {s : ι → ℝ}
    {ρ : ι → ℝ → ℝ} {γ : ι → ℝ → ℂ} {C R : ℝ}
    (hρ : ∀ k, Continuous (ρ k)) (hγ : ∀ k, Continuous (γ k))
    (hρ0 : ∀ k θ, 0 ≤ ρ k θ) (hC : 0 ≤ C) (hρC : ∀ k θ, ρ k θ ≤ C)
    (hR : ∀ k θ, ‖γ k θ‖ ≤ R) {t : ℝ} (ht : 0 < t) :
    0 ≤ ∑ k, ∑ l, s k * s l * weightedGk ρ γ t k l := by
  simp_rw [weightedGk_eq hρ hγ hρ0 hC hρC hR ht]
  have hint (k l : ι) : Integrable (fun u : ℂ => weightedgk ρ γ t k u * weightedgk ρ γ t l u) := by
    have hg : Integrable (fun u : ℂ =>
        (2*π*C*Real.exp (2*t*R^2)*(2*π*C))*Real.exp (-t*‖(0:ℂ)-u‖^2)) :=
      (integrable_gaussC ht 0).const_mul _
    refine hg.mono'
      ((continuous_weightedgk hρ hγ t k).mul (continuous_weightedgk hρ hγ t l)).aestronglyMeasurable ?_
    filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weightedgk_nonneg hρ0 γ t k u)
      (weightedgk_nonneg hρ0 γ t l u))]
    simp only [zero_sub, norm_neg]
    calc
      _ ≤ (2*π*C*Real.exp (2*t*R^2)*Real.exp (-t*‖u‖^2))*(2*π*C) :=
        mul_le_mul (weightedgk_le_gaussian hρ hγ hC hρC hR ht.le k u)
          (weightedgk_le_two_pi hρ hγ hC hρC ht.le l u)
          (weightedgk_nonneg hρ0 γ t l u) (by positivity)
      _ = _ := by ring
  have he : ∑ k, ∑ l, s k * s l *
      (4*t/π * ∫ u : ℂ, weightedgk ρ γ t k u * weightedgk ρ γ t l u) =
      4*t/π * ∫ u : ℂ, (∑ k, s k * weightedgk ρ γ t k u)^2 := by
    have hs (u : ℂ) : (∑ k, s k * weightedgk ρ γ t k u)^2 =
        ∑ k, ∑ l, s k*s l*(weightedgk ρ γ t k u*weightedgk ρ γ t l u) := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    simp_rw [hs]
    rw [MeasureTheory.integral_finset_sum _
      (fun k _ => integrable_finset_sum _ (fun l _ => (hint k l).const_mul _))]
    simp_rw [MeasureTheory.integral_finset_sum _ (fun l _ => (hint _ l).const_mul _),
      MeasureTheory.integral_const_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [he]
  exact mul_nonneg (by positivity) (integral_nonneg fun u => sq_nonneg _)

end
end Li2Unified.ParameterFamily.Energy

end


end
