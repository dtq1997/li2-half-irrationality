module
public import Li2Unified.Modular.Base.FiniteVandermondeScale
public import Li2Unified.Modular.Base.OriginalContourNormBound

set_option backward.privateInPublic true

@[expose] public section

open Polynomial MeasureTheory
open scoped BigOperators
namespace Li2
noncomputable section

private lemma originalContour_norm_integrand_scale (n : ℕ) (x : Fin (2 * n) → ℝ) :
    (∏ k : Fin (2 * n), ‖originalContourDensity n ((n : ℝ) * x k)‖) *
      (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, ((n : ℝ) * x j - (n : ℝ) * x i)) ^ 2 =
    (n : ℝ) ^ ((2 * n) * (2 * n - 1)) *
      ((∏ k : Fin (2 * n), ‖originalContourDensity n ((n : ℝ) * x k)‖) *
        (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, (x j - x i)) ^ 2) := by
  rw [vandermonde_sq_mul_scale]
  ring

theorem integrable_originalContour_scaled_norm_vandermonde (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun x : Fin (2 * n) → ℝ =>
        (∏ k : Fin (2 * n), ‖originalContourDensity n ((n : ℝ) * x k)‖) *
          (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, (x j - x i)) ^ 2)
      (Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ)) := by
  have hnNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnNat
  let μ : Measure (Fin (2 * n) → ℝ) := Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ)
  let F : (Fin (2 * n) → ℝ) → ℝ := fun x =>
    (∏ k : Fin (2 * n), ‖originalContourDensity n (x k)‖) *
      (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, (x j - x i)) ^ 2
  let G : (Fin (2 * n) → ℝ) → ℝ := fun x =>
    (∏ k : Fin (2 * n), ‖originalContourDensity n ((n : ℝ) * x k)‖) *
      (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, (x j - x i)) ^ 2
  change Integrable G μ
  have hcomp : Integrable (fun x : Fin (2 * n) → ℝ => F (fun i => (n : ℝ) * x i)) μ :=
    (integrable_pi_mul_scale_iff (2 * n) (n : ℝ) hnR.ne' F).2
      (integrable_originalContour_norm_vandermonde n)
  have hconst : Integrable (fun x : Fin (2 * n) → ℝ =>
          (n : ℝ) ^ ((2 * n) * (2 * n - 1)) * G x) μ :=
    hcomp.congr (Filter.Eventually.of_forall (fun x => originalContour_norm_integrand_scale n x))
  have hsmul : Integrable (fun x : Fin (2 * n) → ℝ =>
          (n : ℝ) ^ ((2 * n) * (2 * n - 1)) • G x) μ := by
    simpa only [smul_eq_mul] using hconst
  exact (MeasureTheory.integrable_fun_smul_iff (μ := μ) (pow_ne_zero _ hnR.ne') G).mp hsmul

theorem originalContour_norm_integral_scale (n : ℕ) (hn : 1 ≤ n) :
    (∫ x : Fin (2 * n) → ℝ,
      (∏ k : Fin (2 * n), ‖originalContourDensity n (x k)‖) *
        (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, (x j - x i)) ^ 2
      ∂(Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ))) =
    (n : ℝ) ^ ((2 * n) ^ 2) * (∫ x : Fin (2 * n) → ℝ,
        (∏ k : Fin (2 * n), ‖originalContourDensity n ((n : ℝ) * x k)‖) *
          (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, (x j - x i)) ^ 2
        ∂(Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ))) := by
  have hnNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnNat
  let μ : Measure (Fin (2 * n) → ℝ) := Measure.pi fun _ : Fin (2 * n) => (volume : Measure ℝ)
  let F : (Fin (2 * n) → ℝ) → ℝ := fun x =>
    (∏ k : Fin (2 * n), ‖originalContourDensity n (x k)‖) *
      (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, (x j - x i)) ^ 2
  let G : (Fin (2 * n) → ℝ) → ℝ := fun x =>
    (∏ k : Fin (2 * n), ‖originalContourDensity n ((n : ℝ) * x k)‖) *
      (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, (x j - x i)) ^ 2
  change (∫ x, F x ∂μ) = (n : ℝ) ^ ((2 * n) ^ 2) * (∫ x, G x ∂μ)
  have hinner : (∫ x : Fin (2 * n) → ℝ, F (fun i => (n : ℝ) * x i) ∂μ) =
      (n : ℝ) ^ ((2 * n) * (2 * n - 1)) * (∫ x, G x ∂μ) := by
    calc
      _ = ∫ x : Fin (2 * n) → ℝ, (n : ℝ) ^ ((2 * n) * (2 * n - 1)) * G x ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => originalContour_norm_integrand_scale n x))
      _ = _ := MeasureTheory.integral_const_mul (μ := μ) ((n : ℝ) ^ ((2 * n) * (2 * n - 1))) G
  have hh : 1 ≤ 2 * n := by omega
  have hexp : 2 * n + (2 * n) * (2 * n - 1) = (2 * n) ^ 2 := by
    calc
      2 * n + (2 * n) * (2 * n - 1) = (2 * n) * ((2 * n - 1) + 1) := by ring
      _ = (2 * n) ^ 2 := by rw [Nat.sub_add_cancel hh]; ring
  calc
    (∫ x, F x ∂μ) = (n : ℝ) ^ (2 * n) *
          (∫ x : Fin (2 * n) → ℝ, F (fun i => (n : ℝ) * x i) ∂μ) :=
      integral_pi_mul_scale (2 * n) (n : ℝ) hnR F
    _ = (n : ℝ) ^ (2 * n) * ((n : ℝ) ^ ((2 * n) * (2 * n - 1)) * (∫ x, G x ∂μ)) :=
      congrArg (fun z : ℝ => (n : ℝ) ^ (2 * n) * z) hinner
    _ = (n : ℝ) ^ ((2 * n) ^ 2) * (∫ x, G x ∂μ) := by
      rw [← mul_assoc, ← pow_add, hexp]

end
end Li2

end
