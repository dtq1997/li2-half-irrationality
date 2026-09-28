module
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Ring

set_option backward.privateInPublic true

@[expose] public section

/-! Pairwise moments imply integrability of the full determinant product.
The measurable source is arbitrary so the same theorem serves all four instances. -/
open MeasureTheory Finset Equiv

namespace Li2.Andreief

variable {α : Type*} [MeasurableSpace α]
variable {n : ℕ} {μ : Measure α} [SigmaFinite μ]
variable {𝕜 : Type*} [RCLike 𝕜]

theorem integrable_det_mul_det
    (f g : Fin n → α → 𝕜)
    (hfg : ∀ i j, Integrable (fun x => f i x * g j x) μ) :
    Integrable
      (fun x : Fin n → α =>
        (Matrix.of fun i j => f i (x j)).det *
          (Matrix.of fun i j => g i (x j)).det)
      (Measure.pi fun _ : Fin n => μ) := by
  classical
  have hint : ∀ σ τ : Perm (Fin n), Integrable
      (fun x : Fin n → α =>
        (Perm.sign σ : 𝕜) * (Perm.sign τ : 𝕜) *
          ((∏ i, f (σ i) (x i)) * (∏ i, g (τ i) (x i))))
      (Measure.pi fun _ : Fin n => μ) := by
    intro σ τ
    have hprod :
        (fun x : Fin n → α =>
          (∏ i, f (σ i) (x i)) * (∏ i, g (τ i) (x i))) =
        (fun x => ∏ i, (fun i y => f (σ i) y * g (τ i) y) i (x i)) := by
      funext x
      simp only [← Finset.prod_mul_distrib]
    refine Integrable.const_mul ?_ _
    rw [hprod]
    exact Integrable.fintype_prod fun i => hfg (σ i) (τ i)
  have hpt : ∀ x : Fin n → α,
      (Matrix.of fun i j => f i (x j)).det *
          (Matrix.of fun i j => g i (x j)).det =
        ∑ τ : Perm (Fin n), ∑ σ : Perm (Fin n),
          (Perm.sign σ : 𝕜) * (Perm.sign τ : 𝕜) *
            ((∏ i, f (σ i) (x i)) * (∏ i, g (τ i) (x i))) := by
    intro x
    rw [Matrix.det_apply', Matrix.det_apply',
      Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ =>
      Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.of_apply]
    ring
  simp_rw [hpt]
  exact integrable_finset_sum _ fun τ _ =>
    integrable_finset_sum _ fun σ _ => hint σ τ

end Li2.Andreief

end
