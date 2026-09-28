module
public import Li2Unified.Modular.Base.Valuation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

set_option backward.privateInPublic true

@[expose] public section

/-! generic tools.
(1) det(W*C) = sum over maps f of columns into the index set of
    (prod_b C (f b) b) * det(W restricted to the columns f), and non-injective f vanish.
(2) The resulting valuation bound: if every injective f has total weight >= B, then
    GV p det(W*C) >= B. Capacity limits are automatic: each index is one column of W.
(3) Slot counting: for monotone theta and injective g : Fin h -> ℕ,
    sum_{i<h} theta i <= sum_b theta (g b). -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

theorem det_mul_expand {R : Type*} [CommRing R] {h : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (W : Matrix (Fin h) I R) (Cm : Matrix I (Fin h) R) :
    (W * Cm).det = ∑ f : Fin h → I,
      (∏ b, Cm (f b) b) * (Matrix.of fun a b => W a (f b)).det := by
  rw [Matrix.det_apply]
  have hs : ∀ σ : Equiv.Perm (Fin h), ∏ i, (W * Cm) (σ i) i =
      ∑ f : Fin h → I, ∏ i, (W (σ i) (f i) * Cm (f i) i) := by
    intro σ
    simp only [Matrix.mul_apply]
    exact Fintype.prod_sum (fun i k => W (σ i) k * Cm k i)
  simp_rw [hs, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  rw [Matrix.det_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib, mul_smul_comm, mul_comm]
  rfl

lemma det_cols_eq_zero {R : Type*} [CommRing R] {h : ℕ} {I : Type*}
    (W : Matrix (Fin h) I R) (f : Fin h → I) (hf : ¬ Function.Injective f) :
    (Matrix.of fun a b => W a (f b)).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
    by_contra hcon
    push_neg at hcon
    exact hf fun i j h => hcon i j h
  exact Matrix.det_zero_of_column_eq hne fun k => by simp [hij]

theorem det_mul_GV (p : ℕ) [Fact p.Prime] {h : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (W : Matrix (Fin h) I ℚ[X]) (Cm : Matrix I (Fin h) ℚ[X]) (ω κ : I → ℚ)
    (hW : ∀ a i, GV p (W a i) (ω i)) (hC : ∀ i b, GV p (Cm i b) (κ i)) (B : ℚ)
    (hB : ∀ f : Fin h → I, Function.Injective f → B ≤ ∑ b, (ω (f b) + κ (f b))) :
    GV p (W * Cm).det B := by
  rw [det_mul_expand]
  apply GV.sum
  intro f _
  by_cases hf : Function.Injective f
  · have hprod : GV p (∏ b, Cm (f b) b) (∑ b, κ (f b)) := GV.prod _ fun b _ => hC (f b) b
    have hdet : GV p (Matrix.of fun a b => W a (f b)).det
        (∑ _a : Fin h, (0:ℚ) + ∑ b, ω (f b)) :=
      det_GV (p := p) _ (fun _ => 0) (fun b => ω (f b)) fun a b => by
        simpa using hW a (f b)
    simp only [Finset.sum_const_zero, zero_add] at hdet
    refine (hprod.mul hdet).mono ?_
    have := hB f hf
    rw [Finset.sum_add_distrib] at this
    linarith
  · rw [det_cols_eq_zero W f hf, mul_zero]
    exact GV.zero _

theorem sum_range_le_sum_finset (θ : ℕ → ℚ) (hθ : Monotone θ) :
    ∀ (h : ℕ) (S : Finset ℕ), S.card = h → ∑ i ∈ Finset.range h, θ i ≤ ∑ x ∈ S, θ x := by
  intro h
  induction h with
  | zero => intro S hS; rw [Finset.card_eq_zero.mp hS]; simp
  | succ h ih =>
    intro S hS
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    set t := S.max' hne with ht
    have htS : t ∈ S := S.max'_mem hne
    have hcard : (S.erase t).card = h := by rw [Finset.card_erase_of_mem htS]; omega
    have hsub : S ⊆ Finset.range (t+1) := fun x hx =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (S.le_max' x hx))
    have hht : h ≤ t := by
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      omega
    rw [Finset.sum_range_succ, ← Finset.add_sum_erase S θ htS]
    linarith [ih (S.erase t) hcard, hθ hht]

theorem sum_range_le_of_injective (θ : ℕ → ℚ) (hθ : Monotone θ) {h : ℕ} (g : Fin h → ℕ)
    (hg : Function.Injective g) : ∑ i ∈ Finset.range h, θ i ≤ ∑ b, θ (g b) := by
  classical
  have hc : (Finset.univ.image g).card = h := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have := sum_range_le_sum_finset θ hθ h _ hc
  rwa [Finset.sum_image fun x _ y _ hxy => hg hxy] at this

end
end Li2

end
