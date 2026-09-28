module
public import Li2Unified.Modular.Base.FiniteSignedEnergyAlgebra
public import Mathlib.Tactic.FieldSimp
public import Li2Unified.Modular.Positive.Packed.P190
public import Li2Unified.Modular.Positive.Packed.P192
public import Li2Unified.Modular.Positive.Packed.P189

set_option backward.privateInPublic true

@[expose] public section

section
open scoped BigOperators
namespace Li2Unified.Proofs.Measure
noncomputable section

/-- Compress all comparison layers into one negative block. -/
def starProfileBlock {h l : ℕ} (T : ℝ)
    (P : (Fin h ⊕ Fin l) → (Fin h ⊕ Fin l) → ℝ) :
    Option (Fin h) → Option (Fin h) → ℝ
  | some i, some j => T^2 * P (.inl i) (.inl j)
  | some i, none => T * ∑ j : Fin l, P (.inl i) (.inr j)
  | none, some i => T * ∑ j : Fin l, P (.inr j) (.inl i)
  | none, none => ∑ j : Fin l, ∑ k : Fin l, P (.inr j) (.inr k)

lemma starProfileBlock_symmetric {h l : ℕ} (T : ℝ)
    (P : (Fin h ⊕ Fin l) → (Fin h ⊕ Fin l) → ℝ)
    (hP : ∀ i j, P i j = P j i) :
    ∀ i j, starProfileBlock T P i j = starProfileBlock T P j i := by
  intro i j
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => simp only [starProfileBlock, hP]
  | some i =>
    cases j with
    | none => simp only [starProfileBlock, hP]
    | some j => simp only [starProfileBlock, hP]

lemma starProfile_signed_sum {h l : ℕ}
    (P : (Fin h ⊕ Fin l) → (Fin h ⊕ Fin l) → ℝ) :
    let s : (Fin h ⊕ Fin l) → ℝ := Sum.elim (fun _ => 1) (fun _ => -(h:ℝ))
    (∑ i : Fin h ⊕ Fin l, ∑ j : Fin h ⊕ Fin l, s i*s j*P i j) =
      (∑ i : Fin h, ∑ j : Fin h, P (.inl i) (.inl j)) -
      (h:ℝ)*(∑ i : Fin h, ∑ j : Fin l, P (.inl i) (.inr j)) -
      (h:ℝ)*(∑ i : Fin l, ∑ j : Fin h, P (.inr i) (.inl j)) +
      (h:ℝ)^2*(∑ i : Fin l, ∑ j : Fin l, P (.inr i) (.inr j)) := by
  classical
  dsimp only
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem starProfileBlock_energy {h l : ℕ} (hh : 0 < h) (T : ℝ) (hT : T ≠ 0)
    (P : (Fin h ⊕ Fin l) → (Fin h ⊕ Fin l) → ℝ) :
    let w : Option (Fin h) → ℝ := fun k => match k with
      | none => -1 | some _ => 1/((h:ℝ)*T)
    let s : (Fin h ⊕ Fin l) → ℝ := Sum.elim (fun _ => 1) (fun _ => -(h:ℝ))
    (∑ i : Option (Fin h), ∑ j : Option (Fin h), w i*w j*starProfileBlock T P i j) =
      (1/(h:ℝ))^2 *
        (∑ i : Fin h ⊕ Fin l, ∑ j : Fin h ⊕ Fin l, s i*s j*P i j) := by
  classical
  have hh0 : (h:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hh
  dsimp only
  simp only [Fintype.sum_option, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, starProfileBlock, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i : Fin h => fun j : Fin l => P (.inr j) (.inl i))]
  field_simp
  ring

end
end Li2Unified.Proofs.Measure
#print axioms Li2Unified.Proofs.Measure.starProfileBlock_energy
#print axioms Li2Unified.Proofs.Measure.starProfileBlock_symmetric

end

section
/-! The actual circle-to-comparison block satisfies the uniform potential
bound used in finite signed energy. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison
open Li2Unified.Proofs.Measure

theorem starProfileBlock_cross_le (h : ℕ) (x : Fin h → ℂ)
    {ε : ℝ} (hε : 0 < ε) (i : Fin h) :
    starProfileBlock (2 * Real.pi)
      (fun k l => weightedPairInt (starProfileDensity h)
        (starProfileCurve h x ε)
        (fun z w : ℂ => Real.log ‖z - w‖) k l) (some i) none ≤
      (2 * Real.pi) *
        (comparisonPotential (x i) + 11 / 10 * ε) := by
  change (2 * Real.pi) *
      (∑ j : Fin layerData.length,
        weightedPairInt (starProfileDensity h) (starProfileCurve h x ε)
          (fun z w : ℂ => Real.log ‖z - w‖) (.inl i) (.inr j)) ≤ _
  rw [starProfile_circle_layer_sum]
  exact mul_le_mul_of_nonneg_left
    (actual_circle_comparisonPotential_le (x i) hε)
    (by positivity)

end
end Li2Unified.Proofs.Contour

end

section
/-! Continuity, positivity and global bounds for the actual signed finite
circle/layer family, as required by the Gaussian energy theorem. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

def starProfileDensityBound (h : ℕ) : ℝ :=
  ∑ k : starProfileIndex h, starProfileDensity h k 0

def starProfileCurveBound (h : ℕ) (x : Fin h → ℂ) (ε : ℝ) : ℝ :=
  56 / 5 + |ε| + ∑ i : Fin h, ‖x i‖

private lemma starLayerAngularDensity_nonneg (s : StarLayer) (hs : s.Valid) :
    0 ≤ starLayerAngularDensity s := by
  have hd : (0 : ℝ) ≤ s.density := by exact_mod_cast hs.2
  unfold starLayerAngularDensity
  exact div_nonneg (mul_nonneg hd (sub_nonneg.mpr (s.left_le_right hs.1)))
    (by positivity)

theorem starProfileDensity_nonneg (h : ℕ) (k : starProfileIndex h) (θ : ℝ) :
    0 ≤ starProfileDensity h k θ := by
  cases k with
  | inl i =>
      change (0 : ℝ) ≤ (2 * Real.pi)⁻¹
      positivity
  | inr j =>
      change (0 : ℝ) ≤ starLayerAngularDensity (layerData.get j)
      exact starLayerAngularDensity_nonneg _
        (layerData_valid _ (List.get_mem layerData j))

theorem continuous_starProfileDensity (h : ℕ) (k : starProfileIndex h) :
    Continuous (starProfileDensity h k) := by
  cases k <;> exact continuous_const

theorem continuous_starProfileCurve (h : ℕ) (x : Fin h → ℂ)
    (ε : ℝ) (k : starProfileIndex h) :
    Continuous (starProfileCurve h x ε k) := by
  cases k with
  | inl i => exact continuous_circleMap (x i) ε
  | inr j => exact continuous_starLayerCurve (layerData.get j)

theorem starProfileDensityBound_nonneg (h : ℕ) :
    0 ≤ starProfileDensityBound h := by
  unfold starProfileDensityBound
  exact Finset.sum_nonneg (fun k _ => starProfileDensity_nonneg h k 0)

theorem starProfileDensity_le (h : ℕ) (k : starProfileIndex h) (θ : ℝ) :
    starProfileDensity h k θ ≤ starProfileDensityBound h := by
  have he : starProfileDensity h k θ = starProfileDensity h k 0 := by
    cases k <;> rfl
  rw [he]
  unfold starProfileDensityBound
  exact Finset.single_le_sum
    (fun j _ => starProfileDensity_nonneg h j 0) (Finset.mem_univ k)

theorem starProfileCurve_norm_le (h : ℕ) (x : Fin h → ℂ)
    (ε : ℝ) (k : starProfileIndex h) (θ : ℝ) :
    ‖starProfileCurve h x ε k θ‖ ≤ starProfileCurveBound h x ε := by
  have hsum : 0 ≤ ∑ i : Fin h, ‖x i‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg (x i))
  cases k with
  | inl i =>
      have hxi : ‖x i‖ ≤ ∑ j : Fin h, ‖x j‖ :=
        Finset.single_le_sum (fun j _ => norm_nonneg (x j)) (Finset.mem_univ i)
      have hc : ‖circleMap (x i) ε θ‖ ≤ ‖x i‖ + |ε| := by
        calc
          _ ≤ ‖x i‖ + ‖circleMap 0 ε θ‖ := by
            simpa only [circleMap, zero_add] using
              (norm_add_le (x i) (circleMap 0 ε θ))
          _ = _ := by rw [norm_circleMap_zero]
      change ‖circleMap (x i) ε θ‖ ≤ _
      unfold starProfileCurveBound
      linarith
  | inr j =>
      change ‖starLayerCurve (layerData.get j) θ‖ ≤ _
      have hs := layerData_valid _ (List.get_mem layerData j)
      have hr := (layerData_radii _ (List.get_mem layerData j)).2
      have h0 := starLayerCurve_norm_le (layerData.get j) hs θ
      unfold starProfileCurveBound
      have hr' : ((layerData.get j).radius : ℝ) ≤ 56 / 5 := by
        rw [show (56 / 5 : ℝ) = ((56 / 5 : ℚ) : ℝ) by norm_num]
        exact Rat.cast_le.mpr hr
      linarith [abs_nonneg ε]

end
end Li2Unified.Proofs.Contour

end


end
