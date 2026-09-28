module
public import Li2Unified.Modular.Base.FieldPoleCompatibility

set_option backward.privateInPublic true

@[expose] public section

/-! Finite linear assembly for the field-valued simple-pole functional. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

lemma field_sum_isRestricted (s : Finset κ) (f : κ → PowerSeries ℚ_[p])
    (hf : ∀ i ∈ s, PowerSeries.IsRestricted 1 (f i)) :
    PowerSeries.IsRestricted 1 (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact PowerSeries.IsRestricted.zero 1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PowerSeries.IsRestricted.add 1 (hf a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem fieldRestrictedMoment_sum (μ : ℕ → ℤ_[p]) (s : Finset κ)
    (f : κ → PowerSeries ℚ_[p]) (hf : ∀ i ∈ s, PowerSeries.IsRestricted 1 (f i)) :
    fieldRestrictedMoment μ (∑ i ∈ s, f i) = ∑ i ∈ s, fieldRestrictedMoment μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fieldRestrictedMoment]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fieldRestrictedMoment_add]
    · rw [ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    · exact hf a (Finset.mem_insert_self _ _)
    · exact field_sum_isRestricted s f (fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem fieldPoleFunctional_sum (μ : ℕ → ℤ_[p]) (w : ι → (ℚ_[p])[X])
    (s : Finset κ) (f : κ → PowerSeries ℚ_[p])
    (hf : ∀ i ∈ s, PowerSeries.IsRestricted 1 (f i)) (r : κ → ι → ℚ_[p]) :
    fieldPoleFunctional μ w (∑ i ∈ s, f i) (fun j => ∑ i ∈ s, r i j) =
      ∑ i ∈ s, fieldPoleFunctional μ w (f i) (r i) := by
  simp only [fieldPoleFunctional, fieldRestrictedMoment_sum μ s f hf,
    map_sum, Finset.sum_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm]

theorem fieldPoleNumerator_sum (c : ι → ℤ_[p]) (s : Finset κ)
    (f : κ → PowerSeries ℚ_[p]) (r : κ → ι → ℚ_[p]) :
    fieldPoleNumerator c (∑ i ∈ s, f i) (fun j => ∑ i ∈ s, r i j) =
      ∑ i ∈ s, fieldPoleNumerator c (f i) (r i) := by
  simp only [fieldPoleNumerator, map_sum, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 1
  exact map_sum Polynomial.coeToPowerSeries.ringHom _ _

end
end Li2

end
