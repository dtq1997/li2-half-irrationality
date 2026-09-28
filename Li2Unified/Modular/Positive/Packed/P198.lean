module
public import Li2Unified.Modular.Positive.Packed.P193
public import Li2Unified.Modular.Positive.Packed.P195
public import Li2Unified.Modular.Positive.Packed.P196
public import Li2Unified.Modular.Positive.Packed.P197

set_option backward.privateInPublic true

@[expose] public section

section
/-! A pointwise discrete logarithmic energy bound for distinct centers on the
actual 36-layer comparison measure. The radius error is explicit. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Proofs.Measure
open Li2Unified.Instances.PosHalf.LayerComparison

theorem starProfile_discrete_log_bound {h : ℕ} (hh : 0 < h)
    (x : Fin h → ℂ) {ε : ℝ} (hε : 0 < ε)
    (hinj : Function.Injective x) :
    2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i,
      Real.log ‖x j - x i‖) ≤
      2 * (h : ℝ) * (∑ i : Fin h, comparisonPotential (x i)) -
        (h : ℝ)^2 * comparisonEnergy -
        (h : ℝ) * Real.log ε +
        (11 / 5 : ℝ) * (h : ℝ)^2 * ε := by
  let E := starProfileBlock (2 * Real.pi) (starProfilePair h x ε)
  have hEsym : ∀ k l, E k l = E l k := by
    apply starProfileBlock_symmetric
    intro k l
    exact starProfilePair_symmetric h x hε k l
  have henergy :
      let w : Option (Fin h) → ℝ := fun k => match k with
        | none => -1 | some _ => 1 / ((h : ℝ) * (2 * Real.pi))
      (∑ k : Option (Fin h), ∑ l : Option (Fin h),
        w k * w l * E k l) ≤ 0 := by
    simpa only [E, starProfilePair] using!
      starProfileBlock_energy_nonpos hh x hε
  have h00 : E none none = comparisonEnergy :=
    starProfileBlock_none_none h x ε
  have hcross : ∀ i : Fin h, E (some i) none ≤
      (2 * Real.pi) *
        (comparisonPotential (x i) + 2 * (11 / 20 : ℝ) * ε) := by
    intro i
    convert! starProfileBlock_cross_le h x hε i using 1 <;> ring
  have hdiag : ∀ i : Fin h, E (some i) (some i) =
      (2 * Real.pi)^2 * Real.log ε :=
    starProfileBlock_circle_self h x hε
  have hoff : ∀ i j : Fin h, i ≠ j →
      (2 * Real.pi)^2 * Real.log ‖x j - x i‖ ≤
        E (some i) (some j) := by
    intro i j hij
    exact starProfileBlock_circle_lower h x hε i j
      (fun heq => hij (hinj heq))
  have hmain := complex_signed_energy_log_bound hh
    (2 * Real.pi) ε (11 / 20 : ℝ)
    (by positivity) hε (by norm_num)
    x (fun i => comparisonPotential (x i)) comparisonEnergy E
    hEsym henergy h00 hcross hdiag hoff
  convert! hmain using 1 <;> ring

end
end Li2Unified.Proofs.Contour

end


end
