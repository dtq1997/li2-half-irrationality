module
public import Li2Unified.Modular.Positive.Packed.P190
public import Li2Unified.Modular.Positive.Packed.P191

set_option backward.privateInPublic true

@[expose] public section

section
/-! The circle average of the actual comparison potential has an explicit
uniform error for every complex center and every positive radius. -/

open MeasureTheory
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Instances.PosHalf.LayerComparison

theorem actual_circle_comparisonPotential_le (c : ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi,
      comparisonPotential (circleMap c ε θ)) ≤
      comparisonPotential c + 11 / 10 * ε := by
  rw [actual_circle_comparisonPotential_eq_truncation c hε]
  have hT : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ hT, one_mul]
  exact actual_comparisonPotential_truncation_le c hε

end
end Li2Unified.Proofs.Contour

end


end
