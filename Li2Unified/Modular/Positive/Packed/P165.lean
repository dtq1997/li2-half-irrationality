module
public import Li2Unified.Modular.Positive.Packed.P109

set_option backward.privateInPublic true

@[expose] public section

section
/-! The fixed comparison measure's actual potential on both axes, before
expanding the 36 rational layers. -/
open MeasureTheory Set
namespace Li2Unified.Proofs.Potential
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

def rayLayerValue (s : StarLayer) (x : ℝ) : ℝ :=
  (s.density : ℝ) *
    (if s.vertical then 2*perpendicularSlice (s.radius : ℝ) x
    else logPrimitive ((s.radius : ℝ)-x)-logPrimitive (-x))

def verticalLayerValue (s : StarLayer) (y : ℝ) : ℝ :=
  (s.density : ℝ) *
    (if s.vertical then
      logPrimitive ((s.radius : ℝ)-y)-logPrimitive (-(s.radius : ℝ)-y)
    else perpendicularSlice (s.radius : ℝ) y)

def rayPotentialValue (x : ℝ) : ℝ :=
  (layerData.map (fun s => rayLayerValue s x)).sum

def verticalPotentialValue (y : ℝ) : ℝ :=
  (layerData.map (fun s => verticalLayerValue s y)).sum

theorem comparisonPotential_real_eq (x : ℝ) (hx : 0 ≤ x) :
    comparisonPotential (x:ℂ) = rayPotentialValue x := by
  rw [comparisonPotential_eq]
  unfold rayPotentialValue
  congr 1
  apply List.map_congr_left
  intro s hs
  have hr : 0 < (s.radius : ℝ) := by
    exact_mod_cast (layerData_radii s hs).1
  cases hv : s.vertical
  · simp only [rayLayerValue, hv, Bool.false_eq_true, ↓reduceIte,
      StarLayer.left, StarLayer.right, StarLayer.direction, mul_one]
    rw [horizontal_ray_integral]
  · simp only [rayLayerValue, hv, ↓reduceIte,
      StarLayer.left, StarLayer.right, StarLayer.direction]
    rw [vertical_ray_integral hr hx]

theorem comparisonPotential_imag_eq (y : ℝ) (hy : 0 ≤ y) :
    comparisonPotential ((y:ℂ)*Complex.I) = verticalPotentialValue y := by
  rw [comparisonPotential_eq]
  unfold verticalPotentialValue
  congr 1
  apply List.map_congr_left
  intro s hs
  have hr : 0 < (s.radius : ℝ) := by
    exact_mod_cast (layerData_radii s hs).1
  cases hv : s.vertical
  · simp only [verticalLayerValue, hv, Bool.false_eq_true, ↓reduceIte,
      StarLayer.left, StarLayer.right, StarLayer.direction, mul_one]
    rw [horizontal_vertical_integral hr hy]
  · simp only [verticalLayerValue, hv, ↓reduceIte,
      StarLayer.left, StarLayer.right, StarLayer.direction]
    rw [vertical_vertical_integral]

end
end Li2Unified.Proofs.Potential

end


end
