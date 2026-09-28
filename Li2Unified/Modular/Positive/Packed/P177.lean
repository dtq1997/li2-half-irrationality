module
public import Li2Unified.Modular.Positive.Packed.P164
public import Li2Unified.Modular.Positive.Packed.P166

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Potential.CompactAffine

open Li2Unified.Stage0.HalfPotentialExpressions
open Li2Unified.Stage0.HalfAnalytic

noncomputable section

def rayCompactExpr (x : ℝ) : ℝ :=
  8 * Real.log 2 - 4 + 3 * H (1 + x) - H (4 + x) +
    (4 * rayDensitySum - 2) * H x - x * Real.log 2 +
    (rayLayers.map (fun q => 4 * (q.2 : ℝ) * H ((q.1 : ℝ) - x))).sum +
    (verticalLayers.map (fun q =>
      8 * (q.2 : ℝ) * (F (q.1 : ℝ) x + Real.pi * x / 2))).sum

def verticalCompactExpr (y : ℝ) : ℝ :=
  8 * Real.log 2 - 4 + 3 * F 1 y - F 4 y +
    (4 * rayDensitySum - 2) * Real.pi * y / 2 +
    (rayLayers.map (fun q => 4 * (q.2 : ℝ) * F (q.1 : ℝ) y)).sum +
    (verticalLayers.map (fun q =>
      4 * (q.2 : ℝ) * (H ((q.1 : ℝ) - y) + H ((q.1 : ℝ) + y)))).sum

private theorem ray_vertical_sum (L : List (ℚ × ℚ)) (x : ℝ) :
    (L.map (fun q => 8 * (q.2 : ℝ) * (F (q.1 : ℝ) x + Real.pi * x / 2))).sum =
      (L.map (fun q => 8 * (q.2 : ℝ) *
        ((q.1 : ℝ) * Real.log ((q.1 : ℝ) ^ 2 + x * x) / 2 +
          x * (Real.pi / 2 - Real.arctan (x / (q.1 : ℝ)))))).sum := by
  induction L with
  | nil => simp
  | cons q qs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      unfold F
      ring

private theorem vertical_ray_sum (L : List (ℚ × ℚ)) (y : ℝ) :
    (L.map (fun q => 4 * (q.2 : ℝ) * F (q.1 : ℝ) y)).sum =
      (L.map (fun q => 2 * (q.2 : ℝ) * (q.1 : ℝ) *
        Real.log ((q.1 : ℝ) ^ 2 + y * y))).sum -
      y * (L.map (fun q => 4 * (q.2 : ℝ) *
        Real.arctan (y / (q.1 : ℝ)))).sum := by
  induction L with
  | nil => simp
  | cons q qs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      unfold F
      ring

theorem rayCompactExpr_eq_rayExpr (x : ℝ) :
    rayCompactExpr x = rayExpr x := by
  unfold rayCompactExpr rayExpr
  rw [ray_vertical_sum verticalLayers x]

theorem verticalCompactExpr_eq_verticalExpr (y : ℝ) :
    verticalCompactExpr y = verticalExpr y := by
  unfold verticalCompactExpr verticalExpr
  rw [vertical_ray_sum rayLayers y]
  simp only [F, one_pow, div_one]
  ring_nf

theorem rayCompactExpr_actual (x : ℝ) (hx : 0 ≤ x) :
    rayCompactExpr x = psiRay x :=
  (rayCompactExpr_eq_rayExpr x).trans (rayExpr_actual x hx)

theorem verticalCompactExpr_actual (y : ℝ) (hy : 0 ≤ y) :
    verticalCompactExpr y = psiUp y :=
  (verticalCompactExpr_eq_verticalExpr y).trans (verticalExpr_actual y hy)

end
end Li2Unified.Proofs.Potential.CompactAffine

#print axioms Li2Unified.Proofs.Potential.CompactAffine.rayCompactExpr_actual
#print axioms Li2Unified.Proofs.Potential.CompactAffine.verticalCompactExpr_actual

end


end
