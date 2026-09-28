module
public import Li2Unified.Modular.Positive.Packed.P073
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Li2Unified.Modular.Positive.Packed.P165
public import Li2Unified.Modular.Positive.Packed.P109

set_option backward.privateInPublic true

@[expose] public section

section
open Li2Unified.Stage0.HalfAnalytic
namespace Li2Unified.Stage0.HalfPotentialExpressions
noncomputable section
open Li2Unified.Proofs.Potential
open Li2Unified.Instances.PosHalf.LayerComparison
open Li2Unified.ParameterFamily.Energy

def rayLayers : List (ℚ × ℚ) := [
  ((7/100:ℚ), (5486000/100000027:ℚ)),
  ((7/50:ℚ), (3870700/100000027:ℚ)),
  ((21/100:ℚ), (2913000/100000027:ℚ)),
  ((7/25:ℚ), (2327000/100000027:ℚ)),
  ((7/20:ℚ), (1932800/100000027:ℚ)),
  ((21/50:ℚ), (1648500/100000027:ℚ)),
  ((49/100:ℚ), (1433000/100000027:ℚ)),
  ((14/25:ℚ), (1263800/100000027:ℚ)),
  ((63/100:ℚ), (1127200/100000027:ℚ)),
  ((7/10:ℚ), (1014700/100000027:ℚ)),
  ((77/100:ℚ), (920500/100000027:ℚ)),
  ((21/25:ℚ), (840300/100000027:ℚ)),
  ((91/100:ℚ), (771500/100000027:ℚ)),
  ((49/50:ℚ), (711800/100000027:ℚ)),
  ((21/20:ℚ), (659400/100000027:ℚ)),
  ((28/25:ℚ), (613300/100000027:ℚ)),
  ((119/100:ℚ), (572300/100000027:ℚ)),
  ((63/50:ℚ), (535800/100000027:ℚ)),
  ((133/100:ℚ), (503000/100000027:ℚ)),
  ((7/5:ℚ), (2230420/100000027:ℚ)),
  ((21/10:ℚ), (2947820/100000027:ℚ)),
  ((14/5:ℚ), (2013740/100000027:ℚ)),
  ((7/2:ℚ), (1498080/100000027:ℚ)),
  ((21/5:ℚ), (1181890/100000027:ℚ)),
  ((49/10:ℚ), (974840/100000027:ℚ)),
  ((28/5:ℚ), (833640/100000027:ℚ)),
  ((63/10:ℚ), (735770/100000027:ℚ)),
  ((7/1:ℚ), (668860/100000027:ℚ)),
  ((77/10:ℚ), (626710/100000027:ℚ)),
  ((42/5:ℚ), (607930/100000027:ℚ)),
  ((91/10:ℚ), (617440/100000027:ℚ)),
  ((49/5:ℚ), (677410/100000027:ℚ)),
  ((21/2:ℚ), (958380/100000027:ℚ)),
  ((56/5:ℚ), (929970/100000027:ℚ))
]

def verticalLayers : List (ℚ × ℚ) := [
  ((1/25:ℚ), (3687200/100000027:ℚ)),
  ((2/25:ℚ), (3178600/100000027:ℚ))
]

def H (x : ℝ) : ℝ := x * Real.log |x|
def rayDensitySum : ℝ := (rayLayers.map (fun q => (q.2:ℝ))).sum

def rayExpr (x : ℝ) : ℝ :=
  8*Real.log 2-4+3*H (1+x)-H (4+x)+(4*rayDensitySum-2)*H x-x*Real.log 2 +
    (rayLayers.map (fun q => 4*(q.2:ℝ)*H ((q.1:ℝ)-x))).sum +
    (verticalLayers.map (fun q => 8*(q.2:ℝ)*
      ((q.1:ℝ)*Real.log ((q.1:ℝ)^2+x*x)/2 + x*(Real.pi/2-Real.arctan (x/(q.1:ℝ)))))).sum

def verticalExpr (y : ℝ) : ℝ :=
  8*Real.log 2-4+(3/2:ℝ)*Real.log (1+y*y)-2*Real.log (16+y*y) +
    (rayLayers.map (fun q => 2*(q.2:ℝ)*(q.1:ℝ)*Real.log ((q.1:ℝ)^2+y*y))).sum +
    y*((2*rayDensitySum-1)*Real.pi-3*Real.arctan y+Real.arctan (y/4) -
      (rayLayers.map (fun q => 4*(q.2:ℝ)*Real.arctan (y/(q.1:ℝ)))).sum) +
    (verticalLayers.map (fun q => 4*(q.2:ℝ)*(H ((q.1:ℝ)-y)+H ((q.1:ℝ)+y)))).sum

private lemma log_four : Real.log (4:ℝ) = 2*Real.log 2 := by
  rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
  ring

private lemma vertical_primitive_to_H (r y : ℝ) :
    logPrimitive (r-y)-logPrimitive (-r-y) =
      H (r-y)+H (r+y)-2*r := by
  rw [show -r-y = -(r+y) by ring, logPrimitive_neg]
  simp only [logPrimitive, H, Real.log_abs]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem rayExpr_actual (x : ℝ) (hx : 0 ≤ x) : rayExpr x = psiRay x := by
  rw [psiRay, Vray, baseRay_eq_primitives,
    comparisonPotential_real_eq x hx]
  unfold rayExpr rayPotentialValue rayLayerValue rayDensitySum H
  simp only [logPrimitive, Real.log_abs, perpendicularSlice, log_four]
  norm_num [layerData, rayLayers, verticalLayers, StarLayer.left]
  ring_nf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem verticalExpr_actual (y : ℝ) (hy : 0 ≤ y) : verticalExpr y = psiUp y := by
  rw [psiUp, Vvertical, baseVertical_eq_primitives y hy,
    comparisonPotential_imag_eq y hy]
  unfold verticalExpr verticalPotentialValue verticalLayerValue rayDensitySum
  simp_rw [vertical_primitive_to_H]
  rw [abs_of_nonneg hy]
  simp only [H, Real.log_abs, perpendicularSlice, log_four]
  norm_num [layerData, rayLayers, verticalLayers, StarLayer.left]
  ring_nf

namespace RayDerivativeBridge
private lemma hasDerivAt_H {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt H (Real.log |x| + 1) x := by
  have hf : H = fun y => y * Real.log y := by
    funext y
    simp only [H, Real.log_abs]
  rw [hf]
  simpa only [Real.log_abs] using! Real.hasDerivAt_mul_log hx

end RayDerivativeBridge

end
end Li2Unified.Stage0.HalfPotentialExpressions

end

end
