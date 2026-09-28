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

def rayDerivative (x : ℝ) : ℝ :=
  3*Real.log (1+x)-Real.log (4+x)+(4*rayDensitySum-2)*Real.log x-Real.log 2 -
    (rayLayers.map (fun q => 4*(q.2:ℝ)*Real.log |(q.1:ℝ)-x|)).sum +
    (verticalLayers.map (fun q => 8*(q.2:ℝ)*(Real.pi/2-Real.arctan (x/(q.1:ℝ))))).sum

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
  simpa only [Real.log_abs] using Real.hasDerivAt_mul_log hx

private lemma hasDerivAt_H_shift (r x : ℝ) (h : r - x ≠ 0) :
    HasDerivAt (fun t : ℝ => H (r-t)) (-(Real.log |r-x| + 1)) x := by
  convert (hasDerivAt_H h).comp x
    ((hasDerivAt_const x r).sub (hasDerivAt_id x)) using 1
  ring

private lemma hasDerivAt_rayVerticalAtom (r x : ℝ) (hr : 0 < r) :
    HasDerivAt
      (fun t : ℝ => r * Real.log (t^2+r^2)/2 +
        t*(Real.pi/2-Real.arctan (t/r)))
      (Real.pi/2-Real.arctan (x/r)) x := by
  have hr0 : r ≠ 0 := hr.ne'
  have hQ : x^2+r^2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos hr))
  have hlog : HasDerivAt (fun t : ℝ => Real.log (t^2+r^2))
      (2*x/(x^2+r^2)) x := by
    convert (((hasDerivAt_id x).pow 2).add_const (r^2)).log hQ using 1
    <;> norm_num
    <;> ring
  have hquot : 1+(x/r)^2 = (x^2+r^2)/r^2 := by
    field_simp [hr0]
    ring
  have hatan : HasDerivAt (fun t : ℝ => Real.arctan (t/r))
      (r/(x^2+r^2)) x := by
    convert ((hasDerivAt_id x).div_const r).arctan using 1
    dsimp only [id_eq]
    rw [hquot]
    field_simp [hr0,hQ]
    <;> ring
  have h := (((hlog.const_mul r).div_const 2).add
    ((hasDerivAt_id x).mul ((hasDerivAt_const x (Real.pi/2)).sub hatan)))
  convert h using 1
  dsimp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq]
  field_simp [hr0,hQ]
  <;> ring

private lemma hasDerivAt_rayHorizontalLayer (q : ℚ × ℚ) (x : ℝ)
    (h : x ≠ (q.1:ℝ)) :
    HasDerivAt
      (fun t : ℝ => 4*(q.2:ℝ)*H ((q.1:ℝ)-t))
      (-4*(q.2:ℝ)*(Real.log |(q.1:ℝ)-x|+1)) x := by
  have h' : (q.1:ℝ)-x ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  convert (hasDerivAt_H_shift (q.1:ℝ) x h').const_mul (4*(q.2:ℝ)) using 1
  ring

private lemma hasDerivAt_rayVerticalLayer (q : ℚ × ℚ) (x : ℝ)
    (hq : 0 < q.1) :
    HasDerivAt
      (fun t : ℝ => 8*(q.2:ℝ)*
        ((q.1:ℝ)*Real.log ((q.1:ℝ)^2+t*t)/2 +
          t*(Real.pi/2-Real.arctan (t/(q.1:ℝ)))))
      (8*(q.2:ℝ)*(Real.pi/2-Real.arctan (x/(q.1:ℝ)))) x := by
  have hq' : (0:ℝ) < q.1 := by exact_mod_cast hq
  convert (hasDerivAt_rayVerticalAtom (q.1:ℝ) x hq').const_mul (8*(q.2:ℝ)) using 1
  · funext t
    simp only [pow_two]
    ring_nf

private lemma hasDerivAt_list_sum {α : Type} (L : List α)
    (f : α → ℝ → ℝ) (df : α → ℝ) (x : ℝ)
    (h : ∀ q ∈ L, HasDerivAt (f q) (df q) x) :
    HasDerivAt (fun t => (L.map (fun q => f q t)).sum) ((L.map df).sum) x := by
  induction L with
  | nil => simpa using (hasDerivAt_const x (0:ℝ))
  | cons q qs ih =>
    have hq := h q (by simp)
    have hs := ih (fun a ha => h a (by simp [ha]))
    simpa only [List.map_cons, List.sum_cons] using hq.add hs

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem hasDerivAt_rayExpr_proof (x : ℝ) (hx : 0 < x)
    (havoid : ∀ q ∈ rayLayers, x ≠ (q.1:ℝ)) :
    HasDerivAt rayExpr (rayDerivative x) x := by
  have h1 : HasDerivAt (fun t : ℝ => H (1+t))
      (Real.log (1+x)+1) x := by
    have hpos : (0:ℝ) < 1+x := by linarith
    convert (hasDerivAt_H hpos.ne').comp x
      ((hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x)) using 1
    simp [abs_of_pos hpos]
  have h4 : HasDerivAt (fun t : ℝ => H (4+t))
      (Real.log (4+x)+1) x := by
    have hpos : (0:ℝ) < 4+x := by linarith
    convert (hasDerivAt_H hpos.ne').comp x
      ((hasDerivAt_const x (4:ℝ)).add (hasDerivAt_id x)) using 1
    simp [abs_of_pos hpos]
  have hxH : HasDerivAt H (Real.log x+1) x := by
    simpa [abs_of_pos hx] using hasDerivAt_H hx.ne'
  have hbase : HasDerivAt
      (fun t : ℝ => 8*Real.log 2-4+3*H (1+t)-H (4+t)+
        (4*rayDensitySum-2)*H t-t*Real.log 2)
      (3*(Real.log (1+x)+1)-(Real.log (4+x)+1)+
        (4*rayDensitySum-2)*(Real.log x+1)-Real.log 2) x := by
    convert ((((((hasDerivAt_const x (8*Real.log 2-4)).add
      (h1.const_mul 3)).sub h4).add
      (hxH.const_mul (4*rayDensitySum-2))).sub
      ((hasDerivAt_id x).mul_const (Real.log 2)))) using 1
    <;> ring
  have hhor : HasDerivAt
      (fun t : ℝ => (rayLayers.map (fun q => 4*(q.2:ℝ)*H ((q.1:ℝ)-t))).sum)
      (rayLayers.map (fun q => -4*(q.2:ℝ)*(Real.log |(q.1:ℝ)-x|+1))).sum x := by
    apply hasDerivAt_list_sum
    intro q hq
    exact hasDerivAt_rayHorizontalLayer q x (havoid q hq)
  have hvert : HasDerivAt
      (fun t : ℝ => (verticalLayers.map (fun q => 8*(q.2:ℝ)*
        ((q.1:ℝ)*Real.log ((q.1:ℝ)^2+t*t)/2 +
          t*(Real.pi/2-Real.arctan (t/(q.1:ℝ)))))).sum)
      (verticalLayers.map (fun q => 8*(q.2:ℝ)*
        (Real.pi/2-Real.arctan (x/(q.1:ℝ))))).sum x := by
    apply hasDerivAt_list_sum
    intro q hq
    have hqpos : 0 < q.1 := by
      simp only [verticalLayers, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with hq | hq <;> subst q <;> norm_num
    exact hasDerivAt_rayVerticalLayer q x hqpos
  have h := (hbase.add hhor).add hvert
  convert h using 1
  simp only [rayDerivative]
  simp only [rayDensitySum, rayLayers, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

end RayDerivativeBridge

theorem hasDerivAt_rayExpr (x : ℝ) (hx : 0 < x)
    (havoid : ∀ q ∈ rayLayers, x ≠ (q.1:ℝ)) :
    HasDerivAt rayExpr (rayDerivative x) x := by
  exact RayDerivativeBridge.hasDerivAt_rayExpr_proof x hx havoid

end
end Li2Unified.Stage0.HalfPotentialExpressions

end


end
