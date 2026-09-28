module
public import Li2Unified.Modular.Base.LogNormIntegral
public import Li2Unified.Modular.Positive.Packed.P104
public import Li2Unified.Modular.Positive.Packed.P069
public import Li2Unified.Modular.Positive.Packed.P073

set_option backward.privateInPublic true

@[expose] public section

section
/-! Exact iterated logarithmic integrals for perpendicular line segments.
The positive vertical length b is fixed. The outer primitive is smooth at x=0.
No measure-energy identification or global potential bound is claimed here. -/
open MeasureTheory Set
namespace Li2Unified.ParameterFamily.Energy
noncomputable section

def perpendicularSlice (b x : ℝ) : ℝ :=
  b/2 * Real.log (x^2+b^2) - b + x*(Real.pi/2-Real.arctan (x/b))

def perpendicularPrimitive (b x : ℝ) : ℝ :=
  x*b/2 * Real.log (x^2+b^2) - 3*x*b/2 + Real.pi*x^2/4 +
    (b^2-x^2)/2 * Real.arctan (x/b)

lemma log_norm_coordinate_swap (x y : ℝ) :
    Real.log ‖(x:ℂ)+(y:ℂ)*Complex.I‖ =
      Real.log ‖(y:ℂ)+(x:ℂ)*Complex.I‖ := by
  simp only [Li2.log_norm_real_add_imag, add_comm]

lemma perpendicularSlice_eq_original {b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    perpendicularSlice b x = Li2.logNormIntegralPrimitive x b := by
  by_cases hx0 : x = 0
  · subst x
    simp [perpendicularSlice, Li2.logNormIntegralPrimitive]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have h := Real.arctan_inv_of_pos (div_pos hxpos hb)
    rw [inv_div] at h
    simp only [perpendicularSlice, Li2.logNormIntegralPrimitive, h]
    rw [add_comm (b^2) (x^2)]

lemma continuous_perpendicularSlice {b : ℝ} (hb : 0 < b) :
    Continuous (perpendicularSlice b) := by
  have hQ : ∀ x : ℝ, x^2+b^2 ≠ 0 := fun x =>
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg x) (pow_pos hb 2))
  have hlog : Continuous (fun x : ℝ => Real.log (x^2+b^2)) :=
    ((continuous_id.pow 2).add continuous_const).log hQ
  exact ((hlog.const_mul (b/2)).sub continuous_const).add
    (continuous_id.mul (continuous_const.sub
      (Real.continuous_arctan.comp (continuous_id.div_const b))))

lemma hasDerivAt_perpendicularPrimitive {b : ℝ} (hb : 0 < b) (x : ℝ) :
    HasDerivAt (perpendicularPrimitive b) (perpendicularSlice b x) x := by
  have hb0 : b ≠ 0 := hb.ne'
  have hQ : x^2+b^2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg x) (pow_pos hb 2))
  have hquot : 1+(x/b)^2 = (x^2+b^2)/b^2 := by
    field_simp [hb0]
    <;> ring
  have hlog : HasDerivAt (fun t : ℝ => Real.log (t^2+b^2))
      (2*x/(x^2+b^2)) x := by
    convert! (((hasDerivAt_id x).pow 2).add_const (b^2)).log hQ using 1
    <;> norm_num
    <;> ring
  have hatan : HasDerivAt (fun t : ℝ => Real.arctan (t/b))
      (b/(x^2+b^2)) x := by
    convert! ((hasDerivAt_id x).div_const b).arctan using 1
    dsimp only [id_eq]
    rw [hquot]
    field_simp [hb0, hQ]
    <;> ring
  have h :=
    (((((hasDerivAt_id x).mul_const b).div_const 2).mul hlog).sub
      ((((hasDerivAt_id x).const_mul 3).mul_const b).div_const 2)).add
      ((((hasDerivAt_id x).pow 2).const_mul Real.pi).div_const 4)
  have hh := h.add
    ((((hasDerivAt_const x (b^2)).sub ((hasDerivAt_id x).pow 2)).div_const 2).mul hatan)
  convert! hh using 1
  <;> dsimp [perpendicularPrimitive, perpendicularSlice]
  <;> field_simp [hQ]
  <;> ring

lemma integral_perpendicularSlice {b : ℝ} (hb : 0 < b) (a c : ℝ) :
    (∫ x in a..c, perpendicularSlice b x) =
      perpendicularPrimitive b c-perpendicularPrimitive b a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_perpendicularPrimitive hb x)
    ((continuous_perpendicularSlice hb).intervalIntegrable a c)

lemma integral_log_norm_perpendicular {b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    (∫ y in (0:ℝ)..b, Real.log ‖(x:ℂ)+(y:ℂ)*Complex.I‖) =
      perpendicularSlice b x := by
  simp_rw [log_norm_coordinate_swap x]
  rw [Li2.integral_log_norm_real_add_imag hx hb.le]
  exact (perpendicularSlice_eq_original hb hx).symm

lemma integral_integral_log_norm_perpendicular {b a c : ℝ}
    (hb : 0 < b) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (∫ x in a..c, ∫ y in (0:ℝ)..b, Real.log ‖(x:ℂ)+(y:ℂ)*Complex.I‖) =
      perpendicularPrimitive b c-perpendicularPrimitive b a := by
  calc
    _ = ∫ x in a..c, perpendicularSlice b x := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact integral_log_norm_perpendicular hb ((le_min ha hc).trans hx.1)
    _ = _ := integral_perpendicularSlice hb a c

lemma integral_integral_log_norm_perpendicular_from_zero {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) :
    (∫ x in (0:ℝ)..a, ∫ y in (0:ℝ)..b, Real.log ‖(x:ℂ)+(y:ℂ)*Complex.I‖) =
      perpendicularPrimitive b a := by
  simpa [perpendicularPrimitive] using!
    integral_integral_log_norm_perpendicular hb (le_refl 0) ha

end
end Li2Unified.ParameterFamily.Energy

end

section
/-! Exact line-log symmetries and a symmetric perpendicular segment.
All pointwise identities respect total Real.log0. -/
open MeasureTheory Set
namespace Li2Unified.ParameterFamily.Energy
noncomputable section

lemma logPrimitive_neg (x : ℝ) : logPrimitive (-x) = -logPrimitive x := by
  simp only [logPrimitive, Real.log_neg_eq_log]
  ring

lemma logSecondPrimitive_neg (x : ℝ) :
    logSecondPrimitive (-x) = logSecondPrimitive x := by
  simp only [logSecondPrimitive, Real.log_neg_eq_log]
  ring

lemma log_norm_real_sub_real (x y : ℝ) :
    Real.log ‖(x:ℂ)-(y:ℂ)‖ = Real.log (x-y) := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]

lemma log_norm_imag_sub_imag (x y : ℝ) :
    Real.log ‖(x:ℂ)*Complex.I-(y:ℂ)*Complex.I‖ = Real.log (x-y) := by
  rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, Real.log_abs]

lemma log_norm_real_sub_imag (x y : ℝ) :
    Real.log ‖(x:ℂ)-(y:ℂ)*Complex.I‖ =
      Real.log ‖(x:ℂ)+(y:ℂ)*Complex.I‖ := by
  have h : (x:ℂ)-(y:ℂ)*Complex.I = (x:ℂ)+((-y:ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  rw [h, Li2.log_norm_real_add_imag, Li2.log_norm_real_add_imag, neg_sq]

lemma log_norm_imag_sub_real (x y : ℝ) :
    Real.log ‖(y:ℂ)*Complex.I-(x:ℂ)‖ =
      Real.log ‖(x:ℂ)+(y:ℂ)*Complex.I‖ := by
  rw [norm_sub_rev]
  exact log_norm_real_sub_imag x y

lemma integral_log_norm_symmetric_perpendicular {x b : ℝ}
    (hx : 0 ≤ x) (hb : 0 < b) :
    (∫ y in -b..b, Real.log ‖(x:ℂ)+(y:ℂ)*Complex.I‖) =
      2*perpendicularSlice b x := by
  let f : ℝ → ℝ := fun y => Real.log ‖(x:ℂ)+(y:ℂ)*Complex.I‖
  have hf : ∀ a c : ℝ, IntervalIntegrable f volume a c := by
    intro a c
    have heq : f = fun y : ℝ => Real.log ‖(y:ℂ)+(x:ℂ)*Complex.I‖ := by
      funext y
      exact log_norm_coordinate_swap x y
    rw [heq]
    exact Li2.intervalIntegrable_log_norm_real_add_imag hx a c
  have heven : ∀ y : ℝ, f (-y) = f y := by
    intro y
    simp only [f, Li2.log_norm_real_add_imag, neg_sq]
  have hneg : (∫ y in -b..(0:ℝ), f y) = ∫ y in (0:ℝ)..b, f y := by
    have h := intervalIntegral.integral_comp_neg (f := f) (a := (0:ℝ)) (b := b)
    simpa only [heven, neg_zero] using! h.symm
  change (∫ y in -b..b, f y) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf (-b) 0) (hf 0 b), hneg]
  have hpos : (∫ y in (0:ℝ)..b, f y) = perpendicularSlice b x :=
    integral_log_norm_perpendicular hb hx
  rw [hpos]
  ring

lemma perpendicularPrimitive_symmetricForm {x b : ℝ} (hx : 0 ≤ x) (hb : 0 < b) :
    perpendicularPrimitive b x =
      (x*b*Real.log (x^2+b^2)-3*x*b +
        x^2*Real.arctan (b/x)+b^2*Real.arctan (x/b))/2 := by
  by_cases hx0 : x = 0
  · subst x
    simp [perpendicularPrimitive]
  · have h := Real.arctan_inv_of_pos (div_pos (lt_of_le_of_ne hx (Ne.symm hx0)) hb)
    rw [inv_div] at h
    rw [h]
    unfold perpendicularPrimitive
    ring

end
end Li2Unified.ParameterFamily.Energy

end

section
/-! Actual one-layer potential integrals on the real and imaginary axes. -/
open MeasureTheory Set
namespace Li2Unified.Proofs.Potential
noncomputable section
open Li2Unified.ParameterFamily.Energy

lemma horizontal_ray_integral (r x : ℝ) :
    (∫ t in (0:ℝ)..r, Real.log ‖(t:ℂ)-(x:ℂ)‖) =
      logPrimitive (r-x)-logPrimitive (-x) := by
  simp_rw [log_norm_real_sub_real]
  simpa only [zero_sub] using! integral_log_shift 0 r x

lemma horizontal_vertical_integral {r y : ℝ} (hr : 0 < r) (hy : 0 ≤ y) :
    (∫ t in (0:ℝ)..r, Real.log ‖(t:ℂ)-(y:ℂ)*Complex.I‖) =
      perpendicularSlice r y := by
  convert! integral_log_norm_perpendicular hr hy using 1
  apply intervalIntegral.integral_congr
  intro t _
  change Real.log ‖(t:ℂ)-(y:ℂ)*Complex.I‖ =
    Real.log ‖(y:ℂ)+(t:ℂ)*Complex.I‖
  rw [log_norm_real_sub_imag t y, ← log_norm_coordinate_swap y t]

lemma vertical_ray_integral {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    (∫ t in -r..r, Real.log ‖(t:ℂ)*Complex.I-(x:ℂ)‖) =
      2*perpendicularSlice r x := by
  simp_rw [log_norm_imag_sub_real]
  exact integral_log_norm_symmetric_perpendicular hx hr

lemma vertical_vertical_integral (r y : ℝ) :
    (∫ t in -r..r, Real.log ‖(t:ℂ)*Complex.I-(y:ℂ)*Complex.I‖) =
      logPrimitive (r-y)-logPrimitive (-r-y) := by
  simp_rw [log_norm_imag_sub_imag]
  exact integral_log_shift (-r) r y

end
end Li2Unified.Proofs.Potential

end

section
open MeasureTheory Set
namespace Li2Unified.Proofs.Potential
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

lemma horizontal_reflection_norm (t y : ℝ) :
    ‖(t:ℂ)-(-(y:ℂ))*Complex.I‖ = ‖(t:ℂ)-(y:ℂ)*Complex.I‖ := by
  have h := Complex.norm_conj ((t:ℂ)-(y:ℂ)*Complex.I)
  simpa only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_mul]
    using! h

lemma layer_potential_reflection (s : StarLayer) (y : ℝ) :
    (∫ x in s.left..s.right, Real.log ‖(x:ℂ)*s.direction-(-(y:ℂ))*Complex.I‖) =
    (∫ x in s.left..s.right, Real.log ‖(x:ℂ)*s.direction-(y:ℂ)*Complex.I‖) := by
  cases hv : s.vertical
  · simp only [StarLayer.left, StarLayer.right, StarLayer.direction, hv,
      Bool.false_eq_true, ↓reduceIte, mul_one]
    simp_rw [horizontal_reflection_norm]
  · simp only [StarLayer.left, StarLayer.right, StarLayer.direction, hv, ↓reduceIte]
    have h := vertical_vertical_integral (s.radius:ℝ) (-y)
    simp only [Complex.ofReal_neg] at h
    rw [h, vertical_vertical_integral]
    rw [show (s.radius:ℝ)-(-y) = -(-(s.radius:ℝ)-y) by ring,
      show -(s.radius:ℝ)-(-y) = -((s.radius:ℝ)-y) by ring]
    rw [logPrimitive_neg, logPrimitive_neg]
    ring

theorem comparisonPotential_reflection (y : ℝ) :
    comparisonPotential (-(y:ℂ)*Complex.I) =
      comparisonPotential ((y:ℂ)*Complex.I) := by
  rw [comparisonPotential_eq, comparisonPotential_eq]
  congr 1
  apply List.map_congr_left
  intro s _
  rw [layer_potential_reflection]

theorem psi_reflection (y : ℝ) :
    Li2Unified.Stage0.HalfAnalytic.psiDown y =
      Li2Unified.Stage0.HalfAnalytic.psiUp y := by
  unfold Li2Unified.Stage0.HalfAnalytic.psiDown Li2Unified.Stage0.HalfAnalytic.psiUp
  rw [comparisonPotential_reflection]

end
end Li2Unified.Proofs.Potential
#print axioms Li2Unified.Proofs.Potential.psi_reflection

end

section
/-! Exact external-field axis integrals in the actual potential definitions. -/
open MeasureTheory Set
namespace Li2Unified.Proofs.Potential
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Stage0.HalfAnalytic

theorem baseRay_eq_primitives (x : ℝ) :
    baseRay x = 4*Real.log 4-1 +
      3*(logPrimitive (1+x)-logPrimitive x) -
      (logPrimitive (4+x)-logPrimitive x) := by
  have h1 : (∫ t in (0:ℝ)..1, Real.log (t+x)) =
      logPrimitive (1+x)-logPrimitive x := by
    simpa only [sub_neg_eq_add, zero_add] using! integral_log_shift 0 1 (-x)
  have h4 : (∫ t in (0:ℝ)..4, Real.log (t+x)) =
      logPrimitive (4+x)-logPrimitive x := by
    simpa only [sub_neg_eq_add, zero_add] using! integral_log_shift 0 4 (-x)
  simp only [baseRay, h1, h4]

theorem baseVertical_eq_primitives (y : ℝ) (hy : 0 ≤ y) :
    baseVertical y = 4*Real.log 4-1 +
      3*perpendicularSlice 1 y-perpendicularSlice 4 y := by
  have h1 : (∫ t in (0:ℝ)..1,
      Real.log ‖(t:ℂ)+(y:ℂ)*Complex.I‖) = perpendicularSlice 1 y := by
    simpa only [log_norm_coordinate_swap y] using!
      (integral_log_norm_perpendicular (b:=1) (x:=y) (by norm_num) hy)
  have h4 : (∫ t in (0:ℝ)..4,
      Real.log ‖(t:ℂ)+(y:ℂ)*Complex.I‖) = perpendicularSlice 4 y := by
    simpa only [log_norm_coordinate_swap y] using!
      (integral_log_norm_perpendicular (b:=4) (x:=y) (by norm_num) hy)
  simp only [baseVertical, h1, h4]

end
end Li2Unified.Proofs.Potential

end


end
