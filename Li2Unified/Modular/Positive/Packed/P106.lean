module
public import Li2Unified.Modular.Positive.Packed.P073
public import Li2Unified.Modular.Base.LogNormMonotone
public import Li2Unified.Modular.Positive.Packed.P069
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic

set_option backward.privateInPublic true

@[expose] public section

section
open MeasureTheory Set
namespace Li2Unified.Proofs.Potential
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

lemma three_integrals_sub_four_le (f : ℝ → ℝ)
    (hm : MonotoneOn f (Icc 0 4)) :
    3*(∫ t in (0:ℝ)..1, f t) - (∫ t in (0:ℝ)..4, f t) ≤ -f 0 := by
  have h1m : MonotoneOn f (uIcc 0 1) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hm.mono (by intro x hx; exact ⟨hx.1, by linarith [hx.2]⟩)
  have h4m : MonotoneOn f (uIcc 0 4) := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 4)] using! hm
  have h1 : IntervalIntegrable f volume 0 1 := h1m.intervalIntegrable
  have h4 : IntervalIntegrable f volume 0 4 := h4m.intervalIntegrable
  have hs : IntervalIntegrable (fun t => f (4*t)) volume 0 1 := by
    simpa using! h4.comp_mul_left (c := (4:ℝ))
  have hlo : f 0 ≤ ∫ t in (0:ℝ)..1, f t := by
    have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f 0) volume 0 1)
      h1 (fun t ht => hm ⟨le_rfl, by norm_num⟩ ⟨ht.1, by linarith [ht.2]⟩ ht.1)
    simpa using! h
  have hcmp := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) h1 hs
    (fun t ht => hm ⟨ht.1, by linarith [ht.2]⟩
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ (by linarith [ht.1]))
  have he := intervalIntegral.smul_integral_comp_mul_left f (4:ℝ) (a := 0) (b := 1)
  norm_num only [smul_eq_mul, mul_zero, mul_one] at he
  linarith

theorem baseRay_tail_upper (x : ℝ) (hx : 0 < x) :
    baseRay x ≤ 4*Real.log 4-1-Real.log x := by
  have hm : MonotoneOn (fun t : ℝ => Real.log (t+x)) (Icc 0 4) := by
    intro s hs t ht hst
    exact Real.log_le_log (by linarith [hs.1]) (by linarith)
  have h := three_integrals_sub_four_le _ hm
  simp only [zero_add] at h
  unfold baseRay
  linarith

theorem baseVertical_tail_upper (y : ℝ) (hy : 0 < y) :
    baseVertical y ≤ 4*Real.log 4-1-Real.log y := by
  have hm : MonotoneOn (fun t : ℝ => Real.log ‖(t:ℂ)+(y:ℂ)*Complex.I‖)
      (Icc 0 4) := by
    intro s hs t ht hst
    simp only [Li2.log_norm_real_add_imag]
    have hp : 0 < s^2+y^2 := by nlinarith [sq_nonneg s]
    have hs2 : s^2 ≤ t^2 := by nlinarith [hs.1, ht.1]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hp (by linarith)) (by norm_num)
  have h := three_integrals_sub_four_le _ hm
  simp only [Complex.ofReal_zero, zero_add, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy] at h
  unfold baseVertical
  linarith

end
end Li2Unified.Proofs.Potential
#print axioms Li2Unified.Proofs.Potential.baseRay_tail_upper
#print axioms Li2Unified.Proofs.Potential.baseVertical_tail_upper

end

section
open MeasureTheory Set
namespace Li2Unified.Proofs.Potential
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

lemma layer_ae_distance_ray (s : StarLayer) (x e : ℝ) (hx : 0 ≤ x) (he : 0 ≤ e)
    (hr : (s.radius:ℝ) ≤ x) (hvsmall : s.vertical = true → (s.radius:ℝ) ≤ e) :
    ∀ᵐ z ∂s.measure, ‖z-(x:ℂ)‖ ≤ x+e := by
  have hm : Measurable (fun t : ℝ => (t:ℂ)*s.direction) := by fun_prop
  have hset : MeasurableSet {z : ℂ | ‖z-(x:ℂ)‖ ≤ x+e} :=
    (isClosed_le (continuous_id.sub continuous_const).norm continuous_const).measurableSet
  have ht : ∀ᵐ t : ℝ ∂(volume : Measure ℝ).restrict (Ioc s.left s.right),
      ‖(t:ℂ)*s.direction-(x:ℂ)‖ ≤ x+e := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    cases hv : s.vertical
    · have ht0 : 0 ≤ t := by simpa [StarLayer.left,hv] using! ht.1.le
      have htx : t ≤ x := ht.2.trans hr
      simp only [StarLayer.direction, hv, Bool.false_eq_true, ↓reduceIte, mul_one,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr htx)]
      linarith
    · have hte : |t| ≤ e := by
        apply abs_le.mpr
        have hlo : -(s.radius:ℝ) ≤ t := by simpa [StarLayer.left,hv] using! ht.1.le
        have hhi : t ≤ (s.radius:ℝ) := ht.2
        constructor <;> linarith [hvsmall hv, hhi]
      calc
        _ ≤ ‖(t:ℂ)*s.direction‖+‖(x:ℂ)‖ := norm_sub_le _ _
        _ ≤ x+e := by
          simp only [StarLayer.direction,hv,↓reduceIte,norm_mul,Complex.norm_I,mul_one,
            Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx]
          linarith
  exact Measure.ae_smul_measure ((ae_map_iff hm.aemeasurable hset).2 ht) _

lemma starLayers_ae_distance_ray (ss : List StarLayer) (x e : ℝ)
    (hx : 0 ≤ x) (he : 0 ≤ e)
    (hr : ∀ s ∈ ss, (s.radius:ℝ) ≤ x)
    (hv : ∀ s ∈ ss, s.vertical = true → (s.radius:ℝ) ≤ e) :
    ∀ᵐ z ∂starLayerMeasure ss, ‖z-(x:ℂ)‖ ≤ x+e := by
  induction ss with
  | nil => simp [starLayerMeasure]
  | cons s ss ih =>
    rw [starLayerMeasure, ae_add_measure_iff]
    exact ⟨layer_ae_distance_ray s x e hx he (hr s (by simp)) (hv s (by simp)),
      ih (fun t ht => hr t (by simp [ht])) (fun t ht => hv t (by simp [ht]))⟩

lemma comparisonPotential_le_of_distance (w : ℂ) (R : ℝ) (hR : 1 ≤ R)
    (h : ∀ᵐ z ∂comparisonMeasure, ‖z-w‖ ≤ R) :
    comparisonPotential w ≤ Real.log R := by
  have hlo : 0 ≤ Real.log R := Real.log_nonneg hR
  have hh : ∀ᵐ z ∂comparisonMeasure, Real.log ‖z-w‖ ≤ Real.log R := by
    filter_upwards [h] with z hz
    by_cases he : z-w = 0
    · simpa [he] using! hlo
    · exact Real.log_le_log (norm_pos_iff.mpr he) hz
  have hi := integral_mono_ae (integrable_log_comparisonMeasure w)
    (integrable_const (Real.log R)) hh
  simpa [comparisonPotential] using! hi

theorem comparisonPotential_ray_tail (x : ℝ) (hx : 18 ≤ x) :
    comparisonPotential (x:ℂ) ≤ Real.log (x+2/25) := by
  apply comparisonPotential_le_of_distance _ _ (by linarith)
  apply starLayers_ae_distance_ray layerData x (2/25) (by linarith) (by norm_num)
  · intro s hs
    have hr : (s.radius:ℝ) ≤ 56/5 := by
      rw [show (56/5:ℝ) = ((56/5:ℚ):ℝ) by norm_num]
      exact Rat.cast_le.mpr (layerData_radii s hs).2
    linarith
  · norm_num [layerData]

theorem comparisonPotential_vertical_tail (y : ℝ) (hy : 2 ≤ y) :
    comparisonPotential ((y:ℂ)*Complex.I) ≤ Real.log (56/5+y) := by
  apply comparisonPotential_le_of_distance _ _ (by linarith)
  filter_upwards [ae_norm_comparisonMeasure] with z hz
  have h := norm_sub_le z ((y:ℂ)*Complex.I)
  simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ y by linarith)] at h
  linarith

end
end Li2Unified.Proofs.Potential
#print axioms Li2Unified.Proofs.Potential.comparisonPotential_ray_tail
#print axioms Li2Unified.Proofs.Potential.comparisonPotential_vertical_tail

end

section
/-! Sound arithmetic operations for rational intervals. No use of
native evaluation, external interval libraries, or unchecked certificates.
The actual finite quarter certificate is a separate obligation. -/
namespace Li2Unified.ParameterFamily

structure RationalBounds where
  lower : ℚ
  upper : ℚ

namespace RationalBounds

def Contains (a : RationalBounds) (x : ℝ) : Prop :=
  (a.lower:ℝ) ≤ x ∧ x ≤ (a.upper:ℝ)

def point (q : ℚ) : RationalBounds := ⟨q,q⟩
def add (a b : RationalBounds) : RationalBounds :=
  ⟨a.lower+b.lower,a.upper+b.upper⟩
def neg (a : RationalBounds) : RationalBounds := ⟨-a.upper,-a.lower⟩
def mul (a b : RationalBounds) : RationalBounds :=
  ⟨min (min (a.lower*b.lower) (a.lower*b.upper))
      (min (a.upper*b.lower) (a.upper*b.upper)),
   max (max (a.lower*b.lower) (a.lower*b.upper))
      (max (a.upper*b.lower) (a.upper*b.upper))⟩

theorem contains_point (q : ℚ) : (point q).Contains (q:ℝ) := ⟨le_rfl,le_rfl⟩

theorem contains_add {a b : RationalBounds} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (add a b).Contains (x+y) := by
  simpa only [Contains, add, Rat.cast_add] using!
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem contains_neg {a : RationalBounds} {x : ℝ}
    (hx : a.Contains x) : (neg a).Contains (-x) := by
  simpa only [Contains, neg, Rat.cast_neg] using!
    And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

private lemma product_upper (a x b c : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    x*c ≤ max (a*c) (b*c) := by
  by_cases hc : 0 ≤ c
  · exact (mul_le_mul_of_nonneg_right hb hc).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right ha (le_of_not_ge hc)).trans (le_max_left _ _)

private lemma product_lower (a x b c : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    min (a*c) (b*c) ≤ x*c := by
  by_cases hc : 0 ≤ c
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right ha hc)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hb (le_of_not_ge hc))

private lemma product_corners (a x b c y d : ℝ)
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
    x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have la : min (a*c) (a*d) ≤ a*y := by
    simpa only [mul_comm] using! product_lower c y d a hy.1 hy.2
  have lb : min (b*c) (b*d) ≤ b*y := by
    simpa only [mul_comm] using! product_lower c y d b hy.1 hy.2
  have ua : a*y ≤ max (a*c) (a*d) := by
    simpa only [mul_comm] using! product_upper c y d a hy.1 hy.2
  have ub : b*y ≤ max (b*c) (b*d) := by
    simpa only [mul_comm] using! product_upper c y d b hy.1 hy.2
  constructor
  · exact (min_le_min la lb).trans (product_lower a x b y hx.1 hx.2)
  · exact (product_upper a x b y hx.1 hx.2).trans (max_le_max ua ub)

theorem contains_mul {a b : RationalBounds} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (mul a b).Contains (x*y) := by
  simpa only [Contains, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul] using!
    product_corners (a.lower:ℝ) x (a.upper:ℝ) (b.lower:ℝ) y (b.upper:ℝ) hx hy

theorem contains_widen {a b : RationalBounds} {x : ℝ}
    (hx : a.Contains x) (hl : b.lower ≤ a.lower) (hu : a.upper ≤ b.upper) :
    b.Contains x := by
  constructor
  · exact (by exact_mod_cast hl : (b.lower:ℝ) ≤ a.lower).trans hx.1
  · exact hx.2.trans (by exact_mod_cast hu : (a.upper:ℝ) ≤ b.upper)

theorem contains_log {a b : RationalBounds} {x : ℝ}
    (hx : a.Contains x) (ha : 0 < a.lower)
    (hl : (b.lower:ℝ) ≤ Real.log (a.lower:ℝ))
    (hu : Real.log (a.upper:ℝ) ≤ (b.upper:ℝ)) : b.Contains (Real.log x) := by
  have ha' : (0:ℝ) < a.lower := by exact_mod_cast ha
  exact ⟨hl.trans (Real.log_le_log ha' hx.1),
    (Real.log_le_log (ha'.trans_le hx.1) hx.2).trans hu⟩

theorem contains_arctan {a b : RationalBounds} {x : ℝ}
    (hx : a.Contains x)
    (hl : (b.lower:ℝ) ≤ Real.arctan (a.lower:ℝ))
    (hu : Real.arctan (a.upper:ℝ) ≤ (b.upper:ℝ)) : b.Contains (Real.arctan x) :=
  ⟨hl.trans (Real.arctan_le_arctan_iff.mpr hx.1), (Real.arctan_le_arctan_iff.mpr hx.2).trans hu⟩

end RationalBounds
end Li2Unified.ParameterFamily

end


end
