module
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic
public import Li2Unified.Modular.Positive.Packed.P183
public import Li2Unified.Modular.Positive.Packed.P189
public import Li2Unified.Modular.Positive.Packed.P185
public import Li2Unified.Modular.Positive.Packed.P069
public import Mathlib.MeasureTheory.Integral.Prod

set_option backward.privateInPublic true

@[expose] public section

section
/-! Null fibers imply null pair collisions. These statements concern
restricted Lebesgue parameters and are independent of logarithmic integrability. -/
open MeasureTheory Set Filter
namespace Li2Unified.ParameterFamily.Energy
noncomputable section

#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "Noncollision: imports loaded"
  out.flush

lemma circle_fiber_null (c w : ℂ) (r a b : ℝ) (hr : r ≠ 0) :
    (volume.restrict (Ioc a b)) {t : ℝ | circleMap c r t = w} = 0 := by
  have h := (Set.countable_singleton w).preimage_circleMap c hr
  simpa using! h.measure_zero (volume.restrict (Ioc a b))

lemma pair_collision_null (f g : ℝ → ℂ) (μ ν : Measure ℝ) [SFinite ν]
    (hf : Continuous f) (hg : Continuous g)
    (hnull : ∀ w : ℂ, ν {t : ℝ | g t = w} = 0) :
    (μ.prod ν) {p : ℝ × ℝ | f p.1 = g p.2} = 0 := by
  have hm : MeasurableSet {p : ℝ × ℝ | f p.1 = g p.2} :=
    (isClosed_eq (hf.comp continuous_fst) (hg.comp continuous_snd)).measurableSet
  apply Measure.measure_prod_null_of_ae_null hm
  exact Filter.Eventually.of_forall (fun x => by simpa [eq_comm] using! hnull (f x))

#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "Noncollision: declarations processed"
  out.flush

end
end Li2Unified.ParameterFamily.Energy

end

section
/-! Every actual positive-radius layer has null fibers on the angular
interval, even though its clipped parameterization is constant outside it. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy

lemma starLayerCurve_fiber_null (s : StarLayer) (hr : 0 < s.radius)
    (w : ℂ) :
    (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))
      {θ : ℝ | starLayerCurve s θ = w} = 0 := by
  have hw : s.left < s.right := by
    have hr' : (0 : ℝ) < s.radius := by exact_mod_cast hr
    cases hv : s.vertical <;> simp [StarLayer.left, StarLayer.right, hv] <;> linarith
  have hdir : s.direction ≠ 0 := by
    cases hv : s.vertical <;> simp [StarLayer.direction, hv]
  have hslope : (s.right - s.left) / (2 * Real.pi) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hw.ne')
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hfiber :
      ({θ : ℝ | starLayerCurve s θ = w} ∩ Ioc (0 : ℝ) (2 * Real.pi)).Subsingleton := by
    rintro θ ⟨hθw, hθ⟩ φ ⟨hφw, hφ⟩
    have he := hθw.trans hφw.symm
    rw [starLayerCurve_on s ⟨hθ.1.le, hθ.2⟩,
      starLayerCurve_on s ⟨hφ.1.le, hφ.2⟩] at he
    have he' :
        (((s.right - s.left) / (2 * Real.pi) * θ + s.left : ℝ) : ℂ) =
          (((s.right - s.left) / (2 * Real.pi) * φ + s.left : ℝ) : ℂ) :=
      mul_right_cancel₀ hdir he
    have hre := congrArg Complex.re he'
    simp only [Complex.ofReal_re] at hre
    exact mul_left_cancel₀ hslope (add_right_cancel hre)
  rw [Measure.restrict_apply' measurableSet_Ioc]
  exact hfiber.countable.measure_zero (volume : Measure ℝ)

end
end Li2Unified.Proofs.Contour

end

section
/-! All ordered pairs of actual particle circles and comparison layers avoid
collision almost everywhere, including coincident centers and self-pairs. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

theorem starProfile_ae_ne (h : ℕ) (x : Fin h → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ k l : starProfileIndex h,
      ∀ᵐ p : ℝ × ℝ ∂(μcirc.prod μcirc),
        starProfileCurve h x ε k p.1 ≠ starProfileCurve h x ε l p.2 := by
  have hcont (k : starProfileIndex h) :
      Continuous (starProfileCurve h x ε k) := by
    cases k with
    | inl i => exact continuous_circleMap (x i) ε
    | inr j => exact continuous_starLayerCurve (layerData.get j)
  have hfiber (k : starProfileIndex h) (w : ℂ) :
      μcirc {θ : ℝ | starProfileCurve h x ε k θ = w} = 0 := by
    cases k with
    | inl i =>
        exact circle_fiber_null (x i) w ε 0 (2 * Real.pi) hε.ne'
    | inr j =>
        exact starLayerCurve_fiber_null (layerData.get j)
          (layerData_radii _ (List.get_mem layerData j)).1 w
  intro k l
  have hpair := pair_collision_null
    (starProfileCurve h x ε k) (starProfileCurve h x ε l)
    μcirc μcirc (hcont k) (hcont l) (hfiber l)
  apply MeasureTheory.ae_iff.mpr
  simpa only [not_not] using! hpair

end
end Li2Unified.Proofs.Contour

end

section
/-! Joint absolute integrability of the genuine weighted log kernel for every
ordered pair among the fixed 36 comparison layers. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

private lemma layer_measure_le (ss : List StarLayer) {t : StarLayer}
    (ht : t ∈ ss) : t.measure ≤ starLayerMeasure ss := by
  induction ss with
  | nil => simp at ht
  | cons s ss ih =>
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Measure.le_add_right le_rfl
      · exact (ih ht').trans (Measure.le_add_left le_rfl)

private lemma layer_width_pos (s : StarLayer) (hr : 0 < s.radius) :
    s.left < s.right := by
  have hr' : (0 : ℝ) < s.radius := by exact_mod_cast hr
  cases hv : s.vertical <;> simp [StarLayer.left, StarLayer.right, hv] <;> linarith

def angularLayerPairKernel (s t : StarLayer) (θ φ : ℝ) : ℝ :=
  starLayerAngularDensity s * starLayerAngularDensity t *
    Real.log ‖starLayerCurve s θ - starLayerCurve t φ‖

theorem integrable_angularLayerPairKernel {s t : StarLayer}
    (hs : s ∈ layerData) (ht : t ∈ layerData) :
    Integrable (fun p : ℝ × ℝ => angularLayerPairKernel s t p.1 p.2)
      (μcirc.prod μcirc) := by
  have hvs := layerData_valid s hs
  have hvt := layerData_valid t ht
  have hrs := (layerData_radii s hs).1
  have hrt := (layerData_radii t ht).1
  have hρs : 0 ≤ starLayerAngularDensity s := by
    have hd : (0 : ℝ) ≤ s.density := by exact_mod_cast hvs.2
    exact div_nonneg (mul_nonneg hd (sub_nonneg.mpr (s.left_le_right hvs.1)))
      (by positivity)
  have hρt : 0 ≤ starLayerAngularDensity t := by
    have hd : (0 : ℝ) ≤ t.density := by exact_mod_cast hvt.2
    exact div_nonneg (mul_nonneg hd (sub_nonneg.mpr (t.left_le_right hvt.1)))
      (by positivity)
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      angularLayerPairKernel s t p.1 p.2) := by
    unfold angularLayerPairKernel
    exact (measurable_const.mul measurable_const).mul
      ((((continuous_starLayerCurve s).measurable.comp measurable_fst).sub
        ((continuous_starLayerCurve t).measurable.comp measurable_snd)).norm.log)
  have hrow (θ : ℝ) : IntervalIntegrable
      (fun φ => angularLayerPairKernel s t θ φ) volume 0 (2 * Real.pi) := by
    have h := starLayer_intervalIntegrable_log t (layer_width_pos t hrt)
      (starLayerCurve s θ)
    change IntervalIntegrable
      (fun φ => starLayerAngularDensity s * starLayerAngularDensity t *
        Real.log ‖starLayerCurve s θ - starLayerCurve t φ‖)
      volume 0 (2 * Real.pi)
    have hsymmetric : ∀ φ : ℝ,
        Real.log ‖starLayerCurve s θ - starLayerCurve t φ‖ =
          Real.log ‖starLayerCurve t φ - starLayerCurve s θ‖ := by
      intro φ; rw [norm_sub_rev]
    simpa only [hsymmetric] using! h.const_mul
      (starLayerAngularDensity s * starLayerAngularDensity t)
  have hrow_norm (θ : ℝ) :
      (∫ φ in (0 : ℝ)..2 * Real.pi,
        ‖angularLayerPairKernel s t θ φ‖) =
        starLayerAngularDensity s *
          (∫ z : ℂ, |Real.log ‖starLayerCurve s θ - z‖| ∂t.measure) := by
    have he (φ : ℝ) :
        ‖angularLayerPairKernel s t θ φ‖ =
          starLayerAngularDensity s * starLayerAngularDensity t *
            |Real.log ‖starLayerCurve s θ - starLayerCurve t φ‖| := by
      simp [angularLayerPairKernel, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg hρs, abs_of_nonneg hρt]
    calc
      _ = starLayerAngularDensity s *
          (∫ φ in (0 : ℝ)..2 * Real.pi,
            starLayerAngularDensity t *
              |Real.log ‖starLayerCurve s θ - starLayerCurve t φ‖|) := by
        simp_rw [he, mul_assoc]
        rw [intervalIntegral.integral_const_mul]
      _ = starLayerAngularDensity s *
          ((t.density : ℝ) * ∫ y in t.left..t.right,
            |Real.log ‖starLayerCurve s θ - ((y : ℂ) * t.direction)‖|) := by
        congr 1
        exact starLayer_angular_integral t
          (fun z => |Real.log ‖starLayerCurve s θ - z‖|)
      _ = _ := by
        congr 1
        exact (t.integral_eq hvt (fun z => |Real.log ‖starLayerCurve s θ - z‖|)
          (by simpa only [Real.norm_eq_abs] using!
            ((measurable_const (a := starLayerCurve s θ)).sub measurable_id).norm.log.norm)).symm
  have hmt : t.measure ≤ comparisonMeasure := layer_measure_le layerData ht
  have hrow_le (θ : ℝ) :
      (∫ φ in (0 : ℝ)..2 * Real.pi,
        ‖angularLayerPairKernel s t θ φ‖) ≤
          starLayerAngularDensity s * (11 / 10 + Real.log (112 / 5 : ℝ)) := by
    rw [hrow_norm]
    have hr : ((s.radius : ℝ)) ≤ 56 / 5 := by
      rw [show (56 / 5 : ℝ) = ((56 / 5 : ℚ) : ℝ) by norm_num]
      exact Rat.cast_le.mpr (layerData_radii s hs).2
    have hw : ‖starLayerCurve s θ‖ ≤ 56 / 5 :=
      (starLayerCurve_norm_le s hvs θ).trans hr
    have hcomp : Integrable (fun z : ℂ =>
        |Real.log ‖starLayerCurve s θ - z‖|) comparisonMeasure := by
      simpa only [norm_sub_rev] using!
        (integrable_log_comparisonMeasure (starLayerCurve s θ)).abs
    have hm :
        (∫ z : ℂ, |Real.log ‖starLayerCurve s θ - z‖| ∂t.measure) ≤
          ∫ z : ℂ, |Real.log ‖starLayerCurve s θ - z‖| ∂comparisonMeasure := by
      apply integral_mono_measure hmt
      · exact Filter.Eventually.of_forall (fun z => abs_nonneg _)
      · exact hcomp
    have hc :
        (∫ z : ℂ, |Real.log ‖starLayerCurve s θ - z‖| ∂comparisonMeasure) ≤
          11 / 10 + Real.log (56 / 5 + ‖starLayerCurve s θ‖) := by
      simpa only [norm_sub_rev] using!
        integral_abs_log_comparisonMeasure_le (starLayerCurve s θ)
    have hlog : Real.log (56 / 5 + ‖starLayerCurve s θ‖) ≤
        Real.log (112 / 5 : ℝ) :=
      Real.log_le_log (by linarith [norm_nonneg (starLayerCurve s θ)]) (by linarith)
    exact mul_le_mul_of_nonneg_left
      (hm.trans (hc.trans (add_le_add le_rfl hlog))) hρs
  apply (integrable_prod_iff hmeas.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (fun θ =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1 (hrow θ))
  · have hm : AEStronglyMeasurable
        (fun θ : ℝ => ∫ φ : ℝ,
          ‖angularLayerPairKernel s t θ φ‖ ∂μcirc) μcirc :=
        hmeas.aestronglyMeasurable.norm.integral_prod_right'
    apply (integrable_const
      (starLayerAngularDensity s * (11 / 10 + Real.log (112 / 5 : ℝ)))).mono' hm
    filter_upwards [] with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
      ← intervalIntegral.integral_of_le (by positivity)]
    exact hrow_le θ

end
end Li2Unified.Proofs.Contour

end

end
