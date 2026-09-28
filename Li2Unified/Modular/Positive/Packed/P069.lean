module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Tactic
public import Li2Unified.Modular.Positive.Packed.P068
public import Mathlib.MeasureTheory.Integral.Prod

set_option backward.privateInPublic true

@[expose] public section

section
/-! The negative logarithmic singularity has total line mass2.
The convention is Real.log0=0, which does not change Lebesgue integrals. -/
open MeasureTheory Set
namespace Li2Unified.ParameterFamily.Energy
noncomputable section

#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "NegativeLog: imports loaded"
  out.flush


def negativeLog (x : ℝ) : ℝ := max (-Real.log x) 0

lemma negativeLog_nonneg (x : ℝ) : 0 ≤ negativeLog x := le_max_right _ _

lemma negativeLog_eq_indicator : negativeLog =
    (Ioc (-1:ℝ) 1).indicator (fun x : ℝ => -Real.log x) := by
  funext x
  by_cases hx : x ∈ Ioc (-1:ℝ) 1
  · have ha : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2⟩
    have hl : Real.log x ≤ 0 := by
      rw [← Real.log_abs]
      exact Real.log_nonpos (abs_nonneg x) ha
    simp only [negativeLog, indicator_of_mem hx, max_eq_left (neg_nonneg.mpr hl)]
  · have ha : 1 ≤ |x| := by
      by_contra h
      have hlt : |x| < 1 := lt_of_not_ge h
      have hh := abs_lt.mp hlt
      exact hx ⟨hh.1, hh.2.le⟩
    have hl : 0 ≤ Real.log x := by
      rw [← Real.log_abs]
      exact Real.log_nonneg ha
    simp only [negativeLog, indicator_of_notMem hx, max_eq_right (neg_nonpos.mpr hl)]

lemma integrable_negativeLog : Integrable negativeLog := by
  rw [negativeLog_eq_indicator]
  exact (intervalIntegral.intervalIntegrable_log' (a := (-1:ℝ)) (b := 1)).1.neg.integrable_indicator measurableSet_Ioc

lemma integral_negativeLog : (∫ x : ℝ, negativeLog x) = 2 := by
  rw [negativeLog_eq_indicator, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    intervalIntegral.integral_neg, integral_log]
  norm_num

lemma integral_negativeLog_sub (a : ℝ) :
    (∫ x : ℝ, negativeLog (x-a)) = 2 := by
  rw [integral_sub_right_eq_self negativeLog a, integral_negativeLog]

lemma setIntegral_negativeLog_sub_le (a : ℝ) (s : Set ℝ) :
    (∫ x in s, negativeLog (x-a)) ≤ 2 := by
  calc
    _ ≤ ∫ x : ℝ, negativeLog (x-a) :=
      setIntegral_le_integral (integrable_negativeLog.comp_sub_right a)
        (Filter.Eventually.of_forall (fun x => negativeLog_nonneg (x-a)))
    _ = 2 := integral_negativeLog_sub a


#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "NegativeLog: declarations processed"
  out.flush

end
end Li2Unified.ParameterFamily.Energy

end

section
/-! Uniform negative-log bound2 on any real or imaginary line cell.
The real-coordinate exception is explicitly removed as a Lebesgue null singleton. -/
open MeasureTheory Set
namespace Li2Unified.ParameterFamily.Energy
noncomputable section

lemma negativeLog_norm_real_sub_le (w : ℂ) (x : ℝ) (hx : x ≠ w.re) :
    negativeLog ‖(x:ℂ)-w‖ ≤ negativeLog (x-w.re) := by
  have hb : |x-w.re| ≤ ‖(x:ℂ)-w‖ := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using Complex.abs_re_le_norm ((x:ℂ)-w)
  have ha : 0 < |x-w.re| := abs_pos.mpr (sub_ne_zero.mpr hx)
  have hl : Real.log (x-w.re) ≤ Real.log ‖(x:ℂ)-w‖ := by
    simpa only [Real.log_abs] using Real.log_le_log ha hb
  exact max_le_max (neg_le_neg hl) le_rfl

lemma ae_negativeLog_norm_real_sub_le (w : ℂ) :
    ∀ᵐ x : ℝ, negativeLog ‖(x:ℂ)-w‖ ≤ negativeLog (x-w.re) := by
  filter_upwards [(volume : Measure ℝ).ae_ne w.re] with x hx
  exact negativeLog_norm_real_sub_le w x hx

lemma integrable_negativeLog_norm_real_sub (w : ℂ) :
    Integrable (fun x : ℝ => negativeLog ‖(x:ℂ)-w‖) := by
  have hm : Measurable (fun x : ℝ => negativeLog ‖(x:ℂ)-w‖) := by
    unfold negativeLog
    fun_prop
  exact (integrable_negativeLog.comp_sub_right w.re).mono_nonneg hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => negativeLog_nonneg ‖(x:ℂ)-w‖))
    (ae_negativeLog_norm_real_sub_le w)

lemma setIntegral_negativeLog_norm_real_sub_le (w : ℂ) (s : Set ℝ) :
    (∫ x in s, negativeLog ‖(x:ℂ)-w‖) ≤ 2 := by
  have hb := integral_mono_ae (integrable_negativeLog_norm_real_sub w)
    (integrable_negativeLog.comp_sub_right w.re) (ae_negativeLog_norm_real_sub_le w)
  rw [integral_negativeLog_sub] at hb
  exact (setIntegral_le_integral (integrable_negativeLog_norm_real_sub w)
    (Filter.Eventually.of_forall (fun x => negativeLog_nonneg ‖(x:ℂ)-w‖))).trans hb

lemma norm_imag_sub (w : ℂ) (x : ℝ) :
    ‖(x:ℂ)*Complex.I-w‖ = ‖(x:ℂ)-w/Complex.I‖ := by
  have he : (x:ℂ)*Complex.I-w = ((x:ℂ)-w/Complex.I)*Complex.I := by
    field_simp [Complex.I_ne_zero]
    <;> ring
  rw [he, norm_mul, Complex.norm_I, mul_one]

lemma integrable_negativeLog_norm_imag_sub (w : ℂ) :
    Integrable (fun x : ℝ => negativeLog ‖(x:ℂ)*Complex.I-w‖) := by
  simpa only [norm_imag_sub] using integrable_negativeLog_norm_real_sub (w/Complex.I)

lemma setIntegral_negativeLog_norm_imag_sub_le (w : ℂ) (s : Set ℝ) :
    (∫ x in s, negativeLog ‖(x:ℂ)*Complex.I-w‖) ≤ 2 := by
  simpa only [norm_imag_sub] using setIntegral_negativeLog_norm_real_sub_le (w/Complex.I) s

end
end Li2Unified.ParameterFamily.Energy

end

section
/-! Actual integrals, support and negative-log bounds for finite star layers.
No numerical certificate or sharp potential/energy bound is assumed. -/
open MeasureTheory Set
namespace Li2Unified.ParameterFamily.Energy
noncomputable section
namespace StarLayer

lemma left_le_right (s : StarLayer) (hr : 0 ≤ s.radius) : s.left ≤ s.right := by
  have hr' : (0:ℝ) ≤ s.radius := by exact_mod_cast hr
  cases hv : s.vertical <;> simp [left, right, hv] <;> linarith

lemma integral_eq (s : StarLayer) (hs : s.Valid) (f : ℂ → ℝ) (hf : Measurable f) :
    (∫ z : ℂ, f z ∂s.measure) =
      (s.density : ℝ) * ∫ x in s.left..s.right, f ((x:ℂ)*s.direction) := by
  have hx : Measurable (fun x : ℝ => (x:ℂ)*s.direction) := by fun_prop
  have hd : (0:ℝ) ≤ s.density := by exact_mod_cast hs.2
  rw [measure, integral_smul_measure, ENNReal.toReal_ofReal hd, smul_eq_mul,
    integral_map hx.aemeasurable hf.aestronglyMeasurable,
    intervalIntegral.integral_of_le (s.left_le_right hs.1)]

lemma ae_norm (s : StarLayer) (R : ℝ) (hR : 0 ≤ R) (hr : (s.radius : ℝ) ≤ R) :
    ∀ᵐ z ∂s.measure, ‖z‖ ≤ R := by
  have hx : Measurable (fun x : ℝ => (x:ℂ)*s.direction) := by fun_prop
  have hm : MeasurableSet {z : ℂ | ‖z‖ ≤ R} :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hl : -R ≤ s.left := by
    cases hv : s.vertical <;> simp [left, hv] <;> linarith
  have ht : ∀ᵐ x : ℝ ∂(volume : Measure ℝ).restrict (Ioc s.left s.right),
      ‖(x:ℂ)*s.direction‖ ≤ R := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx'
    have ha : |x| ≤ R := abs_le.mpr ⟨hl.trans hx'.1.le, hx'.2.trans hr⟩
    cases hv : s.vertical <;>
      simpa [direction, hv, norm_mul, Complex.norm_real, Real.norm_eq_abs] using ha
  exact Measure.ae_smul_measure ((ae_map_iff hx.aemeasurable hm).2 ht) _

lemma integrable_negativeLog (s : StarLayer) (w : ℂ) :
    Integrable (fun z : ℂ => negativeLog ‖z-w‖) s.measure := by
  have hg : Measurable (fun z : ℂ => negativeLog ‖z-w‖) := by
    unfold negativeLog
    fun_prop
  have hf : Measurable (fun x : ℝ => (x:ℂ)*s.direction) := by fun_prop
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply (integrable_map_measure hg.aestronglyMeasurable hf.aemeasurable).2
  cases hv : s.vertical
  · simpa [direction, hv] using
      (integrable_negativeLog_norm_real_sub w).restrict (s := Ioc s.left s.right)
  · simpa [direction, hv] using
      (integrable_negativeLog_norm_imag_sub w).restrict (s := Ioc s.left s.right)

lemma integral_negativeLog_le (s : StarLayer) (w : ℂ) (hd : 0 ≤ s.density) :
    (∫ z : ℂ, negativeLog ‖z-w‖ ∂s.measure) ≤ 2*(s.density : ℝ) := by
  have hd' : (0:ℝ) ≤ s.density := by exact_mod_cast hd
  have hg : Measurable (fun z : ℂ => negativeLog ‖z-w‖) := by
    unfold negativeLog
    fun_prop
  have hf : Measurable (fun x : ℝ => (x:ℂ)*s.direction) := by fun_prop
  rw [measure, integral_smul_measure, ENNReal.toReal_ofReal hd', smul_eq_mul,
    integral_map hf.aemeasurable hg.aestronglyMeasurable]
  have hb : (∫ x in Ioc s.left s.right, negativeLog ‖(x:ℂ)*s.direction-w‖) ≤ 2 := by
    cases hv : s.vertical
    · simpa [direction, hv] using
        setIntegral_negativeLog_norm_real_sub_le w (Ioc s.left s.right)
    · simpa [direction, hv] using
        setIntegral_negativeLog_norm_imag_sub_le w (Ioc s.left s.right)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb hd'

end StarLayer

lemma ae_norm_starLayerMeasure (ss : List StarLayer) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ s ∈ ss, (s.radius : ℝ) ≤ R) :
    ∀ᵐ z ∂starLayerMeasure ss, ‖z‖ ≤ R := by
  induction ss with
  | nil => simp [starLayerMeasure]
  | cons s ss ih =>
    rw [starLayerMeasure, ae_add_measure_iff]
    exact ⟨s.ae_norm R hR (hr s (by simp)), ih (fun t ht => hr t (by simp [ht]))⟩

lemma integrable_negativeLog_starLayerMeasure (ss : List StarLayer) (w : ℂ) :
    Integrable (fun z : ℂ => negativeLog ‖z-w‖) (starLayerMeasure ss) := by
  induction ss with
  | nil => simp [starLayerMeasure]
  | cons s ss ih => exact (s.integrable_negativeLog w).add_measure ih

lemma integral_negativeLog_starLayerMeasure_le (ss : List StarLayer) (w : ℂ)
    (hd : ∀ s ∈ ss, 0 ≤ s.density) :
    (∫ z : ℂ, negativeLog ‖z-w‖ ∂starLayerMeasure ss) ≤
      ((2*(ss.map StarLayer.density).sum : ℚ) : ℝ) := by
  induction ss with
  | nil => simp [starLayerMeasure]
  | cons s ss ih =>
    have ht : ∀ t ∈ ss, 0 ≤ t.density := fun t ht => hd t (by simp [ht])
    rw [starLayerMeasure, integral_add_measure (s.integrable_negativeLog w)
      (integrable_negativeLog_starLayerMeasure ss w)]
    have h1 := s.integral_negativeLog_le w (hd s (by simp))
    have h2 := ih ht
    simp only [List.map_cons, List.sum_cons, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_add] at h2 ⊢
    linarith

lemma integral_starLayerMeasure (ss : List StarLayer) (hs : ∀ s ∈ ss, s.Valid)
    (f : ℂ → ℝ) (hf : Measurable f) (hi : Integrable f (starLayerMeasure ss)) :
    (∫ z : ℂ, f z ∂starLayerMeasure ss) =
      (ss.map (fun s => (s.density : ℝ) *
        ∫ x in s.left..s.right, f ((x:ℂ)*s.direction))).sum := by
  induction ss with
  | nil => simp [starLayerMeasure]
  | cons s ss ih =>
    have ht : ∀ t ∈ ss, t.Valid := fun t ht => hs t (by simp [ht])
    have h1 : Integrable f s.measure := hi.left_of_add_measure
    have h2 : Integrable f (starLayerMeasure ss) := hi.right_of_add_measure
    rw [starLayerMeasure, integral_add_measure h1 h2,
      s.integral_eq (hs s (by simp)) f hf, ih ht h2]
    rfl

end
end Li2Unified.ParameterFamily.Energy

end

section
/-! Joint logarithmic integrability and actual integral transport for
PosHalf's fixed 36-layer probability. No energy value or sharp potential bound. -/
open MeasureTheory Set
namespace Li2Unified.Instances.PosHalf.LayerComparison
noncomputable section
open Li2Unified.ParameterFamily.Energy

lemma ae_norm_comparisonMeasure : ∀ᵐ z ∂comparisonMeasure, ‖z‖ ≤ 56/5 := by
  apply ae_norm_starLayerMeasure layerData (56/5) (by norm_num)
  intro s hs
  rw [show (56/5 : ℝ) = ((56/5 : ℚ) : ℝ) by norm_num]
  exact Rat.cast_le.mpr (layerData_radii s hs).2

lemma integrable_negativeLog_comparisonMeasure (w : ℂ) :
    Integrable (fun z : ℂ => negativeLog ‖z-w‖) comparisonMeasure :=
  integrable_negativeLog_starLayerMeasure layerData w

lemma integral_negativeLog_comparisonMeasure_le (w : ℂ) :
    (∫ z : ℂ, negativeLog ‖z-w‖ ∂comparisonMeasure) ≤ 11/10 := by
  have h := integral_negativeLog_starLayerMeasure_le layerData w
    (fun s hs => (layerData_valid s hs).2)
  have hb : ((2*(layerData.map StarLayer.density).sum : ℚ) : ℝ) ≤ 11/10 := by
    rw [show (11/10 : ℝ) = ((11/10 : ℚ) : ℝ) by norm_num]
    exact Rat.cast_le.mpr layerData_density_bound
  exact h.trans hb

lemma ae_log_norm_sub_le (w : ℂ) :
    ∀ᵐ z ∂comparisonMeasure, Real.log ‖z-w‖ ≤ Real.log (56/5+‖w‖) := by
  filter_upwards [ae_norm_comparisonMeasure] with z hz
  by_cases hd : z-w = 0
  · rw [hd, norm_zero, Real.log_zero]
    exact Real.log_nonneg (by linarith [norm_nonneg w])
  · exact Real.log_le_log (norm_pos_iff.mpr hd)
      ((norm_sub_le z w).trans (add_le_add hz le_rfl))

lemma integral_abs_log_comparisonMeasure_le (w : ℂ) :
    (∫ z : ℂ, |Real.log ‖z-w‖| ∂comparisonMeasure) ≤ 11/10 + Real.log (56/5+‖w‖) := by
  have hn := integrable_negativeLog_comparisonMeasure w
  have hl := integrable_log_comparisonMeasure w
  have hC : 0 ≤ Real.log (56/5+‖w‖) := Real.log_nonneg (by linarith [norm_nonneg w])
  have hb : ∀ᵐ z ∂comparisonMeasure,
      |Real.log ‖z-w‖| ≤ negativeLog ‖z-w‖ + Real.log (56/5+‖w‖) := by
    filter_upwards [ae_log_norm_sub_le w] with z hz
    unfold negativeLog
    apply abs_le.mpr
    constructor
    · linarith [le_max_left (-Real.log ‖z-w‖) (0:ℝ)]
    · linarith [le_max_right (-Real.log ‖z-w‖) (0:ℝ)]
  calc
    _ ≤ ∫ z : ℂ, (negativeLog ‖z-w‖ + Real.log (56/5+‖w‖)) ∂comparisonMeasure :=
      integral_mono_ae hl.abs (hn.add (integrable_const _)) hb
    _ = (∫ z : ℂ, negativeLog ‖z-w‖ ∂comparisonMeasure) + Real.log (56/5+‖w‖) := by
      rw [integral_add hn (integrable_const _)]
      simp
    _ ≤ _ := add_le_add (integral_negativeLog_comparisonMeasure_le w) le_rfl

lemma integrable_log_comparison_prod :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖)
      (comparisonMeasure.prod comparisonMeasure) := by
  have hm : AEStronglyMeasurable (fun p : ℂ × ℂ => Real.log ‖p.2-p.1‖)
      (comparisonMeasure.prod comparisonMeasure) :=
    ((measurable_snd.sub measurable_fst).norm.log).aestronglyMeasurable
  have h : Integrable (fun p : ℂ × ℂ => Real.log ‖p.2-p.1‖)
      (comparisonMeasure.prod comparisonMeasure) := by
    apply (integrable_prod_iff hm).2
    constructor
    · exact Filter.Eventually.of_forall (fun w => integrable_log_comparisonMeasure w)
    · have hi : AEStronglyMeasurable
          (fun w : ℂ => ∫ z : ℂ, ‖Real.log ‖z-w‖‖ ∂comparisonMeasure) comparisonMeasure :=
        hm.norm.integral_prod_right'
      apply (integrable_const (11/10 + Real.log (112/5:ℝ))).mono' hi
      filter_upwards [ae_norm_comparisonMeasure] with w hw
      have hn : 0 ≤ ∫ z : ℂ, ‖Real.log ‖z-w‖‖ ∂comparisonMeasure :=
        integral_nonneg (fun z => norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      have hlog : Real.log (56/5+‖w‖) ≤ Real.log (112/5:ℝ) :=
        Real.log_le_log (by linarith [norm_nonneg w]) (by linarith)
      simpa only [Real.norm_eq_abs] using
        (integral_abs_log_comparisonMeasure_le w).trans (add_le_add le_rfl hlog)
  simpa only [norm_sub_rev] using h

lemma integral_comparisonMeasure (f : ℂ → ℝ) (hf : Measurable f)
    (hi : Integrable f comparisonMeasure) :
    (∫ z : ℂ, f z ∂comparisonMeasure) =
      (layerData.map (fun s => (s.density : ℝ) *
        ∫ x in s.left..s.right, f ((x:ℂ)*s.direction))).sum :=
  integral_starLayerMeasure layerData layerData_valid f hf hi

lemma measurable_comparisonPotential : Measurable comparisonPotential := by
  have hm : Measurable (fun p : ℂ × ℂ => Real.log ‖p.2-p.1‖) :=
    (measurable_snd.sub measurable_fst).norm.log
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma integrable_comparisonPotential : Integrable comparisonPotential comparisonMeasure :=
  integrable_log_comparison_prod.integral_prod_right

lemma comparisonPotential_eq (w : ℂ) :
    comparisonPotential w =
      (layerData.map (fun s => (s.density : ℝ) *
        ∫ x in s.left..s.right, Real.log ‖(x:ℂ)*s.direction-w‖)).sum :=
  integral_comparisonMeasure _ ((measurable_id.sub_const w).norm.log)
    (integrable_log_comparisonMeasure w)

lemma comparisonEnergy_eq_integral_potential :
    comparisonEnergy = ∫ w : ℂ, comparisonPotential w ∂comparisonMeasure :=
  integral_prod_symm _ integrable_log_comparison_prod

lemma comparisonEnergy_eq :
    comparisonEnergy =
      (layerData.map (fun s => (s.density : ℝ) *
        ∫ x in s.left..s.right, comparisonPotential ((x:ℂ)*s.direction))).sum := by
  rw [comparisonEnergy_eq_integral_potential]
  exact integral_comparisonMeasure _ measurable_comparisonPotential integrable_comparisonPotential

end
end Li2Unified.Instances.PosHalf.LayerComparison

end


end
