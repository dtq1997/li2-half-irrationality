module
public import Li2Unified.Modular.Base.CompactLogTruncation
public import Li2Unified.Modular.Positive.Packed.P068
public import Li2Unified.Modular.Positive.Packed.P069

set_option backward.privateInPublic true

@[expose] public section

section
/-! Uniform finite-line truncation error for arbitrary complex centers.
The pointwise comparison excludes one real-coordinate fiber. Its measure is
zero; no value at the logarithmic singularity is silently changed. -/
open MeasureTheory Set intervalIntegral
namespace Li2Unified.ParameterFamily.Energy
noncomputable section

lemma log_truncation_sub_antitone (ε : ℝ) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    Real.log (max ε s) - Real.log s ≤ Real.log (max ε r) - Real.log r := by
  by_cases hs : s ≤ ε
  · rw [max_eq_left hs, max_eq_left (hrs.trans hs)]
    exact sub_le_sub_left (Real.log_le_log hr hrs) _
  · rw [max_eq_right (le_of_not_ge hs), sub_self]
    exact sub_nonneg.mpr (Real.log_le_log hr (le_max_right _ _))

lemma log_truncation_complex_real_le (ε : ℝ) (w : ℂ) (t : ℝ) (ht : t ≠ w.re) :
    Real.log (max ε ‖(t : ℂ) - w‖) - Real.log ‖(t : ℂ) - w‖ ≤
      Li2.realLogTruncationError ε w.re t := by
  rw [Li2.realLogTruncationError_eq_sub]
  have hr : 0 < |w.re - t| := abs_pos.mpr (sub_ne_zero.mpr ht.symm)
  have hb : |w.re - t| ≤ ‖(t : ℂ) - w‖ := by
    rw [abs_sub_comm]
    simpa only [Complex.sub_re, Complex.ofReal_re] using! Complex.abs_re_le_norm ((t : ℂ) - w)
  exact log_truncation_sub_antitone ε hr hb

theorem integral_log_truncated_real_le (w : ℂ) {ε a b : ℝ} (hε : 0 < ε) (hab : a ≤ b) :
    (∫ t in a..b, Real.log (max ε ‖(t : ℂ) - w‖)) ≤
      (∫ t in a..b, Real.log ‖(t : ℂ) - w‖) + 2 * ε := by
  have hraw : IntervalIntegrable (fun t : ℝ => Real.log ‖(t : ℂ) - w‖) volume a b := by
    simpa only [zero_add, mul_one] using! intervalIntegrable_log_line 0 1 w a b
  have hcut : IntervalIntegrable (fun t : ℝ => Real.log (max ε ‖(t : ℂ) - w‖)) volume a b :=
    ((continuous_const.max (Complex.continuous_ofReal.sub continuous_const).norm).log
      (fun t => (lt_of_lt_of_le hε (le_max_left _ _)).ne')).intervalIntegrable a b
  have herr := Li2.realLogTruncationError_integrable_and_integral hε w.re
  have hierr : IntervalIntegrable (Li2.realLogTruncationError ε w.re) volume a b :=
    herr.1.intervalIntegrable
  have hmono : (∫ t in a..b, Real.log (max ε ‖(t : ℂ) - w‖)) ≤
      ∫ t in a..b, (Real.log ‖(t : ℂ) - w‖ + Li2.realLogTruncationError ε w.re t) := by
    apply intervalIntegral.integral_mono_ae hab hcut (hraw.add hierr)
    filter_upwards [(volume : Measure ℝ).ae_ne w.re] with t ht
    have h := log_truncation_complex_real_le ε w t ht
    linarith only [h]
  have hbound : (∫ t in a..b, Li2.realLogTruncationError ε w.re t) ≤ 2 * ε := by
    rw [intervalIntegral.integral_of_le hab]
    calc
      _ ≤ ∫ t : ℝ, Li2.realLogTruncationError ε w.re t := by
        apply setIntegral_le_integral herr.1
        filter_upwards [(volume : Measure ℝ).ae_ne w.re] with t ht
        exact Li2.realLogTruncationError_nonneg_of_ne ht
      _ = _ := herr.2
  rw [intervalIntegral.integral_add hraw hierr] at hmono
  exact hmono.trans (add_le_add le_rfl hbound)

theorem integral_log_truncated_imag_le (w : ℂ) {ε a b : ℝ} (hε : 0 < ε) (hab : a ≤ b) :
    (∫ t in a..b, Real.log (max ε ‖(t : ℂ) * Complex.I - w‖)) ≤
      (∫ t in a..b, Real.log ‖(t : ℂ) * Complex.I - w‖) + 2 * ε := by
  simpa only [norm_imag_sub] using! integral_log_truncated_real_le (w / Complex.I) hε hab

end
end Li2Unified.ParameterFamily.Energy

end

section
/-! Exact all-point truncation control for the actual 36-layer comparison
measure, expressed as its literal finite sum of segment integrals. -/

open MeasureTheory Set intervalIntegral
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.ParameterFamily.Energy
open Li2Unified.Instances.PosHalf.LayerComparison

private lemma layer_truncated_integral_le (s : StarLayer) (hs : s.Valid)
    (w : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x in s.left..s.right,
      Real.log (max ε ‖(x : ℂ) * s.direction - w‖)) ≤
      (∫ x in s.left..s.right,
        Real.log ‖(x : ℂ) * s.direction - w‖) + 2 * ε := by
  have hab := s.left_le_right hs.1
  cases hv : s.vertical
  · simpa [StarLayer.direction, hv] using!
      integral_log_truncated_real_le w hε hab
  · simpa [StarLayer.direction, hv] using!
      integral_log_truncated_imag_le w hε hab

private lemma layerList_truncated_sum_le (ss : List StarLayer)
    (hvalid : ∀ s ∈ ss, s.Valid) (w : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (ss.map fun s => (s.density : ℝ) *
      ∫ x in s.left..s.right,
        Real.log (max ε ‖(x : ℂ) * s.direction - w‖)).sum ≤
      (ss.map fun s => (s.density : ℝ) *
        ∫ x in s.left..s.right,
          Real.log ‖(x : ℂ) * s.direction - w‖).sum +
        2 * ε * (ss.map fun s => (s.density : ℝ)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    have hs : s.Valid := hvalid s (by simp)
    have hrest : ∀ t ∈ ss, t.Valid := by
      intro t ht
      exact hvalid t (by simp [ht])
    have hd : (0 : ℝ) ≤ s.density := by exact_mod_cast hs.2
    have hline := layer_truncated_integral_le s hs w hε
    have hm := mul_le_mul_of_nonneg_left hline hd
    have htail := ih hrest
    simp only [List.map_cons, List.sum_cons]
    linarith only [hm, htail]

theorem actual_comparisonPotential_truncation_le (w : ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    (layerData.map fun s => (s.density : ℝ) *
      ∫ x in s.left..s.right,
        Real.log (max ε ‖(x : ℂ) * s.direction - w‖)).sum ≤
      comparisonPotential w + 11 / 10 * ε := by
  have hsum := layerList_truncated_sum_le layerData
    layerData_valid w hε
  have hmass : 2 * (layerData.map fun s => (s.density : ℝ)).sum ≤
      (11 / 10 : ℝ) := by
    norm_num [layerData]
  rw [comparisonPotential_eq] 
  have hscale := mul_le_mul_of_nonneg_right hmass hε.le
  linarith only [hsum, hscale]

end
end Li2Unified.Proofs.Contour

end


end
