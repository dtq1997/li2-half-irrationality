module
public import Li2Unified.Modular.Base.CompactLogPotential
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

set_option backward.privateInPublic true

@[expose] public section
open MeasureTheory Set intervalIntegral
namespace Li2
noncomputable section

/-- Its literal value at the singular point is retained; positivity is a.e. -/
def realLogTruncationError (ε x t : ℝ) : ℝ :=
  (Icc (x - ε) (x + ε)).indicator (fun s : ℝ => Real.log ε - Real.log |x - s|) t

lemma realLogTruncationError_eq_sub (ε x t : ℝ) :
    realLogTruncationError ε x t = Real.log (max ε |x - t|) - Real.log |x - t| := by
  have hmem : t ∈ Icc (x - ε) (x + ε) ↔ |x - t| ≤ ε := by
    constructor
    · intro ht
      apply abs_le.mpr
      constructor
      · linarith [ht.2]
      · linarith [ht.1]
    · intro ht
      rcases abs_le.mp ht with ⟨hlo, hhi⟩
      constructor <;> linarith
  by_cases h : |x - t| ≤ ε
  · simp only [realLogTruncationError, Set.indicator_of_mem (hmem.mpr h), max_eq_left h]
  · have ht : t ∉ Icc (x - ε) (x + ε) := fun ht => h (hmem.mp ht)
    simp only [realLogTruncationError, Set.indicator, if_neg ht,
      max_eq_right (lt_of_not_ge h).le, sub_self]

lemma realLogTruncationError_nonneg_of_ne {ε x t : ℝ} (ht : t ≠ x) :
    0 ≤ realLogTruncationError ε x t := by
  rw [realLogTruncationError_eq_sub]
  apply sub_nonneg.mpr
  exact Real.log_le_log (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm ht))) (le_max_right _ _)

/-- Exact total mass of the scalar truncation error kernel. -/
theorem realLogTruncationError_integrable_and_integral {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Integrable (realLogTruncationError ε x) volume ∧
      (∫ t : ℝ, realLogTruncationError ε x t) = 2 * ε := by
  have hab : x - ε ≤ x + ε := by linarith
  have hlog : IntervalIntegrable (fun t : ℝ => Real.log |x - t|) volume (x - ε) (x + ε) := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := -ε) (b := ε)).comp_sub_left x
    simpa only [sub_neg_eq_add, Real.log_abs] using h.symm
  have hconst : IntervalIntegrable (fun _ : ℝ => Real.log ε) volume (x - ε) (x + ε) :=
    intervalIntegral.intervalIntegrable_const
  have hdiff : IntervalIntegrable (fun t : ℝ => Real.log ε - Real.log |x - t|)
      volume (x - ε) (x + ε) := hconst.sub hlog
  have hdiffOn : IntegrableOn (fun t : ℝ => Real.log ε - Real.log |x - t|)
      (Icc (x - ε) (x + ε)) volume := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hdiff
  have hlogIntegral : (∫ t : ℝ in (x - ε)..(x + ε), Real.log |x - t|) =
      2 * ε * Real.log ε - 2 * ε := by
    simp only [Real.log_abs]
    rw [intervalIntegral.integral_comp_sub_left]
    rw [show x - (x + ε) = -ε by ring, show x - (x - ε) = ε by ring,
      integral_log, Real.log_neg_eq_log]
    ring
  refine ⟨?_, ?_⟩
  · exact hdiffOn.integrable_indicator measurableSet_Icc
  · unfold realLogTruncationError
    rw [MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_sub hconst hlog,
      intervalIntegral.integral_const, hlogIntegral]
    simp only [smul_eq_mul]
    ring

theorem integrable_compactLogPotential_truncated_integrand {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hρsupport : HasCompactSupport ρ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Integrable (fun t : ℝ => ρ t * Real.log (max ε |x - t|)) volume := by
  have hpos (t : ℝ) : 0 < max ε |x - t| := lt_of_lt_of_le hε (le_max_left _ _)
  have hlog : Continuous (fun t : ℝ => Real.log (max ε |x - t|)) :=
    (continuous_const.max (continuous_const.sub continuous_id).abs).log (fun t => (hpos t).ne')
  exact (hρ.mul hlog).integrable_of_hasCompactSupport hρsupport.mul_right

/-- Scalar density truncation; no circle geometry or zero-mass energy is assumed. -/
theorem compactLogPotential_truncated_integrable_and_le {ρ : ℝ → ℝ} {M ε : ℝ}
    (hρ : Continuous ρ) (hρsupport : HasCompactSupport ρ)
    (hρbounds : ∀ t : ℝ, 0 ≤ ρ t ∧ ρ t ≤ M) (hε : 0 < ε) (x : ℝ) :
    Integrable (fun t : ℝ => ρ t * Real.log (max ε |x - t|)) volume ∧
    (∫ t : ℝ, ρ t * Real.log (max ε |x - t|)) ≤
      (∫ t : ℝ, ρ t * Real.log |x - t|) + 2 * M * ε := by
  have hcut := integrable_compactLogPotential_truncated_integrand hρ hρsupport hε x
  have hraw := integrable_compactLogPotential_integrand hρ hρsupport x
  have herr := realLogTruncationError_integrable_and_integral hε x
  refine ⟨hcut, ?_⟩
  have hmono : (∫ t : ℝ, ρ t * Real.log (max ε |x - t|)) ≤
      ∫ t : ℝ, (ρ t * Real.log |x - t| + M * realLogTruncationError ε x t) := by
    apply MeasureTheory.integral_mono_ae hcut (hraw.add (herr.1.const_mul M))
    filter_upwards [(volume : Measure ℝ).ae_ne x] with t ht
    have hnonneg := realLogTruncationError_nonneg_of_ne (ε := ε) ht
    have hmul := mul_le_mul_of_nonneg_right (hρbounds t).2 hnonneg
    calc
      ρ t * Real.log (max ε |x - t|) =
          ρ t * Real.log |x - t| + ρ t * realLogTruncationError ε x t := by
        rw [realLogTruncationError_eq_sub]; ring
      _ ≤ ρ t * Real.log |x - t| + M * realLogTruncationError ε x t := by linarith only [hmul]
  rw [MeasureTheory.integral_add hraw (herr.1.const_mul M), MeasureTheory.integral_const_mul, herr.2] at hmono
  calc
    (∫ t : ℝ, ρ t * Real.log (max ε |x - t|)) ≤
        (∫ t : ℝ, ρ t * Real.log |x - t|) + M * (2 * ε) := hmono
    _ = (∫ t : ℝ, ρ t * Real.log |x - t|) + 2 * M * ε := by ring
end
end Li2

end
