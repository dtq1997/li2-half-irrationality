module
public import Li2Unified.Modular.Positive.Packed.P083
public import Li2Unified.Modular.Base.OriginalContourHorizontalTails
public import Li2Unified.Modular.Base.OriginalContourIntegrable

set_option backward.privateInPublic true

@[expose] public section

section
/-! The literal real-ray star density times the original quotient is integrable. -/

open Polynomial MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

private lemma ray_power_norm_le (t : ℝ) (_ht : 0 ≤ t) :
    ‖power (point ⟨0, by decide⟩ t)‖ ≤ Real.exp (-Real.log 2 * t) := by
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    simp [one_div, Real.log_inv]
  have hlogpos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [point_ray]
  unfold power
  rw [Complex.norm_exp]
  have hre : (((Real.log (1 / 2 : ℝ) : ℂ) *
      (((1 / 2 + t : ℝ) : ℂ))).re) = -Real.log 2 * (1 / 2 + t) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, hlog]
  rw [hre]
  apply Real.exp_le_exp.mpr
  nlinarith

private lemma continuousOn_ray_density_integrand (d : ℕ) (F : ℚ[X]) :
    ContinuousOn (fun t : ℝ => density ⟨0, by decide⟩ t *
      Li2.originalComplexQuotient d F (point ⟨0, by decide⟩ t)) (Ioi 0) := by
  intro t ht
  have hz : 0 < (point ⟨0, by decide⟩ t).re := by
    rw [point_ray]
    simpa using (show 0 < (1 / 2 + t : ℝ) by linarith [Set.mem_Ioi.mp ht])
  have hp : ContinuousAt (fun s : ℝ => point ⟨0, by decide⟩ s) t := by
    have h : Continuous (fun s : ℝ => point ⟨0, by decide⟩ s) := by
      simp only [point_ray]
      fun_prop
    exact h.continuousAt
  have hq : ContinuousAt (fun s : ℝ =>
      Li2.originalComplexQuotient d F (point ⟨0, by decide⟩ s)) t :=
    (Li2.analyticAt_originalComplexQuotient d F hz).continuousAt.comp hp
  have hdens : ContinuousAt (fun s : ℝ => density ⟨0, by decide⟩ s) t := by
    change ContinuousAt (fun s : ℝ =>
      (Real.log 2 : ℂ) * point ⟨0, by decide⟩ s * power (point ⟨0, by decide⟩ s)) t
    have hpCont : Continuous (fun s : ℝ => point ⟨0, by decide⟩ s) := by
      simp only [point_ray]
      fun_prop
    have hpow : Continuous power := by unfold power; fun_prop
    exact ((continuous_const.mul hpCont).mul (hpow.comp hpCont)).continuousAt
  exact (hdens.mul hq).continuousWithinAt

lemma ray_density_norm_le (d : ℕ) (F : ℚ[X]) (t : ℝ) (ht : 0 ≤ t) :
    ‖density ⟨0, by decide⟩ t *
      Li2.originalComplexQuotient d F (point ⟨0, by decide⟩ t)‖ ≤
      Real.log 2 * Li2.originalCoefficientNormSum F *
        ((1 + t) ^ (F.natDegree + 1) * Real.exp (-Real.log 2 * t)) := by
  let z : ℂ := point ⟨0, by decide⟩ t
  let C : ℝ := Li2.originalCoefficientNormSum F
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hzre : 0 ≤ z.re := by
    dsimp [z]
    simp only [point, Fin.val_zero, ↓reduceIte]
    simp only [Complex.ofReal_re]
    linarith
  have hz : ‖z‖ ≤ 1 + t := by
    dsimp [z]
    simp only [point, Fin.val_zero, ↓reduceIte]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hR : 1 ≤ 1 + t := by linarith
  have hF : ‖F.eval₂ (Rat.castHom ℂ) z‖ ≤ C * (1 + t) ^ F.natDegree :=
    Li2.originalComplexEval_norm_le_of_norm_le F z (1 + t) hR hz
  have hD : 1 ≤ ‖(Li2.D d).eval₂ (Rat.castHom ℂ) z‖ :=
    Li2.D_eval₂_complex_norm_ge_one_of_re_nonneg d hzre
  have hq : ‖Li2.originalComplexQuotient d F z‖ ≤
      C * (1 + t) ^ F.natDegree := by
    rw [Li2.originalComplexQuotient, norm_div]
    exact (div_le_self (norm_nonneg _) hD).trans hF
  have hp : ‖power z‖ ≤ Real.exp (-Real.log 2 * t) :=
    ray_power_norm_le t ht
  change ‖((Real.log 2 : ℂ) * z * power z) *
      Li2.originalComplexQuotient d F z‖ ≤ _
  calc
    _ = Real.log 2 * ‖z‖ * ‖power z‖ *
          ‖Li2.originalComplexQuotient d F z‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    _ ≤ Real.log 2 * (1 + t) * Real.exp (-Real.log 2 * t) *
          (C * (1 + t) ^ F.natDegree) := by
      gcongr
    _ = _ := by rw [pow_succ]; ring

lemma ray_density_integrableOn (d : ℕ) (F : ℚ[X]) :
    IntegrableOn (fun t : ℝ => density ⟨0, by decide⟩ t *
      Li2.originalComplexQuotient d F (point ⟨0, by decide⟩ t)) (Ioi 0) := by
  let C : ℝ := Real.log 2 * Li2.originalCoefficientNormSum F
  have hm : Integrable (fun t : ℝ =>
      C * ((1 + |t|) ^ (F.natDegree + 1) * Real.exp (-Real.log 2 * |t|))) :=
    (Li2.original_integrable_one_add_abs_pow_exp (F.natDegree + 1)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2))).const_mul C
  apply hm.integrableOn.mono'
    ((continuousOn_ray_density_integrand d F).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  change ‖density ⟨0, by decide⟩ t *
    Li2.originalComplexQuotient d F (point ⟨0, by decide⟩ t)‖ ≤ _
  dsimp [C]
  rw [abs_of_pos ht]
  exact ray_density_norm_le d F t ht.le

end
end Li2Unified.Proofs.Contour

end


end
