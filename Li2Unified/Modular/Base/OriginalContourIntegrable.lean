module
public import Li2Unified.Modular.Base.OriginalContourKernel
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option backward.privateInPublic true

@[expose] public section

open Set MeasureTheory
namespace Li2
noncomputable section

lemma original_integrable_abs_pow_exp (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => |x| ^ n * Real.exp (-b * |x|)) := by
  have hp : IntegrableOn (fun x : ℝ => |x| ^ n * Real.exp (-b * |x|)) (Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-b * x)) (Ioi 0) := by
      simpa only [Real.rpow_natCast, Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1)
          (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n))
          (by norm_num) hb)
    exact h.congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hp⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero] using hp

lemma original_integrable_one_add_abs_pow_exp (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => (1 + |x|) ^ n * Real.exp (-b * |x|)) := by
  have hm : Integrable (fun x : ℝ =>
      (2 : ℝ) ^ (n - 1) * (1 + |x| ^ n) * Real.exp (-b * |x|)) := by
    convert ((original_integrable_abs_pow_exp 0 hb).add
      (original_integrable_abs_pow_exp n hb)).const_mul ((2 : ℝ) ^ (n - 1)) using 1
    funext x
    simp only [Pi.add_apply, pow_zero, one_mul]
    ring
  apply hm.mono' (show Continuous (fun x : ℝ =>
    (1 + |x|) ^ n * Real.exp (-b * |x|)) from by fun_prop).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa only [one_pow] using mul_le_mul_of_nonneg_right
      (add_pow_le (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg x) n)
      (Real.exp_pos _).le)

lemma continuous_originalContourPoint : Continuous originalContourPoint := by
  unfold originalContourPoint
  fun_prop

end
end Li2

end
