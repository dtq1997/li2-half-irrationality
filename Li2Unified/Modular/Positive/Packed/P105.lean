module
public import Li2Unified.Modular.Positive.Packed.P073
public import Li2Unified.Modular.Positive.Packed.P104
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option backward.privateInPublic true

@[expose] public section

section
/-! The only external-field discrepancy after scaling and common translation
is the positive ray's half-step. Its logarithmic increment decreases as the
base point moves away from the endpoint. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic Li2Unified.ParameterFamily.Energy

lemma log_increment_antitone {t y δ : ℝ}
    (ht : 0 < t) (hy : 0 ≤ y) (hδ : 0 ≤ δ) :
    Real.log (t + y + δ) - Real.log (t + y) ≤
      Real.log (t + δ) - Real.log t := by
  have hty : 0 < t + y := by linarith
  have htyδ : 0 < t + y + δ := by linarith
  have htδ : 0 < t + δ := by linarith
  have hq : (t + y + δ) / (t + y) ≤ (t + δ) / t := by
    apply (div_le_div_iff₀ hty ht).2
    nlinarith [mul_nonneg hδ hy]
  have hl := Real.log_le_log (div_pos htyδ hty) hq
  rw [Real.log_div htyδ.ne' hty.ne', Real.log_div htδ.ne' ht.ne'] at hl
  exact hl

lemma intervalIntegrable_log_add (a l r : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log (t + a)) volume l r := by
  have h := (intervalIntegral.intervalIntegrable_log'
    (a := l + a) (b := r + a)).comp_add_right a
  simpa [add_comm] using! h

def rayLogIncrement (y δ t : ℝ) : ℝ :=
  Real.log (t + (y + δ)) - Real.log (t + y)

lemma intervalIntegrable_rayLogIncrement (y δ l r : ℝ) :
    IntervalIntegrable (rayLogIncrement y δ) volume l r :=
  (intervalIntegrable_log_add (y + δ) l r).sub
    (intervalIntegrable_log_add y l r)

lemma rayLogIncrement_integral (y δ b : ℝ) :
    (∫ t in (0 : ℝ)..b, rayLogIncrement y δ t) =
      (∫ t in (0 : ℝ)..b, Real.log (t + (y + δ))) -
        (∫ t in (0 : ℝ)..b, Real.log (t + y)) := by
  exact intervalIntegral.integral_sub
    (intervalIntegrable_log_add (y + δ) 0 b)
    (intervalIntegrable_log_add y 0 b)

lemma Vray_shift_eq (y δ : ℝ) :
    Vray (y + δ) - Vray y =
      3 * (∫ t in (0 : ℝ)..1, rayLogIncrement y δ t) -
        (∫ t in (0 : ℝ)..4, rayLogIncrement y δ t) -
          δ * Real.log 2 := by
  rw [rayLogIncrement_integral y δ 1, rayLogIncrement_integral y δ 4]
  unfold Vray baseRay
  ring

lemma rayLogIncrement_nonneg {y δ t : ℝ}
    (ht : 0 < t) (hy : 0 ≤ y) (hδ : 0 ≤ δ) :
    0 ≤ rayLogIncrement y δ t := by
  unfold rayLogIncrement
  apply sub_nonneg.mpr
  exact Real.log_le_log (by linarith) (by linarith)

lemma rayLogIncrement_integral_le {y δ : ℝ}
    (hy : 0 ≤ y) (hδ : 0 ≤ δ) :
    (∫ t in (0 : ℝ)..1, rayLogIncrement y δ t) ≤
      ∫ t in (0 : ℝ)..1, rayLogIncrement 0 δ t := by
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
    (intervalIntegrable_rayLogIncrement y δ 0 1)
    (intervalIntegrable_rayLogIncrement 0 δ 0 1)
  intro t ht
  have hlog := log_increment_antitone ht.1 hy hδ
  simpa only [rayLogIncrement, zero_add, add_zero, add_assoc] using! hlog

lemma Vray_shift_le_integral {y δ : ℝ}
    (hy : 0 ≤ y) (hδ : 0 ≤ δ) :
    Vray (y + δ) - Vray y ≤
      2 * (∫ t in (0 : ℝ)..1, rayLogIncrement 0 δ t) := by
  have htail : 0 ≤ ∫ t in (1 : ℝ)..4, rayLogIncrement y δ t := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    exact rayLogIncrement_nonneg (by linarith [ht.1]) hy hδ
  have hadd :
      (∫ t in (0 : ℝ)..4, rayLogIncrement y δ t) =
        (∫ t in (0 : ℝ)..1, rayLogIncrement y δ t) +
          (∫ t in (1 : ℝ)..4, rayLogIncrement y δ t) := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_rayLogIncrement y δ 0 1)
      (intervalIntegrable_rayLogIncrement y δ 1 4)).symm
  rw [Vray_shift_eq, hadd]
  have hmono := rayLogIncrement_integral_le hy hδ
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg hδ hlog2]

lemma rayLogIncrement_zero_integral (δ : ℝ) :
    (∫ t in (0 : ℝ)..1, rayLogIncrement 0 δ t) =
      (1 + δ) * Real.log (1 + δ) - δ * Real.log δ := by
  rw [rayLogIncrement_integral 0 δ 1]
  have hδ : (∫ t in (0 : ℝ)..1, Real.log (t + (0 + δ))) =
      logPrimitive (1 + δ) - logPrimitive δ := by
    simpa only [zero_add, sub_neg_eq_add] using!
      (Li2Unified.ParameterFamily.Energy.integral_log_shift 0 1 (-δ))
  have h0 : (∫ t in (0 : ℝ)..1, Real.log (t + 0)) =
      logPrimitive 1 - logPrimitive 0 := by
    simpa only [zero_add, add_zero, sub_zero] using!
      (Li2Unified.ParameterFamily.Energy.integral_log_shift 0 1 0)
  rw [hδ, h0]
  simp only [logPrimitive, Real.log_one, mul_zero, Real.log_zero, sub_zero]
  ring

theorem Vray_shift_le {y δ : ℝ} (hy : 0 ≤ y) (hδ : 0 ≤ δ) :
    Vray (y + δ) - Vray y ≤
      2 * ((1 + δ) * Real.log (1 + δ) - δ * Real.log δ) := by
  simpa only [rayLogIncrement_zero_integral] using!
    Vray_shift_le_integral hy hδ

end
end Li2Unified.Proofs.Contour

#print axioms Li2Unified.Proofs.Contour.Vray_shift_le

end

section
namespace Li2Unified.Proofs.Contour
open Li2Unified.Stage0.HalfAnalytic
noncomputable section

lemma ray_shift_entropy_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2 * ((1 + δ) * Real.log (1 + δ) - δ * Real.log δ) ≤
      2 * δ * (2 - Real.log δ) := by
  have hlog : Real.log (1 + δ) ≤ δ := by
    simpa using! Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + δ)
  have hm := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 1 + δ)
  nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ1)]

lemma ray_half_step_error (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy : 0 ≤ y) :
    (n : ℝ) * (Vray (y + 1 / (2 * (n : ℝ))) - Vray y) ≤
      6 * Real.log ((n : ℝ) + 1) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hδ : (0 : ℝ) < 1 / (2 * (n : ℝ)) := by positivity
  have hδ1 : 1 / (2 * (n : ℝ)) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have hbound := mul_le_mul_of_nonneg_left
    ((Vray_shift_le hy hδ.le).trans (ray_shift_entropy_le hδ hδ1)) hn0.le
  have hlogδ : Real.log (1 / (2 * (n : ℝ))) = -Real.log (2 * (n : ℝ)) := by
    rw [one_div, Real.log_inv]
  have hid : (n : ℝ) * (2 * (1 / (2 * (n : ℝ))) *
      (2 - Real.log (1 / (2 * (n : ℝ))))) = 2 + Real.log (2 * (n : ℝ)) := by
    rw [hlogδ]
    field_simp
    ring
  rw [hid] at hbound
  have hlogn : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log ((n : ℝ) + 1) := by
    have hp : 0 < (n : ℝ) + 1 := by positivity
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 * (n : ℝ))
      (show 2 * (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 by nlinarith [sq_nonneg (n : ℝ)])
    simpa only [Real.log_pow, Nat.cast_ofNat] using! h
  have hhalf : (1 / 2 : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ (n : ℝ) + 1 by linarith)
    norm_num at h2
    linarith
  linarith

end
end Li2Unified.Proofs.Contour
#print axioms Li2Unified.Proofs.Contour.ray_half_step_error

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HalfAnalytic
open Li2Unified.Proofs.Contour

/-- The ray half-step costs six more powers of `n+1`; the vertical arms cost none. -/
theorem star_weight_scaled (n : ℕ) (hn : 1 ≤ n)
    (b : Fin 3) (y : ℝ) (hy : 0 ≤ y) :
    (Li2.Sn n : ℝ) * ‖density b ((n:ℝ)*y) *
      Li2.originalComplexQuotient (4*n) ((Li2.D n)^3)
        (point b ((n:ℝ)*y))‖ ≤
      starPartitionWeightConstant * ((n:ℝ)+1)^12 * (1+y)^6 *
        Real.exp ((n:ℝ) * (if b.val=0 then Vray y else Vvertical y)) := by
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have ht : 0 ≤ (n:ℝ)*y := mul_nonneg hn0.le hy
  have h := star_weight_uniform_fixed n hn b ((n:ℝ)*y) ht
  have hratio : 1 + (n:ℝ)*y/(n:ℝ) = 1+y := by field_simp
  have hray : (1/2+(n:ℝ)*y)/(n:ℝ) = y+1/(2*(n:ℝ)) := by
    field_simp
    ring
  have hvert : (n:ℝ)*y/(n:ℝ) = y := by field_simp
  rw [hratio, hray, hvert] at h
  have hC : 0 ≤ starPartitionWeightConstant := starPartitionWeightConstant_pos.le
  by_cases hb : b.val=0
  · simp only [hb, ↓reduceIte] at h ⊢
    have hs := ray_half_step_error n hn y hy
    have he : Real.exp ((n:ℝ)*Vray (y+1/(2*(n:ℝ)))) ≤
        Real.exp ((n:ℝ)*Vray y) * ((n:ℝ)+1)^6 := by
      calc
        _ ≤ Real.exp ((n:ℝ)*Vray y + 6*Real.log ((n:ℝ)+1)) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = _ := by
          rw [Real.exp_add,
            show (6:ℝ)*Real.log ((n:ℝ)+1) = Real.log (((n:ℝ)+1)^6) by
              rw [Real.log_pow]
              ring,
            Real.exp_log (by positivity)]
    calc
      _ ≤ starPartitionWeightConstant * ((n:ℝ)+1)^6 * (1+y)^6 *
          Real.exp ((n:ℝ)*Vray (y+1/(2*(n:ℝ)))) := h
      _ ≤ starPartitionWeightConstant * ((n:ℝ)+1)^6 * (1+y)^6 *
          (Real.exp ((n:ℝ)*Vray y)*((n:ℝ)+1)^6) :=
            mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by ring
  · simp only [hb, ↓reduceIte] at h ⊢
    have hp : ((n:ℝ)+1)^6 ≤ ((n:ℝ)+1)^12 := by
      exact pow_le_pow_right₀ (by linarith) (by norm_num)
    have hrest : 0 ≤ starPartitionWeightConstant * (1+y)^6 *
        Real.exp ((n:ℝ)*Vvertical y) := by positivity
    calc
      _ ≤ starPartitionWeightConstant * ((n:ℝ)+1)^6 * (1+y)^6 *
          Real.exp ((n:ℝ)*Vvertical y) := h
      _ ≤ starPartitionWeightConstant * ((n:ℝ)+1)^12 * (1+y)^6 *
          Real.exp ((n:ℝ)*Vvertical y) := by
            nlinarith only [mul_le_mul_of_nonneg_right hp hrest]

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.star_weight_scaled

end


end
