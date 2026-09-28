module
public import Li2Unified.Modular.Positive.Packed.P100
public import Li2Unified.Modular.Positive.Packed.P103
public import Li2Unified.Modular.Base.OriginalFnLogBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

set_option backward.privateInPublic true

@[expose] public section

section
/-! The literal three-arm weight bound used by the frozen half-analytic stage. -/

open Polynomial MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

theorem actual_weight_uniform :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ b : Fin 3, ∀ t : ℝ, 0 ≤ t →
        (Li2.Sn n : ℝ) * ‖density b t *
          Li2.originalComplexQuotient (4 * n) ((Li2.D n) ^ 3) (point b t)‖ ≤
        C * (n + 1 : ℝ) ^ K * (1 + t / (n : ℝ)) ^ K *
          Real.exp ((n : ℝ) *
            (if b.val = 0 then Vray ((1 / 2 + t) / (n : ℝ))
             else Vvertical (t / (n : ℝ)))) := by
  refine ⟨rayWeightConstant + verticalWeightConstant, 6, ?_, ?_⟩
  · unfold rayWeightConstant verticalWeightConstant
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  intro n hn b t ht
  fin_cases b
  · have h := ray_density_uniform_bound n hn t ht
    have hc : rayWeightConstant ≤ rayWeightConstant + verticalWeightConstant := by
      have hv : 0 ≤ verticalWeightConstant := by
        unfold verticalWeightConstant
        positivity
      linarith
    have hp : 0 ≤ ((n : ℝ) + 1) ^ 6 *
        (1 + t / (n : ℝ)) ^ 6 *
        Real.exp ((n : ℝ) * Vray ((1 / 2 + t) / (n : ℝ))) := by positivity
    have h' := mul_le_mul_of_nonneg_right hc hp
    simpa only [Fin.val_zero, ↓reduceIte, mul_assoc] using h.trans (by
      simpa only [mul_assoc] using h')
  · have h := up_density_uniform_bound n hn t ht
    have hc : verticalWeightConstant ≤ rayWeightConstant + verticalWeightConstant := by
      have hr : 0 ≤ rayWeightConstant := by
        unfold rayWeightConstant
        have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        positivity
      linarith
    have hp : 0 ≤ ((n : ℝ) + 1) ^ 6 *
        (1 + t / (n : ℝ)) ^ 6 *
        Real.exp ((n : ℝ) * Vvertical (t / (n : ℝ))) := by positivity
    have h' := mul_le_mul_of_nonneg_right hc hp
    simpa only [Fin.val_one, one_ne_zero, ↓reduceIte, mul_assoc] using h.trans (by
      simpa only [mul_assoc] using h')
  · have h := down_density_uniform_bound n hn t ht
    have hc : verticalWeightConstant ≤ rayWeightConstant + verticalWeightConstant := by
      have hr : 0 ≤ rayWeightConstant := by
        unfold rayWeightConstant
        have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        positivity
      linarith
    have hp : 0 ≤ ((n : ℝ) + 1) ^ 6 *
        (1 + t / (n : ℝ)) ^ 6 *
        Real.exp ((n : ℝ) * Vvertical (t / (n : ℝ))) := by positivity
    have h' := mul_le_mul_of_nonneg_right hc hp
    simpa only [Fin.val_two, Nat.reduceEqDiff, ↓reduceIte, mul_assoc] using h.trans (by
      simpa only [mul_assoc] using h')

end
end Li2Unified.Proofs.Contour

end

section
namespace Li2Unified.Proofs.Arithmetic
open Li2 Li2Unified.Proofs.Contour Filter Topology
noncomputable section

def starPartitionWeightConstant : ℝ := rayWeightConstant + verticalWeightConstant

lemma starPartitionWeightConstant_pos : 0 < starPartitionWeightConstant := by
  unfold starPartitionWeightConstant rayWeightConstant verticalWeightConstant
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- Prefactor after all `Sn` factors are absorbed into the densities.
The factor `1/(2n)! ≤ 1` may be dropped for an upper bound. -/
def starPartitionPrefactor (n : ℕ) : ℝ :=
  ((n : ℝ) ^ ((2 * n) ^ 2) / (Fn n : ℝ)) *
    starPartitionWeightConstant ^ (2 * n) * ((n : ℝ) + 1) ^ (6 * (2 * n))

def starPartitionErrorConstant : ℝ :=
  32 + 4 * |Real.log starPartitionWeightConstant|

lemma starPartitionPrefactor_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < starPartitionPrefactor n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hF : 0 < (Fn n : ℝ) := by exact_mod_cast Fn_pos n
  have hC := starPartitionWeightConstant_pos
  unfold starPartitionPrefactor
  positivity

lemma starPartitionErrorConstant_pos : 0 < starPartitionErrorConstant := by
  unfold starPartitionErrorConstant
  positivity

lemma starPartitionPrefactor_log (n : ℕ) (hn : 1 ≤ n) :
    Real.log (starPartitionPrefactor n) =
      4 * (n : ℝ) ^ 2 * Real.log (n : ℝ) - Real.log (Fn n : ℝ) +
      2 * (n : ℝ) * Real.log starPartitionWeightConstant +
      12 * (n : ℝ) * Real.log ((n : ℝ) + 1) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hF : 0 < (Fn n : ℝ) := by exact_mod_cast Fn_pos n
  have hC := starPartitionWeightConstant_pos
  have hp : 0 < (n : ℝ) + 1 := by positivity
  unfold starPartitionPrefactor
  rw [Real.log_mul (mul_ne_zero (div_ne_zero (pow_ne_zero _ hnR.ne') hF.ne')
        (pow_ne_zero _ hC.ne')) (pow_ne_zero _ hp.ne'),
      Real.log_mul (div_ne_zero (pow_ne_zero _ hnR.ne') hF.ne') (pow_ne_zero _ hC.ne'),
      Real.log_div (pow_ne_zero _ hnR.ne') hF.ne', Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- All-n explicit logarithmic prefactor error; no partition integral estimate is assumed. -/
theorem starPartitionPrefactor_log_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (starPartitionPrefactor n) ≤
      (6 - 4 * Real.log 2) * (n : ℝ) ^ 2 +
        starPartitionErrorConstant * (n : ℝ) * Real.log ((n : ℝ) + 1) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogn : Real.log 2 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by linarith only [hnR])
  have hhalf : (1 / 2 : ℝ) ≤ Real.log ((n : ℝ) + 1) := hlogtwo.trans hlogn
  have hFn := (abs_le.mp (originalFn_log_error_bound n hn)).1
  have hC : 2 * (n : ℝ) * Real.log starPartitionWeightConstant ≤
      4 * |Real.log starPartitionWeightConstant| * (n : ℝ) * Real.log ((n : ℝ) + 1) := by
    have hc := le_abs_self (Real.log starPartitionWeightConstant)
    have ha := abs_nonneg (Real.log starPartitionWeightConstant)
    have h1 := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hhalf
      (by positivity : (0 : ℝ) ≤ 4 * |Real.log starPartitionWeightConstant| * (n : ℝ))
    nlinarith only [h1, h2]
  rw [starPartitionPrefactor_log n hn]
  unfold starPartitionErrorConstant
  nlinarith only [hFn, hC]

theorem starPartitionPrefactor_le_exp (n : ℕ) (hn : 1 ≤ n) :
    starPartitionPrefactor n ≤
      Real.exp ((6 - 4 * Real.log 2) * (n : ℝ) ^ 2 +
        starPartitionErrorConstant * (n : ℝ) * Real.log ((n : ℝ) + 1)) := by
  have h := Real.exp_le_exp.mpr (starPartitionPrefactor_log_le n hn)
  simpa only [Real.exp_log (starPartitionPrefactor_pos n hn)] using h

theorem star_n_log_eventually_le_square (K : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, K * (n : ℝ) * Real.log ((n : ℝ) + 1) ≤ δ * (n : ℝ) ^ 2 := by
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hshift
  have hK : Tendsto (fun n : ℕ => K * (Real.log ((n : ℝ) + 1) / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlog.const_mul K
  have herr : ∀ᶠ n : ℕ in atTop, K * (Real.log ((n : ℝ) + 1) / (n : ℝ)) ≤ δ :=
    Filter.Tendsto.eventually_le_const hδ hK
  filter_upwards [herr, eventually_ge_atTop (1 : ℕ)] with n hnerr hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlinear : K * Real.log ((n : ℝ) + 1) ≤ δ * (n : ℝ) :=
    (div_le_iff₀ hnpos).mp (by simpa only [mul_div_assoc] using hnerr)
  calc
    K * (n : ℝ) * Real.log ((n : ℝ) + 1) = (K * Real.log ((n : ℝ) + 1)) * (n : ℝ) := by ring
    _ ≤ (δ * (n : ℝ)) * (n : ℝ) := mul_le_mul_of_nonneg_right hlinear hnpos.le
    _ = δ * (n : ℝ) ^ 2 := by ring

theorem starPartitionPrefactor_eventually_le_exp (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, starPartitionPrefactor n ≤
      Real.exp ((6-4*Real.log 2+δ)*(n:ℝ)^2) := by
  filter_upwards [star_n_log_eventually_le_square starPartitionErrorConstant hδ,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  apply (starPartitionPrefactor_le_exp n hn1).trans
  apply Real.exp_le_exp.mpr
  nlinarith only [hn]

end
end Li2Unified.Proofs.Arithmetic

end

section
open Polynomial MeasureTheory Set
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HalfAnalytic
open Li2Unified.Proofs.Contour

/-- The explicit witness of the already proved three-arm uniform weight theorem. -/
theorem star_weight_uniform_fixed (n : ℕ) (hn : 1 ≤ n)
    (b : Fin 3) (t : ℝ) (ht : 0 ≤ t) :
    (Li2.Sn n : ℝ) * ‖density b t *
      Li2.originalComplexQuotient (4*n) ((Li2.D n)^3) (point b t)‖ ≤
      starPartitionWeightConstant * ((n:ℝ)+1)^6 *
        (1+t/(n:ℝ))^6 *
        Real.exp ((n:ℝ) *
          (if b.val=0 then Vray ((1/2+t)/(n:ℝ))
           else Vvertical (t/(n:ℝ)))) := by
  -- Reapply the three proved arm inequalities to retain the literal constants.
  fin_cases b
  · have h := ray_density_uniform_bound n hn t ht
    have hc : rayWeightConstant ≤ starPartitionWeightConstant := by
      unfold starPartitionWeightConstant
      have hv : 0 ≤ verticalWeightConstant := by
        unfold verticalWeightConstant
        positivity
      linarith
    have hp : 0 ≤ ((n:ℝ)+1)^6 * (1+t/(n:ℝ))^6 *
        Real.exp ((n:ℝ)*Vray ((1/2+t)/(n:ℝ))) := by positivity
    have h' := mul_le_mul_of_nonneg_right hc hp
    simpa only [Fin.val_zero, ↓reduceIte, mul_assoc] using h.trans (by
      simpa only [mul_assoc] using h')
  · have h := up_density_uniform_bound n hn t ht
    have hc : verticalWeightConstant ≤ starPartitionWeightConstant := by
      unfold starPartitionWeightConstant
      have hr : 0 ≤ rayWeightConstant := by
        unfold rayWeightConstant
        have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        positivity
      linarith
    have hp : 0 ≤ ((n:ℝ)+1)^6 * (1+t/(n:ℝ))^6 *
        Real.exp ((n:ℝ)*Vvertical (t/(n:ℝ))) := by positivity
    have h' := mul_le_mul_of_nonneg_right hc hp
    simpa only [Fin.val_one, one_ne_zero, ↓reduceIte, mul_assoc] using h.trans (by
      simpa only [mul_assoc] using h')
  · have h := down_density_uniform_bound n hn t ht
    have hc : verticalWeightConstant ≤ starPartitionWeightConstant := by
      unfold starPartitionWeightConstant
      have hr : 0 ≤ rayWeightConstant := by
        unfold rayWeightConstant
        have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        positivity
      linarith
    have hp : 0 ≤ ((n:ℝ)+1)^6 * (1+t/(n:ℝ))^6 *
        Real.exp ((n:ℝ)*Vvertical (t/(n:ℝ))) := by positivity
    have h' := mul_le_mul_of_nonneg_right hc hp
    simpa only [Fin.val_two, Nat.reduceEqDiff, ↓reduceIte, mul_assoc] using h.trans (by
      simpa only [mul_assoc] using h')

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.star_weight_uniform_fixed

end

section
/-! Exact oriented real line-cell logarithmic integrals, including
intervals crossing zero. These are iterated interval integrals; transfer to
product measures and perpendicular cells is a separate obligation. -/
open MeasureTheory Set
namespace Li2Unified.ParameterFamily.Energy
noncomputable section

def logPrimitive (x : ℝ) : ℝ := x*Real.log x-x

def logSecondPrimitive (x : ℝ) : ℝ :=
  x*(x*Real.log x)/2-3*x^2/4

lemma continuous_logPrimitive : Continuous logPrimitive :=
  Real.continuous_mul_log.sub continuous_id

lemma continuous_logSecondPrimitive : Continuous logSecondPrimitive :=
  ((continuous_id.mul Real.continuous_mul_log).div_const 2).sub
    ((continuous_const.mul (continuous_id.pow 2)).div_const 4)

lemma hasDerivAt_logSecondPrimitive (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt logSecondPrimitive (logPrimitive x) x := by
  have h := (((hasDerivAt_id x).mul (Real.hasDerivAt_mul_log hx)).div_const 2).sub
    ((((hasDerivAt_id x).pow 2).const_mul 3).div_const 4)
  convert h using 1 <;> simp only [logPrimitive, logSecondPrimitive, id_eq] <;> ring

lemma integral_logPrimitive_from_zero (b : ℝ) :
    (∫ x in (0:ℝ)..b, logPrimitive x) = logSecondPrimitive b := by
  by_cases hb : 0 ≤ b
  · have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb
      continuous_logSecondPrimitive.continuousOn
      (fun x hx => hasDerivAt_logSecondPrimitive x hx.1.ne')
      (continuous_logPrimitive.intervalIntegrable 0 b)
    simpa [logSecondPrimitive] using h
  · have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_not_ge hb)
      continuous_logSecondPrimitive.continuousOn
      (fun x hx => hasDerivAt_logSecondPrimitive x hx.2.ne)
      (continuous_logPrimitive.intervalIntegrable b 0)
    rw [intervalIntegral.integral_symm]
    simpa [logSecondPrimitive] using congrArg Neg.neg h

lemma integral_logPrimitive (a b : ℝ) :
    (∫ x in a..b, logPrimitive x) = logSecondPrimitive b-logSecondPrimitive a := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (continuous_logPrimitive.intervalIntegrable a 0) (continuous_logPrimitive.intervalIntegrable 0 b)]
  rw [intervalIntegral.integral_symm (a := 0) (b := a),
    integral_logPrimitive_from_zero, integral_logPrimitive_from_zero]
  ring

lemma integral_log_shift (a b w : ℝ) :
    (∫ x in a..b, Real.log (x-w)) = logPrimitive (b-w)-logPrimitive (a-w) := by
  rw [intervalIntegral.integral_comp_sub_right, integral_log]
  simp only [logPrimitive]
  ring

lemma integral_integral_log_sub (a b c d : ℝ) :
    (∫ y in c..d, ∫ x in a..b, Real.log (x-y)) =
      logSecondPrimitive (b-c)-logSecondPrimitive (b-d)-
        logSecondPrimitive (a-c)+logSecondPrimitive (a-d) := by
  simp_rw [integral_log_shift]
  have hb : Continuous (fun y : ℝ => logPrimitive (b-y)) :=
    continuous_logPrimitive.comp (continuous_const.sub continuous_id)
  have ha : Continuous (fun y : ℝ => logPrimitive (a-y)) :=
    continuous_logPrimitive.comp (continuous_const.sub continuous_id)
  rw [intervalIntegral.integral_sub (hb.intervalIntegrable c d) (ha.intervalIntegrable c d),
    intervalIntegral.integral_comp_sub_left, intervalIntegral.integral_comp_sub_left,
    integral_logPrimitive, integral_logPrimitive]
  ring

end
end Li2Unified.ParameterFamily.Energy

end


end
