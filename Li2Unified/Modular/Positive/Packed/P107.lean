module
public import Li2Unified.Modular.Positive.Packed.P106
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Real.Pi.Bounds

set_option backward.privateInPublic true

@[expose] public section

section
/-! Rational log endpoint enclosures and the singularity bound used
by the quarter certificate. Normalization is an explicit checked equality;
these declarations do not validate the final certificate or any measure. -/
open Finset Set
namespace Li2Unified.ParameterFamily
noncomputable section

def logPartial (r : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ range n, (1-r)^(i+1) / ((i+1:ℕ):ℚ)

def logError (r : ℚ) (n : ℕ) : ℚ := (1-r)^(n+1)/r

def reducedLogBounds (r : ℚ) (n : ℕ) : RationalBounds :=
  ⟨-logPartial r n-logError r n,-logPartial r n+logError r n⟩

def logTwoBounds : RationalBounds :=
  ⟨6931471803/10^10,6931471808/10^10⟩

theorem contains_logTwo : logTwoBounds.Contains (Real.log 2) := by
  convert And.intro (Real.log_two_gt_d9).le (Real.log_two_lt_d9).le using 1 <;>
    norm_num [RationalBounds.Contains, logTwoBounds]

theorem contains_reduced_log (r : ℚ) (hr : 0 < r) (h1 : r ≤ 1) (n : ℕ) :
    (reducedLogBounds r n).Contains (Real.log (r:ℝ)) := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have h1' : (r:ℝ) ≤ 1 := by exact_mod_cast h1
  have hx : |1-(r:ℝ)| < 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx n
  have he : (1:ℝ)-(1-r) = r := by ring
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1-r), he] at h
  have hs : |(logPartial r n:ℝ)+Real.log (r:ℝ)| ≤ (logError r n:ℝ) := by
    simpa only [logPartial, logError, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
      Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_add, Nat.cast_one] using! h
  change ((-logPartial r n-logError r n:ℚ):ℝ) ≤ Real.log (r:ℝ) ∧
    Real.log (r:ℝ) ≤ ((-logPartial r n+logError r n:ℚ):ℝ)
  push_cast
  constructor <;> linarith [(abs_le.mp hs).1, (abs_le.mp hs).2]

def scaledLogBounds (k : ℤ) (r : ℚ) (n : ℕ) : RationalBounds :=
  RationalBounds.add
    (RationalBounds.mul (RationalBounds.point (k:ℚ)) logTwoBounds)
    (reducedLogBounds r n)

theorem contains_scaled_log (q r : ℚ) (k : ℤ) (n : ℕ)
    (hr : 0 < r) (h1 : r ≤ 1) (hq : q = (2:ℚ)^k*r) :
    (scaledLogBounds k r n).Contains (Real.log (q:ℝ)) := by
  have hq' : (q:ℝ) = (2:ℝ)^k*(r:ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat] using!
      congrArg (fun z : ℚ => (z : ℝ)) hq
  have hr' : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [hq', Real.log_mul (zpow_ne_zero k (by norm_num : (2:ℝ) ≠ 0)) hr',
    Real.log_zpow]
  simpa only [scaledLogBounds, Rat.cast_intCast] using!
    RationalBounds.contains_add
      (RationalBounds.contains_mul (RationalBounds.contains_point (k:ℚ)) contains_logTwo)
      (contains_reduced_log r hr h1 n)

theorem mul_log_antitone_quarter :
    AntitoneOn (fun x : ℝ => x*Real.log x) (Icc 0 (1/4)) := by
  have hquarter : Real.log (1/4:ℝ) = -2*Real.log 2 := by
    have h := Real.log_zpow (2:ℝ) (-2)
    norm_num at h
    linarith
  apply antitoneOn_of_deriv_nonpos (convex_Icc (0:ℝ) (1/4))
    (Real.continuous_mul_log).continuousOn
  · intro x hx
    have hx' : (0:ℝ) < x ∧ x < 1/4 := by simpa only [interior_Icc, Set.mem_Ioo] using! hx
    exact (Real.hasDerivAt_mul_log hx'.1.ne').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : (0:ℝ) < x ∧ x < 1/4 := by simpa only [interior_Icc, Set.mem_Ioo] using! hx
    rw [Real.deriv_mul_log hx'.1.ne']
    have hle := Real.log_le_log hx'.1 hx'.2.le
    linarith [Real.log_two_gt_d9]

theorem abs_mul_log_le_radius (x r : ℝ) (hx : |x| ≤ r) (hr : r ≤ 1/4) :
    |x*Real.log x| ≤ -r*Real.log r := by
  have hr0 : 0 ≤ r := (abs_nonneg x).trans hx
  have ha : |x| ≤ (1:ℝ) := by linarith
  have hlog : Real.log x ≤ 0 := by
    rw [← Real.log_abs]
    exact Real.log_nonpos (abs_nonneg x) ha
  have hm := mul_log_antitone_quarter ⟨abs_nonneg x,hx.trans hr⟩ ⟨hr0,hr⟩ hx
  change r * Real.log r ≤ |x| * Real.log |x| at hm
  rw [Real.log_abs] at hm
  rw [abs_mul, abs_of_nonpos hlog]
  nlinarith

end
end Li2Unified.ParameterFamily

end

section
open Set
namespace Li2Unified.Proofs.Potential
noncomputable section
open Li2Unified.ParameterFamily

lemma log_tangent_upper (x a : ℝ) (hx : 0 < x) (ha : 0 < a) :
    Real.log x ≤ Real.log a+(x-a)/a := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx ha)
  rw [Real.log_div hx.ne' ha.ne'] at h
  have he : (x-a)/a = x/a-1 := by field_simp
  rw [he]
  linarith

lemma log_twenty_upper : Real.log (20:ℝ) ≤ 3 := by
  have h := (contains_scaled_log 20 (5/8) 5 12 (by norm_num) (by norm_num)
    (by norm_num)).2
  norm_num [scaledLogBounds, RationalBounds.add, RationalBounds.mul,
    RationalBounds.point, logTwoBounds, reducedLogBounds, logPartial, logError,
    Finset.sum_range_succ] at h
  linarith

lemma log_sixty_six_fifths_upper : Real.log (66/5:ℝ) ≤ 13/5 := by
  have h := (contains_scaled_log (66/5) (33/40) 4 8 (by norm_num) (by norm_num)
    (by norm_num)).2
  norm_num [scaledLogBounds, RationalBounds.add, RationalBounds.mul,
    RationalBounds.point, logTwoBounds, reducedLogBounds, logPartial, logError,
    Finset.sum_range_succ] at h
  linarith

lemma ray_tail_scalar (x : ℝ) (hx : 18 ≤ x) :
    4*Real.log 4-1-Real.log x-x*Real.log 2+4*Real.log (x+2/25) ≤ 19/10 := by
  have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    convert Real.log_pow (2:ℝ) 2 using 1 <;> norm_num
  have h16 : Real.log (16:ℝ) = 4*Real.log 2 := by
    convert Real.log_pow (2:ℝ) 4 using 1 <;> norm_num
  have hxmin := Real.log_le_log (by norm_num : (0:ℝ)<16) (show (16:ℝ) ≤ x by linarith)
  rw [h16] at hxmin
  have htan := log_tangent_upper (x+2/25) 20 (by linarith) (by norm_num)
  have hlog2 := Real.log_two_gt_d9
  have hp := mul_nonneg (show 0 ≤ x-18 by linarith)
    (show 0 ≤ Real.log 2-1/5 by linarith)
  rw [h4]
  nlinarith [log_twenty_upper]

lemma vertical_tail_scalar (y : ℝ) (hy : 2 ≤ y) :
    4*Real.log 4-1-Real.log y-2*Real.pi*y+4*Real.log (56/5+y) ≤ 19/10 := by
  have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    convert Real.log_pow (2:ℝ) 2 using 1 <;> norm_num
  have hymin := Real.log_le_log (by norm_num : (0:ℝ)<2) hy
  have htan := log_tangent_upper (56/5+y) (66/5) (by linarith) (by norm_num)
  have hlog2 := Real.log_two_lt_d9
  have hpi := Real.pi_gt_d2
  have hp := mul_nonneg (show 0 ≤ y-2 by linarith)
    (show 0 ≤ 2*Real.pi-10/33 by linarith)
  rw [h4]
  nlinarith [log_sixty_six_fifths_upper]

end
end Li2Unified.Proofs.Potential
#print axioms Li2Unified.Proofs.Potential.ray_tail_scalar
#print axioms Li2Unified.Proofs.Potential.vertical_tail_scalar

end

section
namespace Li2Unified.Proofs.Potential
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

theorem actual_ray_tail (x : ℝ) (hx : 18 ≤ x) : psiRay x ≤ 19/10 := by
  have hb := baseRay_tail_upper x (by linarith)
  have hp := comparisonPotential_ray_tail x hx
  have hs := ray_tail_scalar x hx
  unfold psiRay Vray
  linarith

theorem actual_up_tail (y : ℝ) (hy : 2 ≤ y) : psiUp y ≤ 19/10 := by
  have hb := baseVertical_tail_upper y (by linarith)
  have hp := comparisonPotential_vertical_tail y hy
  have hs := vertical_tail_scalar y hy
  unfold psiUp Vvertical
  rw [abs_of_nonneg (show 0 ≤ y by linarith)]
  linarith

end
end Li2Unified.Proofs.Potential
#print axioms Li2Unified.Proofs.Potential.actual_ray_tail
#print axioms Li2Unified.Proofs.Potential.actual_up_tail

end


end
