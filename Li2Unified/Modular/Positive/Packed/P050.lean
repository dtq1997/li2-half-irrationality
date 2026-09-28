module
public import Li2Unified.Modular.Positive.Packed.P036
public import Li2Unified.Modular.Base.RationalPrimeLog
public import Li2Unified.Modular.Base.RationalPolynomialPrimeSupport
public import Li2Unified.Modular.Positive.Packed.P049
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic
public import Li2Unified.Modular.Positive.Packed.P044
public import Li2Unified.Modular.Positive.Packed.P045
public import Li2Unified.Modular.Positive.Packed.P047
public import Li2Unified.Modular.Positive.Packed.P048
public import Li2Unified.Modular.Positive.Packed.P043
public import Li2Unified.Modular.Positive.Packed.P025
public import Li2Unified.Modular.Positive.Packed.P046
public import Li2Unified.Modular.Positive.Packed.P042

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial
open scoped BigOperators

namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily

/-- Every prime of the primitive parameter scale occurs in an actual coefficient. -/
theorem parameter_dtilde_primeSupport_subset (lam : ℚ) {n : ℕ}
    (hn : Qtilde lam n ≠ 0) :
    Li2.ratPrimeSupport (dtilde lam n) ⊆
      Li2.ratPolynomialPrimeSupport (Qtilde lam n) := by
  intro p hp
  obtain ⟨hpprime, hval⟩ :=
    (Li2.mem_ratPrimeSupport_iff (dtilde lam n) p).mp hp
  letI : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨k, _, hv, _⟩ := Qtilde_coeff_valuation_minimum lam p hn
  apply (Li2.mem_ratPolynomialPrimeSupport_iff (Qtilde lam n) p).mpr
  refine ⟨hpprime, k, ?_⟩
  rw [hv]
  exact neg_ne_zero.mpr hval

/-- Exact finite prime-log bridge. The large-prime sign is an explicit input. -/
theorem parameter_log_dtilde_le_neg_prime_range (lam : ℚ) (n cutoff : ℕ)
    (hlarge : ∀ p : ℕ, p.Prime → cutoff < p →
      (padicValRat p (dtilde lam n) : ℚ) ≤ 0) :
    Real.log (dtilde lam n : ℝ) ≤
      -(∑ p ∈ (Finset.range (cutoff+1)).filter Nat.Prime,
        ((-padicValRat p (dtilde lam n) : ℤ) : ℝ) * Real.log (p:ℝ)) := by
  classical
  let S := (Finset.range (cutoff+1)).filter Nat.Prime
  let T := Li2.ratPrimeSupport (dtilde lam n) ∪ S
  have hprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Li2.ratPrimeSupport_prime hp
    · exact (Finset.mem_filter.mp hp).2
  have hlog := Li2.log_rat_eq_sum_padicValRat_of_support_subset
    (dtilde_pos lam n) T Finset.subset_union_left hprime
  have hineq :
      (∑ p ∈ T, (padicValRat p (dtilde lam n) : ℝ) * Real.log (p:ℝ)) ≤
      ∑ p ∈ T,
        if p ∈ S then (padicValRat p (dtilde lam n) : ℝ) * Real.log (p:ℝ)
        else 0 := by
    apply Finset.sum_le_sum
    intro p hp
    by_cases hps : p ∈ S
    · rw [if_pos hps]
    · rw [if_neg hps]
      have hpprime := hprime p hp
      have hpn : cutoff < p := by
        have hnot : ¬p ≤ cutoff := fun h =>
          hps (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h), hpprime⟩)
        omega
      have hv : (padicValRat p (dtilde lam n) : ℝ) ≤ 0 := by
        exact_mod_cast hlarge p hpprime hpn
      have hl : 0 ≤ Real.log (p:ℝ) :=
        Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le)
      exact mul_nonpos_of_nonpos_of_nonneg hv hl
  have hfilter : T.filter (fun p => p ∈ S) = S := by
    ext p
    simp only [T, Finset.mem_filter, Finset.mem_union]
    tauto
  calc
    Real.log (dtilde lam n : ℝ) =
        ∑ p ∈ T, (padicValRat p (dtilde lam n) : ℝ) * Real.log (p:ℝ) := hlog
    _ ≤ ∑ p ∈ T,
          if p ∈ S then (padicValRat p (dtilde lam n) : ℝ) * Real.log (p:ℝ)
          else 0 := hineq
    _ = -(∑ p ∈ S,
          ((-padicValRat p (dtilde lam n) : ℤ) : ℝ) * Real.log (p:ℝ)) := by
      rw [← Finset.sum_filter, hfilter, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p _
      push_cast
      ring

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.parameter_dtilde_primeSupport_subset
#print axioms Li2Unified.Proofs.Arithmetic.parameter_log_dtilde_le_neg_prime_range

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf
open Polynomial
open scoped BigOperators

/-- The exact rational prime-factorization identity, with all primes above
the last pole discarded using the proved sign of their actual valuation. -/
theorem posHalf_log_scale_content_raw (n : ℕ) (hn : 1 ≤ n)
    (hne : Instances.PosHalf.Qtilde n ≠ 0) :
    Real.log (dtilde lambda n : ℝ) ≤
      -(∑ p ∈ (Finset.range (4*n+1)).filter Nat.Prime,
        ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ)*Real.log (p:ℝ)) := by
  apply parameter_log_dtilde_le_neg_prime_range lambda n (4*n)
  intro p hp hpn
  have hraw := posHalf_large_content_raw n p hn hp hpn hne
  have hlog : 0 < Real.log (p:ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hvReal : 0 ≤ ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ) :=
    (mul_nonneg_iff_of_pos_right hlog).mp hraw
  have hvInt : padicValRat p (dtilde lambda n) ≤ 0 := by
    have : 0 ≤ -padicValRat p (dtilde lambda n) := by exact_mod_cast hvReal
    omega
  exact_mod_cast hvInt

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.posHalf_log_scale_content_raw

end

section
/-! Strict rational bounds for the explicit logarithmic expression.
These do not prove that this expression is the content-saving rate, and do
not prove any energy bound F. Those are separate analytic/arithmetic bridges. -/
namespace Li2Unified.ParameterFamily
noncomputable section

theorem log_three_bounds : (1.09861 : ℝ) < Real.log 3 ∧ Real.log 3 < 1.09862 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/3:ℝ)) (by norm_num) 12
  have harg : (1:ℝ)-1/3 = 2/3 := by norm_num
  rw [harg, Real.log_div (by norm_num) (by norm_num)] at h
  norm_num [Finset.sum_range_succ] at h
  have hlo := (abs_le.mp h).1
  have hhi := (abs_le.mp h).2
  have htlo := Real.log_two_gt_d9
  have hthi := Real.log_two_lt_d9
  constructor <;> linarith

/-- Formula (15), with its analytic/content interpretation still separate. -/
def cRatExpression (a b : ℤ) : ℝ :=
  7/2 - 523/840 + (8/3)*Real.log (b:ℝ) -
    8*Real.log |(a:ℝ)| - (9/4)*Real.log |((b-a : ℤ) : ℝ)|

theorem cRatExpression_quarter : (4.1022:ℝ) < cRatExpression 1 4 := by
  have hfour : Real.log (4:ℝ) = 2*Real.log 2 := by
    have h := Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)
    norm_num at h
    linarith
  norm_num [cRatExpression, hfour]
  linarith [Real.log_two_gt_d9, log_three_bounds.2]

theorem cRatExpression_third : (4.2474:ℝ) < cRatExpression 1 3 := by
  norm_num [cRatExpression]
  linarith [log_three_bounds.1, Real.log_two_lt_d9]

theorem cRatExpression_posHalf : (4.7257:ℝ) < cRatExpression 1 2 := by
  norm_num [cRatExpression]
  linarith [Real.log_two_gt_d9]

theorem quarter_margin_of_F_bound (F : ℝ) (hF : F < 1.6743) :
    (2.4279:ℝ) < cRatExpression 1 4 - F := by
  linarith [cRatExpression_quarter]

theorem third_margin_of_F_bound (F : ℝ) (hF : F < 2.6622) :
    (1.5852:ℝ) < cRatExpression 1 3 - F := by
  linarith [cRatExpression_third]

theorem posHalf_margin_of_F_bound (F : ℝ) (hF : F < 4.6457) :
    (0.0800:ℝ) < cRatExpression 1 2 - F := by
  linarith [cRatExpression_posHalf]

end
end Li2Unified.ParameterFamily

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf
open Li2Unified.Stage0.HermitePreparation
open Filter Finset
open scoped BigOperators

/-- The sharp arithmetic rate from the actual parameter Gram theorem. -/
theorem posHalf_arithmetic_rate_actual (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Instances.PosHalf.Qtilde n ≠ 0 →
        Real.log (dtilde lambda n : ℝ) ≤
          -(cRatExpression 1 2-ε)*(n:ℝ)^2 := by
  have hε4 : 0 < ε/4 := by linarith
  have htwo := posHalf_two_adic_content_raw (ε/4) hε4
  have hthree := posHalf_three_adic_content_raw (ε/4) hε4
  have hmedium := posHalf_medium_eventually_actual (ε/4) hε4
  have houter := posHalf_outer_eventually (ε/4) hε4
  filter_upwards [htwo, hthree, hmedium, houter,
    eventually_ge_atTop (4:ℕ)] with n h2 h3 hm ho hn
  intro hne
  let f : ℕ → ℝ := fun p =>
    ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ)*Real.log (p:ℝ)
  have hpart := prime_range_three_interval_partition f n 4 (by omega) (by omega)
  have hmedPart := medium_prime_two_interval_partition f n 4 (by omega) (by omega)
  simp only [Finset.Ioc_self, Finset.sum_empty, zero_add] at hpart hmedPart
  rw [← hmedPart] at hpart
  have h2' := h2 hne
  have h3' := h3 hne
  have hm' := hm hne
  have ho' := ho hne
  have hconst :
      ((8/3:ℝ)*Real.log 2-ε/4) + (-ε/4) +
        ((-523/840:ℝ)-ε/4) + ((7/2:ℝ)-ε/4) =
      cRatExpression 1 2-ε := by
    norm_num [cRatExpression]
    ring
  have hsum : (cRatExpression 1 2-ε)*(n:ℝ)^2 ≤
      ∑ p ∈ (Finset.range (4*n+1)).filter Nat.Prime, f p := by
    rw [hpart]
    dsimp only [f] at h2' h3' hm' ho' ⊢
    rw [← hconst]
    linarith
  have hlog := posHalf_log_scale_content_raw n (by omega) hne
  convert (le_trans hlog (neg_le_neg hsum)) using 1
  ring

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.posHalf_arithmetic_rate_actual

end

section
open Polynomial Filter
open scoped BigOperators
namespace Li2Unified.Stage0.HalfArithmetic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf

def contentTerm (n p : ℕ) : ℝ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ) * Real.log (p:ℝ)
  else 0

theorem hermite_parameter_units (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (lambda ≠ 0 ∧ padicValRat p lambda = 0) ∧
      (1-lambda ≠ 0 ∧ padicValRat p (1-lambda) = 0) := by
  have hp2 : ¬p ∣ 2 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  have hp1 : ¬p ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 1) hd
    omega
  rw [lambda_eq_inverse]
  exact ⟨inverseParameter_unit 2 (by norm_num) hp2,
    inverseParameter_one_sub_unit 2 (by norm_num) hp2 (by simpa using hp1)⟩

theorem two_adic_content :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, Instances.PosHalf.Qtilde n ≠ 0 →
      ((8/3:ℝ)*Real.log 2-ε)*(n:ℝ)^2 ≤ contentTerm n 2 := by
  simpa only [contentTerm, dif_pos Nat.prime_two] using
    Li2Unified.Proofs.Arithmetic.posHalf_two_adic_content_raw

theorem three_adic_good_fallback (n : ℕ) (hn : 1 ≤ n) :
    Li2.GV 3 (Instances.PosHalf.Qtilde n) (-((4*n*Nat.log 3 (7*n-2):ℕ):ℚ)) := by
  exact Li2Unified.Proofs.Arithmetic.posHalf_three_adic_good_fallback n hn

theorem three_adic_content :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, Instances.PosHalf.Qtilde n ≠ 0 →
      -ε*(n:ℝ)^2 ≤ contentTerm n 3 := by
  simpa only [contentTerm, dif_pos (by decide : Nat.Prime 3)] using
    Li2Unified.Proofs.Arithmetic.posHalf_three_adic_content_raw

/-- Fixed epsilon away from zero first; small primes use the full log fallback. -/
theorem medium_prime_PNT :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, Instances.PosHalf.Qtilde n ≠ 0 →
      ((-523/840:ℝ)-ε)*(n:ℝ)^2 ≤
        ∑ p ∈ (Finset.range (n+1)).filter (fun p => p.Prime ∧ 5 ≤ p), contentTerm n p := by
  intro ε hε
  filter_upwards [Li2Unified.Proofs.Arithmetic.posHalf_medium_eventually_actual ε hε]
    with n hn
  intro hne
  convert hn hne using 1
  apply Finset.sum_congr rfl
  intro p hp
  simp only [contentTerm, dif_pos (Finset.mem_filter.mp hp).2.1]

theorem outer_prime_content :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, Instances.PosHalf.Qtilde n ≠ 0 →
      ((7/2:ℝ)-ε)*(n:ℝ)^2 ≤
        ∑ p ∈ (Finset.range (4*n+1)).filter (fun p => p.Prime ∧ n < p), contentTerm n p := by
  intro ε hε
  filter_upwards [Li2Unified.Proofs.Arithmetic.posHalf_outer_eventually ε hε] with n hn
  intro hne
  have he : (∑ p ∈ (Finset.range (4*n+1)).filter (fun p => p.Prime ∧ n < p), contentTerm n p) =
      ∑ p ∈ Finset.Ioc n (4*n), if p.Prime then
        ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ)*Real.log (p:ℝ) else 0 := by
    have hs : (Finset.range (4*n+1)).filter (fun p => p.Prime ∧ n < p) =
        (Finset.Ioc n (4*n)).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ioc,Nat.lt_succ_iff]
      tauto
    rw [hs,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h : p.Prime <;> simp [contentTerm,h]
  rw [he]
  exact hn hne

theorem beyond_pole_support (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime)
    (hpn : 4*n < p) (hne : Instances.PosHalf.Qtilde n ≠ 0) : 0 ≤ contentTerm n p := by
  simpa only [contentTerm, dif_pos hp] using
    Li2Unified.Proofs.Arithmetic.posHalf_large_content_raw n p hn hp hpn hne

theorem log_scale_content (n : ℕ) (hn : 1 ≤ n) (hne : Instances.PosHalf.Qtilde n ≠ 0) :
    Real.log (dtilde lambda n : ℝ) ≤
      -(∑ p ∈ (Finset.range (4*n+1)).filter Nat.Prime, contentTerm n p) := by
  have he : (∑ p ∈ (Finset.range (4*n+1)).filter Nat.Prime, contentTerm n p) =
      ∑ p ∈ (Finset.range (4*n+1)).filter Nat.Prime,
        ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ)*Real.log (p:ℝ) := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [contentTerm, dif_pos (Finset.mem_filter.mp hp).2]
  rw [he]
  exact Li2Unified.Proofs.Arithmetic.posHalf_log_scale_content_raw n hn hne

theorem arithmetic_rate :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, Instances.PosHalf.Qtilde n ≠ 0 →
      Real.log (dtilde lambda n : ℝ) ≤
        -(cRatExpression 1 2-ε)*(n:ℝ)^2 := by
  exact Li2Unified.Proofs.Arithmetic.posHalf_arithmetic_rate_actual

theorem arithmetic_eventually :
    ∀ᶠ n : ℕ in atTop, Instances.PosHalf.Qtilde n ≠ 0 →
      (dtilde lambda n : ℝ) ≤ Real.exp (-(47/10:ℝ)*(n:ℝ)^2) := by
  have hgap : (0:ℝ) < cRatExpression 1 2 - 47/10 := by
    linarith [cRatExpression_posHalf]
  filter_upwards [arithmetic_rate (cRatExpression 1 2 - 47/10) hgap] with n hn
  intro hne
  have hlog := hn hne
  have hd : (0:ℝ) < (dtilde lambda n : ℝ) := by
    exact_mod_cast dtilde_pos lambda n
  rw [← Real.exp_log hd]
  apply Real.exp_le_exp.mpr
  convert hlog using 1 <;> ring

end
end Li2Unified.Stage0.HalfArithmetic

#print axioms Li2Unified.Stage0.HalfArithmetic.medium_prime_PNT
#print axioms Li2Unified.Stage0.HalfArithmetic.arithmetic_rate

end


end
