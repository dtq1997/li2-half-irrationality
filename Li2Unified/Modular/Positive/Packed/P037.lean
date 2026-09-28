module
public import Li2Unified.Modular.Positive.Packed.P025
public import Li2Unified.Modular.Positive.Packed.P036
public import Li2Unified.Modular.Base.RationalPrimeLog
public import Mathlib.Algebra.Order.Floor.Semifield

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial
open scoped BigOperators

namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Stage0.HermitePreparation

/-- Transfer the original normalized Hermite matrix estimate to the primitive scale.
The matrix estimate is explicit because its Stage0 proof is a separate obligation. -/
theorem parameter_dtilde_medium_lower (lam : ℚ) (n p : ℕ) [Fact p.Prime]
    (hne : Qtilde lam n ≠ 0)
    (hgram : Li2.GV p (binomGram lam n).det (normalizedDetLower n p)) :
    normalizedDetLower n p ≤ (-padicValRat p (dtilde lam n) : ℚ) := by
  obtain ⟨k, hk0, hkval, _⟩ := Qtilde_coeff_valuation_minimum lam p hne
  have hcoeff := hgram k
  rw [← Qtilde_eq_binomGram_det] at hcoeff
  rcases hcoeff with hzero | hbound
  · exact (hk0 hzero).elim
  · rw [hkval] at hbound
    exact hbound

/-- A literal weighted prime contribution from the actual normalized determinant. -/
theorem parameter_dtilde_medium_weighted (lam : ℚ) (n p : ℕ) [Fact p.Prime]
    (hne : Qtilde lam n ≠ 0)
    (hgram : Li2.GV p (binomGram lam n).det (normalizedDetLower n p)) :
    (normalizedDetLower n p : ℝ) * Real.log (p:ℝ) ≤
      ((-padicValRat p (dtilde lam n) : ℤ) : ℝ) * Real.log (p:ℝ) := by
  have hv : (normalizedDetLower n p : ℝ) ≤
      ((-padicValRat p (dtilde lam n) : ℤ) : ℝ) := by
    exact_mod_cast parameter_dtilde_medium_lower lam n p hne hgram
  have hp : p.Prime := Fact.out
  have hl : 0 ≤ Real.log (p:ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  exact mul_le_mul_of_nonneg_right hv hl

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.parameter_dtilde_medium_lower
#print axioms Li2Unified.Proofs.Arithmetic.parameter_dtilde_medium_weighted

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation

/-- The floor in the analytic profile is the exact integer quotient used by Hermite. -/
private theorem floor_scaled_ratio (c n p : ℕ) (hn : 0 < n) (hp : 0 < p) :
    (⌊(c:ℝ) / ((p:ℝ)/(n:ℝ))⌋ : ℝ) = ((c*n/p : ℕ) : ℝ) := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpR : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hratio : (c:ℝ) / ((p:ℝ)/(n:ℝ)) = ((c*n:ℕ):ℝ)/(p:ℝ) := by
    field_simp [hnR, hpR]
    push_cast
    ring
  rw [hratio]
  rw [Int.floor_div_natCast, Int.floor_natCast]
  have hint : ((c:ℤ)*(n:ℤ))/(p:ℤ) = ((c*n/p:ℕ):ℤ) := by
    rw [← Int.natCast_mul]
    exact (Int.natCast_div (c*n) p).symm
  exact congrArg (fun z : ℤ => (z:ℝ)) hint

/-- Exact discrete/continuous profile identity; the residual L-2A is O(n/p). -/
theorem normalizedDetLower_eq_profile (n p : ℕ) (hn : 0 < n) (hp : 0 < p) :
    (normalizedDetLower n p : ℝ) =
      (n:ℝ) * profile ((p:ℝ)/(n:ℝ)) +
      (((4*n)/p:ℕ):ℝ) - 2*((n/p:ℕ):ℝ) := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpR : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hn0 : (0:ℝ) ≤ n := by positivity
  have hA : (⌊(1:ℝ) / ((p:ℝ)/(n:ℝ))⌋ : ℝ) = ((n/p:ℕ):ℝ) := by
    have h := floor_scaled_ratio 1 n p hn hp
    norm_num only [Nat.cast_one, one_mul] at h
    exact h
  have hL : (⌊(4:ℝ) / ((p:ℝ)/(n:ℝ))⌋ : ℝ) = (((4*n)/p:ℕ):ℝ) :=
    floor_scaled_ratio 4 n p hn hp
  have hB : (⌊(2:ℝ) / ((p:ℝ)/(n:ℝ))⌋ : ℝ) = (((2*n)/p:ℕ):ℝ) :=
    floor_scaled_ratio 2 n p hn hp
  have hmin :
      (n:ℝ) * min (1 - ((n/p:ℕ):ℝ) * ((p:ℝ)/(n:ℝ)))
        (4 - (((4*n)/p:ℕ):ℝ) * ((p:ℝ)/(n:ℝ))) =
      min ((n:ℝ) - ((n/p:ℕ):ℝ) * (p:ℝ))
        (4*(n:ℝ) - (((4*n)/p:ℕ):ℝ) * (p:ℝ)) := by
    rw [mul_min_of_nonneg _ _ hn0]
    congr 1 <;> field_simp [hnR]
  dsimp [normalizedDetLower, profile]
  rw [hA, hL, hB]
  push_cast
  rw [← hmin]
  field_simp [hnR, hpR]

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.normalizedDetLower_eq_profile

end

end
