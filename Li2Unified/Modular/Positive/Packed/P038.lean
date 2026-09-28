module
public import Li2Unified.Modular.Positive.Packed.P037
public import Li2Unified.Modular.Positive.Packed.P035
public import Li2Unified.Modular.Positive.Packed.P025

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation

/-- The discrete normalized determinant estimate dominates its continuous
profile; the exact residual is L-2A and is nonnegative. -/
theorem normalizedDetLower_ge_profile (n p : ℕ)
    (hn : 0 < n) (hp : 0 < p) :
    (n:ℝ)*profile ((p:ℝ)/(n:ℝ)) ≤ (normalizedDetLower n p : ℝ) := by
  have hdiv := Nat.div_mul_le_self n p
  have hfour : 4*(n/p) ≤ (4*n)/p := by
    apply (Nat.le_div_iff_mul_le hp).2
    calc
      (4*(n/p))*p = 4*((n/p)*p) := by ring
      _ ≤ 4*n := Nat.mul_le_mul_left 4 hdiv
  have hres : (0:ℝ) ≤ (((4*n)/p : ℕ):ℝ) - 2*(((n/p : ℕ):ℝ)) := by
    apply sub_nonneg.mpr
    exact_mod_cast (show 2*(n/p) ≤ (4*n)/p by omega)
  rw [normalizedDetLower_eq_profile n p hn hp]
  linarith

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.normalizedDetLower_ge_profile

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Stage0.HermitePreparation
open Polynomial

/-- The actual Hermite valuation bound pays at least the continuous profile
term for each prime. The Hermite estimate remains an explicit premise. -/
theorem parameter_dtilde_profile_weighted (lam : ℚ) (n p : ℕ)
    [Fact p.Prime] (hn : 0 < n)
    (hne : Qtilde lam n ≠ 0)
    (hgram : Li2.GV p (binomGram lam n).det (normalizedDetLower n p)) :
    (n:ℝ)*profile ((p:ℝ)/(n:ℝ))*Real.log (p:ℝ) ≤
      ((-padicValRat p (dtilde lam n) : ℤ):ℝ)*Real.log (p:ℝ) := by
  have hpPrime : p.Prime := Fact.out
  have hp : 0 < p := hpPrime.pos
  have hlog : 0 ≤ Real.log (p:ℝ) :=
    Real.log_nonneg (by exact_mod_cast hpPrime.one_lt.le)
  have hprofile := mul_le_mul_of_nonneg_right
    (normalizedDetLower_ge_profile n p hn hp) hlog
  exact hprofile.trans (parameter_dtilde_medium_weighted lam n p hne hgram)

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.parameter_dtilde_profile_weighted

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Stage0.HermitePreparation
open Li2.PrimeSums Finset Polynomial
open scoped BigOperators

/-- Actual primitive content dominates the full finite-`N` profile window.
The Hermite Gram estimate remains the visible per-prime premise. -/
theorem parameter_profileWindowClosedSumN_le_valuation
    (lam : ℚ) (N n : ℕ) (hN : 1 ≤ N)
    (hn : 0 < n) (hne : Qtilde lam n ≠ 0)
    (hgram : ∀ p ∈ Finset.Ioc
      ⌊((1:ℝ)/((N:ℝ)+1))*(n:ℝ)⌋₊ n,
      ∀ hp : p.Prime,
        letI : Fact p.Prime := ⟨hp⟩
        Li2.GV p (binomGram lam n).det (normalizedDetLower n p)) :
    profileWindowClosedSumN N n ≤
      ∑ p ∈ Finset.Ioc ⌊((1:ℝ)/((N:ℝ)+1))*(n:ℝ)⌋₊ n,
        if p.Prime then
          ((-padicValRat p (dtilde lam n) : ℤ) : ℝ)*Real.log (p:ℝ)
        else 0 := by
  rw [profileWindowClosedSumN_eq_profile N n hN hn]
  apply Finset.sum_le_sum
  intro p hpI
  by_cases hp : p.Prime
  · letI : Fact p.Prime := ⟨hp⟩
    simpa [cPrime, hp] using
      parameter_dtilde_profile_weighted lam n p hn hne (hgram p hpI hp)
  · simp [cPrime, hp]

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.parameter_profileWindowClosedSumN_le_valuation

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation Finset
open scoped BigOperators

private theorem reciprocal_square_telescope_N (N : ℕ) (hN : 2 ≤ N) :
    (∑ A ∈ Finset.Ico 2 (N+1),
      (((A:ℝ)⁻¹)^2 - ((((A:ℝ)+1)⁻¹)^2))) =
      ((2:ℝ)⁻¹)^2 - ((((N:ℝ)+1)⁻¹)^2) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hN2 : 2 ≤ N
    · rw [sum_Ico_succ_top (by omega : 2 ≤ N+1), ih hN2]
      push_cast
      ring
    · have hN1 : N = 1 := by omega
      subst N
      norm_num

/-- Every finite reciprocal cutoff keeps a positive telescoping correction
to the sharp profile integral. -/
theorem profile_cell_sum_N_lower (N : ℕ) (hN : 2 ≤ N) :
    (-523/840:ℝ) + (2/3:ℝ)/((N+1:ℕ):ℝ)^2 <
      ∑ A ∈ Finset.Ico (1:ℕ) (N+1), cellIntegral A := by
  have h1 : cellIntegral 1 = (-383/840:ℝ) := by
    norm_num [cellIntegral]
  have htail :
      (∑ A ∈ Finset.Ico (2:ℕ) (N+1),
        -(2/3:ℝ)*((((A:ℝ)⁻¹)^2)-(((((A:ℝ)+1)⁻¹)^2)))) <
      ∑ A ∈ Finset.Ico (2:ℕ) (N+1), cellIntegral A := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨2, by simp [hN]⟩
    · intro A hA
      have hA2 : (2:ℝ) ≤ A := by exact_mod_cast (mem_Ico.mp hA).1
      exact cell_positive_remainder (A:ℝ) hA2
  have htel := reciprocal_square_telescope_N N hN
  rw [← sum_Ico_consecutive (f := fun A : ℕ => cellIntegral A)
    (by decide : 1 ≤ 2) (by omega : 2 ≤ N+1)]
  have hfirst : (∑ A ∈ Finset.Ico (1:ℕ) 2, cellIntegral A) = cellIntegral 1 := by
    norm_num
  rw [hfirst, h1]
  have hsum :
      (∑ A ∈ Finset.Ico (2:ℕ) (N+1),
        -(2/3:ℝ)*((((A:ℝ)⁻¹)^2)-(((((A:ℝ)+1)⁻¹)^2)))) =
      -(2/3:ℝ)*((((2:ℝ)⁻¹)^2)-((((N:ℝ)+1)⁻¹)^2)) := by
    rw [← Finset.mul_sum, htel]
  rw [hsum] at htail
  push_cast at htail ⊢
  simp only [div_eq_mul_inv, ← inv_pow] at htail ⊢
  norm_num at htail ⊢
  linarith

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.profile_cell_sum_N_lower

end


end
