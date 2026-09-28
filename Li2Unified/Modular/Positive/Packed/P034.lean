module
public import Li2Unified.Modular.Positive.Packed.P029
public import Li2Unified.Modular.Positive.Packed.P033

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation
open Li2.PrimeSums Finset
open scoped BigOperators

/-- On each half-open window the affine prime sum is literally the weighted
profile sum, including every rational endpoint. -/
theorem profileWindowRow_eq_profile (A n : ℕ) (hA : 1 ≤ A) (hn : 0 < n)
    (j : Fin 6) :
    affineSum (profileWindowAlpha A j) (profileWindowBeta A j)
      (profileWindowLeft A j) (profileWindowRight A j) (n:ℝ) =
      ∑ p ∈ Finset.Ioc
        ⌊profileWindowLeft A j*(n:ℝ)⌋₊
        ⌊profileWindowRight A j*(n:ℝ)⌋₊,
        ((n:ℝ)*profile ((p:ℝ)/(n:ℝ))*cPrime p) := by
  unfold affineSum
  apply Finset.sum_congr rfl
  intro p hp
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hleftpos : 0 ≤ profileWindowLeft A j*(n:ℝ) := by
    have hAr : (1:ℝ) ≤ A := by exact_mod_cast hA
    have hwin : 0 < profileWindowLeft A j := by
      fin_cases j <;> norm_num [profileWindowLeft] <;> positivity
    exact mul_nonneg hwin.le hnR.le
  have hrightpos : 0 ≤ profileWindowRight A j*(n:ℝ) := by
    have hAr : (1:ℝ) ≤ A := by exact_mod_cast hA
    have hwin : 0 < profileWindowRight A j := by
      fin_cases j <;> norm_num [profileWindowRight] <;> positivity
    exact mul_nonneg hwin.le hnR.le
  have hl : profileWindowLeft A j*(n:ℝ) < (p:ℝ) :=
    (Nat.floor_lt hleftpos).mp (Finset.mem_Ioc.mp hp).1
  have hr : (p:ℝ) ≤ profileWindowRight A j*(n:ℝ) :=
    (Nat.le_floor_iff hrightpos).mp (Finset.mem_Ioc.mp hp).2
  have hwindow : profileWindowLeft A j < (p:ℝ)/(n:ℝ) ∧
      (p:ℝ)/(n:ℝ) ≤ profileWindowRight A j := by
    constructor
    · exact (lt_div_iff₀ hnR).2 hl
    · exact (div_le_iff₀ hnR).2 hr
  rw [profile_window_half_open A hA j _ hwindow.1 hwindow.2]
  have hn0 : (n:ℝ) ≠ 0 := hnR.ne'
  field_simp

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.profileWindowRow_eq_profile

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Finset
open scoped BigOperators

private lemma window_lt_partition (A : ℝ) (hA : 1 ≤ A) (j : Fin 6) :
    profileWindowLeft A j < profileWindowRight A j := by
  have hApos : 0 < A := by linarith
  fin_cases j <;> norm_num [profileWindowLeft, profileWindowRight]
  all_goals
    try simp only [← one_div]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith

/-- The six half-open windows partition one reciprocal cell exactly, even
when a rational endpoint is an integer prime. -/
theorem profileWindowCell_partition (A n : ℕ) (hA : 1 ≤ A) (f : ℕ → ℝ) :
    (∑ j : Fin 6,
      ∑ p ∈ Finset.Ioc
        ⌊profileWindowLeft A j*(n:ℝ)⌋₊
        ⌊profileWindowRight A j*(n:ℝ)⌋₊, f p) =
      ∑ p ∈ Finset.Ioc ⌊((1:ℝ)/((A:ℝ)+1))*(n:ℝ)⌋₊
        ⌊((1:ℝ)/(A:ℝ))*(n:ℝ)⌋₊, f p := by
  let b0 := ⌊profileWindowLeft A (5:Fin 6)*(n:ℝ)⌋₊
  let b1 := ⌊profileWindowRight A (5:Fin 6)*(n:ℝ)⌋₊
  let b2 := ⌊profileWindowRight A (4:Fin 6)*(n:ℝ)⌋₊
  let b3 := ⌊profileWindowRight A (3:Fin 6)*(n:ℝ)⌋₊
  let b4 := ⌊profileWindowRight A (2:Fin 6)*(n:ℝ)⌋₊
  let b5 := ⌊profileWindowRight A (1:Fin 6)*(n:ℝ)⌋₊
  let b6 := ⌊profileWindowRight A (0:Fin 6)*(n:ℝ)⌋₊
  have hAr : (1:ℝ) ≤ A := by exact_mod_cast hA
  have hnR : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hle (j : Fin 6) :
      ⌊profileWindowLeft A j*(n:ℝ)⌋₊ ≤
        ⌊profileWindowRight A j*(n:ℝ)⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_right
      (window_lt_partition A hAr j).le hnR)
  have h01 : b0 ≤ b1 := hle 5
  have h12 : b1 ≤ b2 := by simpa [b1, b2, profileWindowLeft,
    profileWindowRight] using hle 4
  have h23 : b2 ≤ b3 := by simpa [b2, b3, profileWindowLeft,
    profileWindowRight] using hle 3
  have h34 : b3 ≤ b4 := by simpa [b3, b4, profileWindowLeft,
    profileWindowRight] using hle 2
  have h45 : b4 ≤ b5 := by simpa [b4, b5, profileWindowLeft,
    profileWindowRight] using hle 1
  have h56 : b5 ≤ b6 := by simpa [b5, b6, profileWindowLeft,
    profileWindowRight] using hle 0
  let S (j : Fin 6) : ℝ :=
    ∑ p ∈ Finset.Ioc
      ⌊profileWindowLeft A j*(n:ℝ)⌋₊
      ⌊profileWindowRight A j*(n:ℝ)⌋₊, f p
  have hS : (∑ j : Fin 6, S j) =
      (∑ p ∈ Finset.Ioc b0 b1, f p) +
      (∑ p ∈ Finset.Ioc b1 b2, f p) +
      (∑ p ∈ Finset.Ioc b2 b3, f p) +
      (∑ p ∈ Finset.Ioc b3 b4, f p) +
      (∑ p ∈ Finset.Ioc b4 b5, f p) +
      (∑ p ∈ Finset.Ioc b5 b6, f p) := by
    simp [S, b0, b1, b2, b3, b4, b5, b6,
      Fin.sum_univ_succ, profileWindowLeft, profileWindowRight]
    abel
  change (∑ j : Fin 6, S j) = _
  rw [hS, Finset.sum_Ioc_consecutive f h01 h12,
    Finset.sum_Ioc_consecutive f (h01.trans h12) h23,
    Finset.sum_Ioc_consecutive f ((h01.trans h12).trans h23) h34,
    Finset.sum_Ioc_consecutive f (((h01.trans h12).trans h23).trans h34) h45,
    Finset.sum_Ioc_consecutive f ((((h01.trans h12).trans h23).trans h34).trans h45) h56]
  simp [b0, b6, profileWindowLeft, profileWindowRight]

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.profileWindowCell_partition

end


end
