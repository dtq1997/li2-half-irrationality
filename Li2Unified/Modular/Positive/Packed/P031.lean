module
public import Li2Unified.Modular.Positive.Packed.P028
public import Li2Unified.Modular.Positive.Packed.P025

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Finset
open scoped BigOperators

/-- All reciprocal cells from A=1 through N concatenate to one interval. -/
theorem profileWindowCells_partition (N n : ℕ) (hN : 1 ≤ N) (f : ℕ → ℝ) :
    (∑ A ∈ Finset.Ico (1:ℕ) (N+1),
      ∑ p ∈ Finset.Ioc
        ⌊((1:ℝ)/((A:ℝ)+1))*(n:ℝ)⌋₊
        ⌊((1:ℝ)/(A:ℝ))*(n:ℝ)⌋₊, f p) =
      ∑ p ∈ Finset.Ioc ⌊((1:ℝ)/((N:ℝ)+1))*(n:ℝ)⌋₊ n, f p := by
  induction N, hN using Nat.le_induction with
  | base =>
    norm_num
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ N+1), ih]
    have hnR : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hN1 : (0:ℝ) < (N:ℝ)+1 := by exact_mod_cast (by omega : 0 < N+1)
    have hN2 : (0:ℝ) < (N:ℝ)+2 := by linarith
    have hrec : (1:ℝ)/((N:ℝ)+2) ≤ 1/((N:ℝ)+1) :=
      one_div_le_one_div_of_le hN1 (by linarith)
    have h01 :
        ⌊((1:ℝ)/((N:ℝ)+2))*(n:ℝ)⌋₊ ≤
          ⌊((1:ℝ)/((N:ℝ)+1))*(n:ℝ)⌋₊ :=
      Nat.floor_le_floor (mul_le_mul_of_nonneg_right hrec hnR)
    have hrec1 : (1:ℝ)/((N:ℝ)+1) ≤ 1 := by
      have hNge : (1:ℝ) ≤ (N:ℝ)+1 := by
        have := Nat.cast_nonneg (α := ℝ) N
        linarith
      have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
        hNge
      simpa using! h
    have h12 : ⌊((1:ℝ)/((N:ℝ)+1))*(n:ℝ)⌋₊ ≤ n := by
      have h := Nat.floor_le_floor (mul_le_mul_of_nonneg_right hrec1 hnR)
      simpa using! h
    have hconcat := Finset.sum_Ioc_consecutive f h01 h12
    rw [add_comm]
    convert hconcat using 1 <;> push_cast <;> ring

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.profileWindowCells_partition

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation

end
end Li2Unified.Proofs.Arithmetic

end

end
