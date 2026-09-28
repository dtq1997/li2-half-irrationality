module
public import Li2Unified.Modular.Base.PrimeOuterTableSum
public import Li2Unified.Modular.Base.OuterPrimeWindows
public import Mathlib.Algebra.BigOperators.Intervals

set_option backward.privateInPublic true

@[expose] public section

open Finset Filter Topology
namespace Li2.PrimeSums
noncomputable section

lemma outerPrimeBound_cast_on_row (n : ℕ) (i : Fin 5) (p : ℕ)
    (hp : p ∈ Finset.Ioc ⌊outerWindowLeft i*(n : ℝ)⌋₊
      ⌊outerWindowRight i*(n : ℝ)⌋₊) :
    (Li2.outerPrimeBound p n : ℝ) =
      outerWindowAlpha i*(p : ℝ)+outerWindowBeta i*(n : ℝ)+outerWindowGamma i := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlo : outerWindowLeft i*(n : ℝ) < (p : ℝ) :=
    (Nat.floor_lt (mul_nonneg (outerWindowLeft_pos i).le hn)).mp
      (Finset.mem_Ioc.mp hp).1
  have hhi : (p : ℝ) ≤ outerWindowRight i*(n : ℝ) :=
    (Nat.le_floor_iff (mul_nonneg
      ((outerWindowLeft_pos i).le.trans (outerWindowLeft_le_right i)) hn)).mp
      (Finset.mem_Ioc.mp hp).2
  fin_cases i <;>
    norm_num [outerWindowAlpha, outerWindowBeta, outerWindowGamma,
      outerWindowLeft, outerWindowRight] at hlo hhi ⊢
  · have h1 : 3*p ≤ 4*n := by
      exact_mod_cast (show 3*(p : ℝ) ≤ 4*(n : ℝ) by linarith only [hhi])
    rw [Li2.outerPrimeBound, if_pos h1]
    push_cast <;> ring
  · have hloN : 4*n < 3*p := by
      exact_mod_cast (show 4*(n : ℝ) < 3*(p : ℝ) by linarith only [hlo])
    have h2 : 2*p ≤ 3*n := by
      exact_mod_cast (show 2*(p : ℝ) ≤ 3*(n : ℝ) by linarith only [hhi])
    have h1 : ¬3*p ≤ 4*n := by omega
    rw [Li2.outerPrimeBound, if_neg h1, if_pos h2]
    push_cast <;> ring
  · have hloN : 3*n < 2*p := by
      exact_mod_cast (show 3*(n : ℝ) < 2*(p : ℝ) by linarith only [hlo])
    have h3 : p ≤ 2*n := by exact_mod_cast hhi
    have h1 : ¬3*p ≤ 4*n := by omega
    have h2 : ¬2*p ≤ 3*n := by omega
    rw [Li2.outerPrimeBound, if_neg h1, if_neg h2, if_pos h3]
    push_cast <;> ring
  · have hloN : 2*n < p := by exact_mod_cast hlo
    have h4 : p ≤ 3*n := by exact_mod_cast hhi
    have h1 : ¬3*p ≤ 4*n := by omega
    have h2 : ¬2*p ≤ 3*n := by omega
    have h3 : ¬p ≤ 2*n := by omega
    rw [Li2.outerPrimeBound, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    push_cast <;> ring
  · have hloN : 3*n < p := by exact_mod_cast hlo
    have h1 : ¬3*p ≤ 4*n := by omega
    have h2 : ¬2*p ≤ 3*n := by omega
    have h3 : ¬p ≤ 2*n := by omega
    have h4 : ¬p ≤ 3*n := by omega
    rw [Li2.outerPrimeBound, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
    push_cast <;> ring

lemma outerWindowRowSum_eq_table (n : ℕ) (i : Fin 5) :
    affineSum (outerWindowAlpha i) (outerWindowBeta i)
        (outerWindowLeft i) (outerWindowRight i) (n : ℝ) +
      outerWindowGamma i*logSum (outerWindowLeft i*(n : ℝ))
        (outerWindowRight i*(n : ℝ)) =
    ∑ p ∈ Finset.Ioc ⌊outerWindowLeft i*(n : ℝ)⌋₊
      ⌊outerWindowRight i*(n : ℝ)⌋₊,
      ((Li2.outerPrimeBound p n : ℝ)*cPrime p) := by
  unfold affineSum logSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [outerPrimeBound_cast_on_row n i p hp]
  ring

lemma outerWindow_intervals_partition (n : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin 5,
      (∑ p ∈ Finset.Ioc ⌊outerWindowLeft i*(n : ℝ)⌋₊
        ⌊outerWindowRight i*(n : ℝ)⌋₊, (f p))) =
      ∑ p ∈ Finset.Ioc n (4*n), (f p) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h01 : n ≤ ⌊(4/3 : ℝ)*(n : ℝ)⌋₊ := by
    simpa only [Nat.floor_natCast] using!
      Nat.floor_le_floor (show (n : ℝ) ≤ (4/3 : ℝ)*(n : ℝ) by linarith only [hn])
  have h12 : ⌊(4/3 : ℝ)*(n : ℝ)⌋₊ ≤ ⌊(3/2 : ℝ)*(n : ℝ)⌋₊ :=
    Nat.floor_le_floor (by linarith only [hn])
  have h23 : ⌊(3/2 : ℝ)*(n : ℝ)⌋₊ ≤ ⌊(2 : ℝ)*(n : ℝ)⌋₊ :=
    Nat.floor_le_floor (by linarith only [hn])
  have h34 : ⌊(2 : ℝ)*(n : ℝ)⌋₊ ≤ ⌊(3 : ℝ)*(n : ℝ)⌋₊ :=
    Nat.floor_le_floor (by linarith only [hn])
  have h45 : ⌊(3 : ℝ)*(n : ℝ)⌋₊ ≤ ⌊(4 : ℝ)*(n : ℝ)⌋₊ :=
    Nat.floor_le_floor (by linarith only [hn])
  have h4 : ⌊(4 : ℝ)*(n : ℝ)⌋₊ = 4*n := by
    rw [show (4 : ℝ)*(n : ℝ) = ((4*n : ℕ) : ℝ) by norm_num,
      Nat.floor_natCast]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, outerWindowLeft,
    outerWindowRight, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero, one_mul, Nat.floor_natCast]
  rw [Finset.sum_Ioc_consecutive f h34 h45,
    Finset.sum_Ioc_consecutive f h23 (h34.trans h45),
    Finset.sum_Ioc_consecutive f h12 (h23.trans (h34.trans h45)),
    Finset.sum_Ioc_consecutive f h01 (h12.trans (h23.trans (h34.trans h45))), h4]

theorem outerWindowSum_eq_table (n : ℕ) :
    outerWindowSum (n : ℝ) =
      ∑ p ∈ Finset.Ioc n (4*n), ((Li2.outerPrimeBound p n : ℝ)*cPrime p) := by
  unfold outerWindowSum outerWindowLeadingSum outerWindowCorrection
  rw [← Finset.sum_add_distrib]
  simp_rw [outerWindowRowSum_eq_table]
  exact outerWindow_intervals_partition n (fun p => (Li2.outerPrimeBound p n : ℝ)*cPrime p)

theorem outerPrimeBound_sum_nat_tendsto :
    Tendsto (fun n : ℕ =>
      (∑ p ∈ Finset.Ioc n (4*n), ((Li2.outerPrimeBound p n : ℝ)*cPrime p))/(n : ℝ)^2)
      atTop (𝓝 (7/2 : ℝ)) := by
  simpa only [← outerWindowSum_eq_table] using! outerWindowSum_nat_tendsto

end
end Li2.PrimeSums

end
