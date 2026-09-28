module
public import Li2Unified.Modular.Positive.Packed.P040
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public import Li2Unified.Modular.Positive.Packed.P039
public import Li2Unified.Modular.Positive.Packed.P042

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Finset
open scoped BigOperators

/-- Exact disjoint partition of all prime contributions up to `4n` into
the two exceptional primes and three intervals. -/
theorem prime_range_three_interval_partition (f : ℕ → ℝ)
    (n c : ℕ) (hc4 : 4 ≤ c) (hcn : c ≤ n) :
    (∑ p ∈ (Finset.range (4*n+1)).filter Nat.Prime, f p) =
      f 2 + f 3 +
      (∑ p ∈ Finset.Ioc 4 c, if p.Prime then f p else 0) +
      (∑ p ∈ Finset.Ioc c n, if p.Prime then f p else 0) +
      (∑ p ∈ Finset.Ioc n (4*n), if p.Prime then f p else 0) := by
  let g : ℕ → ℝ := fun p => if p.Prime then f p else 0
  have h0 : (∑ p ∈ Finset.range 5, g p) = f 2 + f 3 := by
    simp [g, Finset.sum_range_succ,
      show ¬ (0:ℕ).Prime by decide, show ¬ (1:ℕ).Prime by decide,
      show (2:ℕ).Prime by decide, show (3:ℕ).Prime by decide,
      show ¬ (4:ℕ).Prime by decide]
  have hIco (a b : ℕ) : Finset.Ico (a+1) (b+1) = Finset.Ioc a b := by
    ext p
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  have h5 : 5 ≤ 4*n+1 := by omega
  rw [Finset.sum_filter]
  change (∑ p ∈ Finset.range (4*n+1), g p) = _
  rw [← Finset.sum_range_add_sum_Ico g h5]
  have hsplit1 :
      (∑ p ∈ Finset.Ico 5 (4*n+1), g p) =
      (∑ p ∈ Finset.Ico 5 (c+1), g p) +
      (∑ p ∈ Finset.Ico (c+1) (4*n+1), g p) := by
    symm
    exact Finset.sum_Ico_consecutive (f := g) (by omega : 5 ≤ c+1)
      (by omega : c+1 ≤ 4*n+1)
  rw [hsplit1]
  have hsplit2 :
      (∑ p ∈ Finset.Ico (c+1) (4*n+1), g p) =
      (∑ p ∈ Finset.Ico (c+1) (n+1), g p) +
      (∑ p ∈ Finset.Ico (n+1) (4*n+1), g p) := by
    symm
    exact Finset.sum_Ico_consecutive (f := g) (by omega : c+1 ≤ n+1)
      (by omega : n+1 ≤ 4*n+1)
  rw [hsplit2, h0, hIco 4 c, hIco c n, hIco n (4*n)]
  simp only [g]
  ring

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.prime_range_three_interval_partition

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Finset
open scoped BigOperators

/-- Exact medium-prime partition at any finite cutoff. -/
theorem medium_prime_two_interval_partition (f : ℕ → ℝ)
    (n c : ℕ) (hc4 : 4 ≤ c) (hcn : c ≤ n) :
    (∑ p ∈ (Finset.range (n+1)).filter (fun p => p.Prime ∧ 5 ≤ p), f p) =
      (∑ p ∈ Finset.Ioc 4 c, if p.Prime then f p else 0) +
      (∑ p ∈ Finset.Ioc c n, if p.Prime then f p else 0) := by
  have hset :
      (Finset.range (n+1)).filter (fun p => p.Prime ∧ 5 ≤ p) =
        (Finset.Ioc 4 n).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨hpn, hpr, hp5⟩
      exact ⟨⟨by omega, by omega⟩, hpr⟩
    · rintro ⟨⟨hp4, hpn⟩, hpr⟩
      exact ⟨by omega, hpr, by omega⟩
  let g : ℕ → ℝ := fun p => if p.Prime then f p else 0
  have hIco (a b : ℕ) : Finset.Ico (a+1) (b+1) = Finset.Ioc a b := by
    ext p
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rw [hset, Finset.sum_filter]
  change (∑ p ∈ Finset.Ioc 4 n, g p) = _
  rw [← hIco 4 n]
  have hsplit :
      (∑ p ∈ Finset.Ico 5 (n+1), g p) =
      (∑ p ∈ Finset.Ico 5 (c+1), g p) +
      (∑ p ∈ Finset.Ico (c+1) (n+1), g p) := by
    symm
    exact Finset.sum_Ico_consecutive (f := g)
      (by omega : 5 ≤ c+1) (by omega : c+1 ≤ n+1)
  rw [hsplit, hIco 4 c, hIco c n]

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.medium_prime_two_interval_partition

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section

/-- The cutoff is chosen after `ε`; each proof uses only finitely many
reciprocal cells. -/
theorem exists_finite_cutoff (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧
      (0:ℝ) < 1/((N+1:ℕ):ℝ) ∧
      1/((N+1:ℕ):ℝ) ≤ 1 ∧
      4/((N+1:ℕ):ℝ) < ε/2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (8/ε+2)
  have hN2R : (2:ℝ) < (N:ℝ) := by
    have hnonneg : (0:ℝ) ≤ 8/ε := by positivity
    linarith
  have hN2 : 2 ≤ N := by exact_mod_cast hN2R.le
  have hden : (0:ℝ) < ((N+1:ℕ):ℝ) := by positivity
  have hN8 : 8/ε < (N:ℝ) := by linarith
  have h8 : 8 < ε*((N+1:ℕ):ℝ) := by
    have := (div_lt_iff₀ hε).mp hN8
    push_cast
    nlinarith
  refine ⟨N, hN2, by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ hden).mpr
    norm_num
  · apply (div_lt_iff₀ hden).mpr
    nlinarith

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.exists_finite_cutoff

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf
open Li2Unified.Stage0.HermitePreparation
open Filter Finset
open scoped BigOperators

end
end Li2Unified.Proofs.Arithmetic

end

end
