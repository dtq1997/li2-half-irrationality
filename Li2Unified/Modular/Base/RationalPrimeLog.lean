module
public import Li2Unified.Modular.Base.RationalPrimeSupport
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Rat.Cast.Order

set_option backward.privateInPublic true

@[expose] public section

open scoped BigOperators
namespace Li2

theorem log_nat_eq_sum_of_support_subset (n : ℕ) (S : Finset ℕ)
    (hS : n.factorization.support ⊆ S) :
    Real.log (n : ℝ) =
      ∑ p ∈ S, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization]
  change (∑ p ∈ n.factorization.support,
    (n.factorization p : ℝ) * Real.log (p : ℝ)) = _
  apply Finset.sum_subset hS
  intro p hpS hpout
  rw [Finsupp.notMem_support_iff.mp hpout]
  simp

/-- Exact finite prime sum with signed valuations. -/
theorem log_rat_eq_sum_padicValRat {s : ℚ} (hs : 0 < s) :
    Real.log (s : ℝ) =
      ∑ p ∈ ratPrimeSupport s, (padicValRat p s : ℝ) * Real.log (p : ℝ) := by
  have hnum : 0 < s.num := Rat.num_pos.mpr hs
  have hnum0 : (s.num : ℝ) ≠ 0 := (Int.cast_pos.mpr hnum).ne'
  have hden0 : (s.den : ℝ) ≠ 0 := (Nat.cast_pos.mpr s.den_pos).ne'
  have habs : (s.num.natAbs : ℝ) = (s.num : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg hnum.le)
    simpa only [Int.cast_natCast] using h
  have hN : s.num.natAbs.factorization.support ⊆ ratPrimeSupport s := by
    intro p hp
    exact Finset.mem_union.mpr (Or.inl hp)
  have hD : s.den.factorization.support ⊆ ratPrimeSupport s := by
    intro p hp
    exact Finset.mem_union.mpr (Or.inr hp)
  calc
    Real.log (s : ℝ) =
        Real.log (s.num.natAbs : ℝ) - Real.log (s.den : ℝ) := by
      rw [Rat.cast_def, Real.log_div hnum0 hden0, habs]
    _ = (∑ p ∈ ratPrimeSupport s,
          (s.num.natAbs.factorization p : ℝ) * Real.log (p : ℝ)) -
        (∑ p ∈ ratPrimeSupport s,
          (s.den.factorization p : ℝ) * Real.log (p : ℝ)) := by
      rw [log_nat_eq_sum_of_support_subset s.num.natAbs (ratPrimeSupport s) hN,
        log_nat_eq_sum_of_support_subset s.den (ratPrimeSupport s) hD]
    _ = ∑ p ∈ ratPrimeSupport s,
        (padicValRat p s : ℝ) * Real.log (p : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [padicValRat_eq_factorizations p (ratPrimeSupport_prime hp) s,
        Int.cast_sub, Int.cast_natCast, sub_mul]

theorem log_rat_eq_sum_padicValRat_of_support_subset {s : ℚ} (hs : 0 < s)
    (S : Finset ℕ) (hS : ratPrimeSupport s ⊆ S)
    (hprime : ∀ p ∈ S, p.Prime) :
    Real.log (s : ℝ) =
      ∑ p ∈ S, (padicValRat p s : ℝ) * Real.log (p : ℝ) := by
  rw [log_rat_eq_sum_padicValRat hs]
  apply Finset.sum_subset hS
  intro p hp hpout
  rw [padicValRat_eq_zero_of_not_mem_ratPrimeSupport (hprime p hp) hpout]
  simp

end Li2

end
