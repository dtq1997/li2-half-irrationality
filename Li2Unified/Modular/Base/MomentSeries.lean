module
public import Li2Unified.Modular.Base.Family
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option backward.privateInPublic true

@[expose] public section

/-! Connect the rational moment recurrence to its defining convergent series. -/
open scoped BigOperators
namespace Li2
noncomputable section

def realMoment (k : ℕ) : ℝ :=
  ∑' m : ℕ, (-1/2 : ℝ)^(m+1) * ((m:ℝ)+1)^k

lemma summable_realMoment (k : ℕ) :
    Summable (fun m : ℕ => (-1/2 : ℝ)^(m+1) * ((m:ℝ)+1)^k) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one k
    (by norm_num : ‖(-1/2 : ℝ)‖ < 1)
  have ht := (summable_nat_add_iff 1).mpr hs
  simpa [Nat.cast_add, mul_comm] using ht

lemma realMoment_step_term (k m : ℕ) :
    (-1/2 : ℝ)^(m+2) * ((m:ℝ)+2)^k =
      (-1/2 : ℝ) * ∑ l ∈ Finset.range (k+1),
        (Nat.choose k l : ℝ) * ((-1/2 : ℝ)^(m+1) * ((m:ℝ)+1)^l) := by
  have hp : ((m:ℝ)+2)^k = ∑ l ∈ Finset.range (k+1),
      ((m:ℝ)+1)^l * (Nat.choose k l : ℝ) := by
    simpa [add_assoc, show (1:ℝ)+1=2 by norm_num] using add_pow ((m:ℝ)+1) 1 k
  rw [hp, show m+2 = (m+1)+1 by omega, pow_succ (-1/2 : ℝ) (m+1), Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma realMoment_recurrence (k : ℕ) :
    realMoment k = (-1/2 : ℝ) + (-1/2 : ℝ) *
      ∑ l ∈ Finset.range (k+1), (Nat.choose k l : ℝ) * realMoment l := by
  have hs := (summable_realMoment k).sum_add_tsum_nat_add 1
  have ht : (∑' m : ℕ, (-1/2 : ℝ)^(m+2) * ((m:ℝ)+2)^k) =
      (-1/2 : ℝ) * ∑ l ∈ Finset.range (k+1), (Nat.choose k l : ℝ) * realMoment l := by
    simp_rw [realMoment_step_term]
    rw [tsum_mul_left, Summable.tsum_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro l _
      exact tsum_mul_left
    · intro l _
      exact (summable_realMoment l).mul_left (Nat.choose k l : ℝ)
  have hs' : realMoment k = (-1/2 : ℝ) +
      ∑' m : ℕ, (-1/2 : ℝ)^(m+2) * ((m:ℝ)+2)^k := by
    simpa [realMoment, Finset.sum_range_one, Nat.cast_add, add_assoc,
      show (1:ℝ)+1=2 by norm_num] using hs.symm
  rw [hs', ht]

theorem moment_cast_eq_realMoment (k : ℕ) : (moment k : ℝ) = realMoment k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      have hr := realMoment_recurrence 0
      norm_num [Finset.sum_range_one] at hr
      norm_num [moment]
      linarith
    | succ k =>
      rw [moment]
      push_cast
      rw [Fin.sum_univ_eq_sum_range
        (fun l : ℕ => (Nat.choose (k+1) l : ℝ) * (moment l : ℝ)) (k+1)]
      have he : (∑ l ∈ Finset.range (k+1),
          (Nat.choose (k+1) l : ℝ) * (moment l : ℝ)) =
          ∑ l ∈ Finset.range (k+1), (Nat.choose (k+1) l : ℝ) * realMoment l := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [ih l (Finset.mem_range.mp hl)]
      rw [he]
      have hr := realMoment_recurrence (k+1)
      rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul] at hr
      linarith

end
end Li2

end
