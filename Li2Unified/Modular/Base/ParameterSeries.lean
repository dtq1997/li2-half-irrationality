module
public import Li2Unified.Modular.Base.ParameterMoments
public import Li2Unified.Modular.Base.Family
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option backward.privateInPublic true

@[expose] public section

/-! The parameter recurrence equals its convergent geometric moment series. -/
open scoped BigOperators
namespace Li2
noncomputable section

theorem parameterMoment_negHalf (k : ℕ) : parameterMoment (-1/2) k = moment k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => norm_num [parameterMoment, moment]
    | succ k =>
      rw [parameterMoment, moment]
      have hs : (∑ j : Fin (k+1), (Nat.choose (k+1) j.val : ℚ) * parameterMoment (-1/2) j.val) =
          ∑ j : Fin (k+1), (Nat.choose (k+1) j.val : ℚ) * moment j.val := by
        apply Finset.sum_congr rfl
        intro j _
        rw [ih j.val j.isLt]
      rw [hs]
      ring

def parameterRealMoment (z : ℝ) (k : ℕ) : ℝ :=
  ∑' m : ℕ, z^(m+1) * ((m:ℝ)+1)^k

lemma summable_parameterRealMoment (z : ℝ) (hz : ‖z‖ < 1) (k : ℕ) :
    Summable (fun m : ℕ => z^(m+1) * ((m:ℝ)+1)^k) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one k hz
  have ht := (summable_nat_add_iff 1).mpr hs
  simpa [Nat.cast_add, mul_comm] using ht

lemma parameterRealMoment_step_term (z : ℝ) (k m : ℕ) :
    z^(m+2) * ((m:ℝ)+2)^k =
      z * ∑ l ∈ Finset.range (k+1),
        (Nat.choose k l : ℝ) * (z^(m+1) * ((m:ℝ)+1)^l) := by
  have hp : ((m:ℝ)+2)^k = ∑ l ∈ Finset.range (k+1),
      ((m:ℝ)+1)^l * (Nat.choose k l : ℝ) := by
    simpa [add_assoc, show (1:ℝ)+1=2 by norm_num] using add_pow ((m:ℝ)+1) 1 k
  rw [hp, show m+2 = (m+1)+1 by omega, pow_succ z (m+1), Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma parameterRealMoment_recurrence (z : ℝ) (hz : ‖z‖ < 1) (k : ℕ) :
    parameterRealMoment z k = z + z *
      ∑ l ∈ Finset.range (k+1), (Nat.choose k l : ℝ) * parameterRealMoment z l := by
  have hs := (summable_parameterRealMoment z hz k).sum_add_tsum_nat_add 1
  have ht : (∑' m : ℕ, z^(m+2) * ((m:ℝ)+2)^k) =
      z * ∑ l ∈ Finset.range (k+1), (Nat.choose k l : ℝ) * parameterRealMoment z l := by
    simp_rw [parameterRealMoment_step_term]
    rw [tsum_mul_left, Summable.tsum_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro l _
      exact tsum_mul_left
    · intro l _
      exact (summable_parameterRealMoment z hz l).mul_left (Nat.choose k l : ℝ)
  have hs' : parameterRealMoment z k = z +
      ∑' m : ℕ, z^(m+2) * ((m:ℝ)+2)^k := by
    simpa [parameterRealMoment, Finset.sum_range_one, Nat.cast_add, add_assoc,
      show (1:ℝ)+1=2 by norm_num] using hs.symm
  rw [hs', ht]

theorem parameterMoment_cast_eq_series (z : ℚ) (hz : ‖(z:ℝ)‖ < 1) (k : ℕ) :
    (parameterMoment z k : ℝ) = parameterRealMoment z k := by
  have hd : (1:ℝ)-(z:ℝ) ≠ 0 := by
    intro h
    have he : (z:ℝ) = 1 := by linarith
    simp only [he, norm_one, lt_self_iff_false] at hz
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      rw [parameterMoment]
      push_cast
      apply (div_eq_iff hd).mpr
      have hr := parameterRealMoment_recurrence z hz 0
      norm_num [Finset.sum_range_one] at hr
      nlinarith
    | succ k =>
      rw [parameterMoment]
      push_cast
      rw [Fin.sum_univ_eq_sum_range
        (fun l : ℕ => (Nat.choose (k+1) l : ℝ) * (parameterMoment z l : ℝ)) (k+1)]
      have he : (∑ l ∈ Finset.range (k+1),
          (Nat.choose (k+1) l : ℝ) * (parameterMoment z l : ℝ)) =
          ∑ l ∈ Finset.range (k+1), (Nat.choose (k+1) l : ℝ) * parameterRealMoment z l := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [ih l (Finset.mem_range.mp hl)]
      rw [he, div_mul_eq_mul_div]
      apply (div_eq_iff hd).mpr
      have hr := parameterRealMoment_recurrence z hz (k+1)
      rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul] at hr
      nlinarith

end
end Li2

end
