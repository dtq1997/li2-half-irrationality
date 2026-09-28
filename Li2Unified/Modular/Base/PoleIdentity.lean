module
public import Li2Unified.Modular.Base.Family
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option backward.privateInPublic true

@[expose] public section

/-! The simple-pole part of the derivative functional is connected to the
actual real series, for every shift j (including j=0). -/
namespace Li2

lemma tau_cast_eq_partial_sum (j : ℕ) : (tau j : ℝ) =
    ∑ k ∈ Finset.range j, (-1/2 : ℝ)^(k+1) / ((k:ℝ)+1)^2 := by
  induction j with
  | zero => simp [tau]
  | succ j ih =>
    rw [tau, Finset.sum_Icc_succ_top (by omega)]
    push_cast
    rw [Finset.sum_range_succ]
    have hi := ih
    unfold tau at hi
    push_cast at hi
    rw [hi]

lemma li2_tail (j : ℕ) :
    ∑' k : ℕ, (-1/2 : ℝ)^(k+j+1) / ((k+j:ℕ)+1 : ℝ)^2 =
      li2NegHalf - (tau j : ℝ) := by
  have hs := summable_li2NegHalf.sum_add_tsum_nat_add j
  rw [← tau_cast_eq_partial_sum, ← li2NegHalf] at hs
  simpa only [Nat.cast_add] using (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hs))

theorem shifted_dilog_identity (j : ℕ) :
    ∑' k : ℕ, (-1/2 : ℝ)^(k+1) / ((k+j:ℕ)+1 : ℝ)^2 =
      (-2 : ℝ)^j * (li2NegHalf - (tau j : ℝ)) := by
  rw [← li2_tail, ← tsum_mul_left]
  apply tsum_congr
  intro k
  have hp : (-2 : ℝ)^j * (-1/2 : ℝ)^j = 1 := by
    rw [← mul_pow]
    norm_num
  rw [show k+j+1 = (k+1)+j by omega, pow_add _ (k+1) j]
  calc
    (-1/2 : ℝ)^(k+1) / ((k+j:ℕ)+1 : ℝ)^2 =
        ((-1/2 : ℝ)^(k+1) / ((k+j:ℕ)+1 : ℝ)^2) *
          ((-2 : ℝ)^j * (-1/2 : ℝ)^j) := by rw [hp, mul_one]
    _ = _ := by ring

/-- The coefficient j comes from d(t/(t+j))/dt = j/(t+j)^2. -/
theorem pole_functional_identity (j : ℕ) :
    ∑' k : ℕ, (-1/2 : ℝ)^(k+1) * (j : ℝ) / ((k+j:ℕ)+1 : ℝ)^2 =
      (j : ℝ) * (-2 : ℝ)^j * (li2NegHalf - (tau j : ℝ)) := by
  calc
    _ = (j : ℝ) * ∑' k : ℕ, (-1/2 : ℝ)^(k+1) / ((k+j:ℕ)+1 : ℝ)^2 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      ring
    _ = _ := by rw [shifted_dilog_identity]; ring

end Li2

end
