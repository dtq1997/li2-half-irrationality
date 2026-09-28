module
public import Li2Unified.Modular.Base.DecayMediumRefined

set_option backward.privateInPublic true

@[expose] public section

/-! for every prime p > 4n (p != 2,3), Qtilde n is p-integral. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

theorem Qtilde_GV_large (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) {n : ℕ}
    (hpn : 4*n < p) : GV p (Qtilde n) 0 := by
  have hp0 := hp.out.pos
  have hK : 4*n < p^2 := lt_of_lt_of_le hpn (by nlinarith [hp.out.two_le])
  have h := Qtilde_GV_prime' p hp2 hp3 n hK
  refine h.mono ?_
  have hnorm : normVal p n = 0 := by
    unfold normVal
    rw [Nat.div_eq_of_lt hpn, Nat.div_eq_of_lt (by omega : n < p)]
    rw [Finset.sum_eq_zero fun i hi => by
      rw [Nat.div_eq_of_lt (by have := Finset.mem_range.mp hi; omega)]; simp]
    simp
  have hcls : ∀ c : Fin p, 0 ≤ ∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c),
      min (Wslot p n c k + 2 * k) 0 := by
    intro c
    have hC : Ccl p (4*n) c ≤ 1 := by
      unfold Ccl; split_ifs
      · rw [Nat.div_eq_of_lt (by omega)]
      · omega
    by_cases hS : Ccl p (4*n) c - Ncl p n c = 0
    · rw [hS]; simp
    · have hS1 : Ccl p (4*n) c - Ncl p n c = 1 := by omega
      have hC1 : Ccl p (4*n) c = 1 := by omega
      have hN0 : Ncl p n c = 0 := by omega
      have hcK : (c:ℕ) + 1 ≤ 4*n := Ccl_pos p (4*n) (t := 0) (by omega)
      rw [hS1, Finset.sum_range_one]
      have hj : jn p (4*n) c 0 = c + 1 := by simp [jn, hC1]
      have hnp : ¬ p ≤ jn p (4*n) c 0 := by rw [hj]; omega
      unfold Wslot Wcl
      rw [if_neg hnp, hC1, hN0]
      have : (0:ℚ) ≤ (if p ∣ (c:ℕ) + 1 then 1 else 0) := by split_ifs <;> norm_num
      apply le_min _ le_rfl
      push_cast
      linarith
  have := Finset.sum_nonneg (s := Finset.univ) fun c _ => hcls c
  rw [hnorm, add_zero]
  exact this

end
end Li2

end
