module
public import Li2Unified.Modular.Base.DecayLargePrimes

set_option backward.privateInPublic true

@[expose] public section

/-! Finite slot costs in the outer prime range. -/
namespace Li2
open scoped BigOperators

lemma Ncl_outer {p n c : ℕ} (hnp : n < p) :
    Ncl p n c = if c + 1 ≤ n then 1 else 0 := by
  unfold Ncl
  split_ifs with h
  · rw [Nat.div_eq_of_lt (by omega : n - (c + 1) < p)]
  · rfl

lemma Ccl_outer_le_four {p n c : ℕ} (hnp : n < p) :
    Ccl p (4*n) c ≤ 4 := by
  have hp0 : 0 < p := by omega
  unfold Ccl
  split_ifs with hc
  · have hd : (4*n-(c+1))/p < 4 :=
      (Nat.div_lt_iff_lt_mul hp0).mpr (by omega)
    omega
  · omega

lemma outer_class_low {p n c : ℕ} (hnp : n < p) (hcn : c+1 ≤ n) :
    (∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c),
      min (Wslot p n c k + 2*k) 0) = min (2 - (Ccl p (4*n) c : ℚ)) 0 := by
  have hp0 : 0 < p := by omega
  have hN : Ncl p n c = 1 := by rw [Ncl_outer hnp, if_pos hcn]
  have hC1 : 1 ≤ Ccl p (4*n) c := by
    simpa [hN] using (Ncl_le_Ccl (p := p) (n := n) (c := c) hp0)
  have hC4 := Ccl_outer_le_four (c := c) hnp
  have hd : ¬ p ∣ c+1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hj0 : ¬ p ≤ c+1 := by omega
  have hj1 : p ≤ c+1+p := by omega
  have hj2 : p ≤ c+1+p*2 := by omega
  have hj3 : p ≤ c+1+p*3 := by omega
  obtain hC | hC | hC | hC : Ccl p (4*n) c = 1 ∨ Ccl p (4*n) c = 2 ∨ Ccl p (4*n) c = 3 ∨ Ccl p (4*n) c = 4 := by omega
  all_goals norm_num [Wslot, Wcl, jn, hN, hd, hC, Finset.sum_range_succ, hj0, hj1, hj2, hj3]

lemma outer_class_high {p n c : ℕ} (hnp : n < p)
    (hcn : n < c+1) (hcp : c+1 < p) :
    (∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c),
      min (Wslot p n c k + 2*k) 0) = -3 * ((Ccl p (4*n) c - 1 : ℕ) : ℚ) := by
  have hN : Ncl p n c = 0 := by rw [Ncl_outer hnp, if_neg (by omega)]
  have hC4 := Ccl_outer_le_four (c := c) hnp
  have hd : ¬ p ∣ c+1 := Nat.not_dvd_of_pos_of_lt (by omega) hcp
  have hj0 : ¬ p ≤ c+1 := by omega
  have hj1 : p ≤ c+1+p := by omega
  have hj2 : p ≤ c+1+p*2 := by omega
  have hj3 : p ≤ c+1+p*3 := by omega
  obtain hC | hC | hC | hC | hC : Ccl p (4*n) c = 0 ∨ Ccl p (4*n) c = 1 ∨ Ccl p (4*n) c = 2 ∨ Ccl p (4*n) c = 3 ∨ Ccl p (4*n) c = 4 := by omega
  all_goals norm_num [Wslot, Wcl, jn, hN, hd, hC, Finset.sum_range_succ, hj0, hj1, hj2, hj3]

lemma outer_class_zero {p n c : ℕ} (hnp : n < p) (hcp : c+1 = p) :
    (∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c),
      min (Wslot p n c k + 2*k) 0) =
      -(Ccl p (4*n) c : ℚ) - (if Ccl p (4*n) c = 3 then 1 else 0) := by
  have hp0 : 0 < p := by omega
  have hN : Ncl p n c = 0 := by rw [Ncl_outer hnp, if_neg (by omega)]
  have hC3 : Ccl p (4*n) c ≤ 3 := by
    unfold Ccl
    split_ifs with hc
    · have hd : (4*n-(c+1))/p < 3 :=
        (Nat.div_lt_iff_lt_mul hp0).mpr (by omega)
      omega
    · omega
  have hd : p ∣ c+1 := by rw [hcp]
  have hj0 : p ≤ c+1 := by omega
  have hj1 : p ≤ c+1+p := by omega
  have hj2 : p ≤ c+1+p*2 := by omega
  obtain hC | hC | hC | hC : Ccl p (4*n) c = 0 ∨ Ccl p (4*n) c = 1 ∨ Ccl p (4*n) c = 2 ∨ Ccl p (4*n) c = 3 := by omega
  all_goals norm_num [Wslot, Wcl, jn, hN, hd, hC, Finset.sum_range_succ, hj0, hj1, hj2]

end Li2

end
