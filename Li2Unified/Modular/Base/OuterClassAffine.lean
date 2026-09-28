module
public import Li2Unified.Modular.Base.OuterClassCosts

set_option backward.privateInPublic true

@[expose] public section

namespace Li2
open scoped BigOperators

lemma outer_class_q3 {p n c r : ℕ} (hnp : n < p) (hc : c < p)
    (hrn : r ≤ n) (hC : Ccl p (4*n) c = 3 + if c < r then 1 else 0) :
    (∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c),
      min (Wslot p n c k + 2*k) 0) =
    -6 - (if c < r then 1 else 0) + 5*(if c < n then 1 else 0) +
      2*(if c+1 = p then 1 else 0) := by
  by_cases hz : c+1 = p
  · rw [outer_class_zero hnp hz, hC]
    norm_num [hz, show ¬ c < r by omega, show ¬ c < n by omega]
  · have hcp : c+1 < p := by omega
    by_cases hn : c < n
    · rw [outer_class_low hnp (by omega), hC]
      by_cases hr : c < r <;> norm_num [hz, hn, hr]
    · rw [outer_class_high hnp (by omega) hcp, hC]
      norm_num [hz, hn, show ¬ c < r by omega]

lemma outer_class_q2_above {p n c r : ℕ} (hnp : n < p) (hc : c < p)
    (hrp : r < p) (hnr : n ≤ r)
    (hC : Ccl p (4*n) c = 2 + if c < r then 1 else 0) :
    (∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c),
      min (Wslot p n c k + 2*k) 0) =
    -3 - 3*(if c < r then 1 else 0) + 5*(if c < n then 1 else 0) +
      (if c+1 = p then 1 else 0) := by
  by_cases hz : c+1 = p
  · rw [outer_class_zero hnp hz, hC]
    norm_num [hz, show ¬ c < r by omega, show ¬ c < n by omega]
  · have hcp : c+1 < p := by omega
    by_cases hn : c < n
    · rw [outer_class_low hnp (by omega), hC]
      norm_num [hz, hn, show c < r by omega]
    · rw [outer_class_high hnp (by omega) hcp, hC]
      by_cases hr : c < r <;> norm_num [hz, hn, hr]

lemma outer_class_q2_below {p n c r : ℕ} (hnp : n < p) (hc : c < p)
    (hrn : r ≤ n) (hC : Ccl p (4*n) c = 2 + if c < r then 1 else 0) :
    (∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c),
      min (Wslot p n c k + 2*k) 0) =
    -3 - (if c < r then 1 else 0) + 3*(if c < n then 1 else 0) +
      (if c+1 = p then 1 else 0) := by
  by_cases hz : c+1 = p
  · rw [outer_class_zero hnp hz, hC]
    norm_num [hz, show ¬ c < r by omega, show ¬ c < n by omega]
  · have hcp : c+1 < p := by omega
    by_cases hn : c < n
    · rw [outer_class_low hnp (by omega), hC]
      by_cases hr : c < r <;> norm_num [hz, hn, hr]
    · rw [outer_class_high hnp (by omega) hcp, hC]
      norm_num [hz, hn, show ¬ c < r by omega]

lemma outer_class_q1_above {p n c r : ℕ} (hnp : n < p) (hc : c < p)
    (hrp : r < p) (hnr : n ≤ r)
    (hC : Ccl p (4*n) c = 1 + if c < r then 1 else 0) :
    (∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c),
      min (Wslot p n c k + 2*k) 0) =
    -3*(if c < r then 1 else 0) + 3*(if c < n then 1 else 0) -
      (if c+1 = p then 1 else 0) := by
  by_cases hz : c+1 = p
  · rw [outer_class_zero hnp hz, hC]
    norm_num [hz, show ¬ c < r by omega, show ¬ c < n by omega]
  · have hcp : c+1 < p := by omega
    by_cases hn : c < n
    · rw [outer_class_low hnp (by omega), hC]
      norm_num [hz, hn, show c < r by omega]
    · rw [outer_class_high hnp (by omega) hcp, hC]
      by_cases hr : c < r <;> norm_num [hz, hn, hr]

lemma outer_class_q1_below {p n c r : ℕ} (hnp : n < p) (hc : c < p)
    (hrn : r ≤ n) (hC : Ccl p (4*n) c = 1 + if c < r then 1 else 0) :
    (∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c),
      min (Wslot p n c k + 2*k) 0) =
      -(if c+1 = p then 1 else 0 : ℚ) := by
  by_cases hz : c+1 = p
  · rw [outer_class_zero hnp hz, hC]
    norm_num [hz, show ¬ c < r by omega]
  · have hcp : c+1 < p := by omega
    by_cases hn : c < n
    · rw [outer_class_low hnp (by omega), hC]
      by_cases hr : c < r <;> norm_num [hz, hr]
    · rw [outer_class_high hnp (by omega) hcp, hC]
      norm_num [hz, show ¬ c < r by omega]

end Li2

end
