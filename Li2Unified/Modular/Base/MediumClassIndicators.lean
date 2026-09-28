module
public import Li2Unified.Modular.Base.MediumClassCounts

set_option backward.privateInPublic true

@[expose] public section

open scoped BigOperators
namespace Li2
noncomputable section

lemma sum_range_two_cuts_rat {p r s : ℕ} (hr : r ≤ p) (hs : s ≤ p)
    (u v w z : ℚ) :
    (∑ c ∈ Finset.range p,
      if c < r then (if c < s then u else v)
      else (if c < s then w else z)) =
      (p : ℚ)*z + (r : ℚ)*(v-z) + (s : ℚ)*(w-z) +
      ((min r s : ℕ) : ℚ)*(u-v-w+z) := by
  have hpoint : ∀ c : ℕ,
      (if c < r then (if c < s then u else v)
        else (if c < s then w else z)) =
      z + (if c < r then v-z else 0) + (if c < s then w-z else 0) +
        (if c < min r s then u-v-w+z else 0) := by
    intro c
    by_cases hcr : c < r <;> by_cases hcs : c < s <;>
      simp [hcr, hcs, lt_min_iff] <;> ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [sum_range_ite_lt_rat hr (v-z) 0, sum_range_ite_lt_rat hs (w-z) 0,
    sum_range_ite_lt_rat (le_trans (min_le_left r s) hr) (u-v-w+z) 0]
  simp

lemma sum_fin_two_cuts_rat {p r s : ℕ} (hr : r ≤ p) (hs : s ≤ p)
    (u v w z : ℚ) :
    (∑ c : Fin p,
      if (c : ℕ) < r then (if (c : ℕ) < s then u else v)
      else (if (c : ℕ) < s then w else z)) =
      (p : ℚ)*z + (r : ℚ)*(v-z) + (s : ℚ)*(w-z) +
      ((min r s : ℕ) : ℚ)*(u-v-w+z) := by
  rw [Fin.sum_univ_eq_sum_range (fun c : ℕ =>
    if c < r then (if c < s then u else v) else (if c < s then w else z))]
  exact sum_range_two_cuts_rat hr hs u v w z

end
end Li2

end
