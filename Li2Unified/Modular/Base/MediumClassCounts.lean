module
public import Li2Unified.Modular.Base.DecayMediumClosed

set_option backward.privateInPublic true

@[expose] public section

/-! Exact residue-class counts and finite step-function sums. -/
open scoped BigOperators
namespace Li2
noncomputable section

lemma Ccl_eq_quot_rem {p K c q r : ℕ} (hp : 0 < p) (hc : c < p)
    (hr : r < p) (hK : K = q * p + r) :
    Ccl p K c = q + if c < r then 1 else 0 := by
  by_cases hcr : c < r
  · have hcK : c + 1 ≤ K := by omega
    rw [Ccl, if_pos hcK, if_pos hcr]
    congr 1
    apply div_eq_of_bounds
    · omega
    · rw [add_mul, one_mul]
      omega
  · rw [if_neg hcr, add_zero]
    cases q with
    | zero =>
        have hcK : ¬ c + 1 ≤ K := by
          simp only [zero_mul, zero_add] at hK
          omega
        simp [Ccl, hcK]
    | succ q =>
        have hK' : K = q * p + p + r := by simpa [Nat.succ_mul] using hK
        have hcK : c + 1 ≤ K := by omega
        rw [Ccl, if_pos hcK]
        have hd : (K - (c + 1)) / p = q := by
          apply div_eq_of_bounds
          · omega
          · rw [add_mul, one_mul]
            omega
        rw [hd]

lemma sum_range_ite_lt_rat {p r : ℕ} (hr : r ≤ p) (A B : ℚ) :
    (∑ c ∈ Finset.range p, if c < r then A else B) =
      (r : ℚ) * A + ((p - r : ℕ) : ℚ) * B := by
  have hp : p = r + (p - r) := by omega
  calc
    (∑ c ∈ Finset.range p, if c < r then A else B) =
        (∑ c ∈ Finset.range r, if c < r then A else B) +
        (∑ c ∈ Finset.range (p-r), if r+c < r then A else B) := by
          rw [← Finset.sum_range_add, ← hp]
    _ = (r : ℚ) * A + ((p-r : ℕ) : ℚ) * B := by
      congr 1
      · calc
          (∑ c ∈ Finset.range r, if c < r then A else B) =
              ∑ _c ∈ Finset.range r, A :=
                Finset.sum_congr rfl (fun c hc => if_pos (Finset.mem_range.mp hc))
          _ = (r : ℚ) * A := by simp
      · calc
          (∑ c ∈ Finset.range (p-r), if r+c < r then A else B) =
              ∑ _c ∈ Finset.range (p-r), B :=
                Finset.sum_congr rfl (fun c _ => if_neg (by omega))
          _ = ((p-r : ℕ) : ℚ) * B := by simp

end
end Li2

end
