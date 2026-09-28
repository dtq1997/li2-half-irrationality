module
public import Li2Unified.Modular.Base.DecayMediumClosed

set_option backward.privateInPublic true

@[expose] public section

/-! Exact floor sums in the original factorial normalization. -/
open scoped BigOperators
namespace Li2
noncomputable section

lemma sum_range_div_block_rat {p : ℕ} (hp : 0 < p) (q : ℕ) :
    (∑ i ∈ Finset.range (q*p), ((i/p : ℕ) : ℚ)) =
      (p : ℚ) * q * ((q : ℚ) - 1) / 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have hs : (∑ i ∈ Finset.range p, (((q*p+i)/p : ℕ) : ℚ)) =
          (p : ℚ) * q := by
        calc
          (∑ i ∈ Finset.range p, (((q*p+i)/p : ℕ) : ℚ)) =
              ∑ _i ∈ Finset.range p, (q : ℚ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [show q*p+i = i+p*q by ring, Nat.add_mul_div_left _ _ hp,
              Nat.div_eq_of_lt (Finset.mem_range.mp hi), zero_add]
          _ = (p : ℚ) * q := by simp
      rw [hs]
      push_cast
      ring

lemma sum_range_div_rat {p K q r : ℕ} (hp : 0 < p) (hr : r < p)
    (hK : K = q*p+r) :
    (∑ i ∈ Finset.range K, ((i/p : ℕ) : ℚ)) =
      (K : ℚ) * q - (p : ℚ) * q * ((q : ℚ)+1) / 2 := by
  rw [hK, Finset.sum_range_add, sum_range_div_block_rat hp q]
  have hs : (∑ i ∈ Finset.range r, (((q*p+i)/p : ℕ) : ℚ)) =
      (r : ℚ) * q := by
    calc
      (∑ i ∈ Finset.range r, (((q*p+i)/p : ℕ) : ℚ)) =
          ∑ _i ∈ Finset.range r, (q : ℚ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hip : i < p := lt_trans (Finset.mem_range.mp hi) hr
        rw [show q*p+i = i+p*q by ring, Nat.add_mul_div_left _ _ hp,
          Nat.div_eq_of_lt hip, zero_add]
      _ = (r : ℚ) * q := by simp
  rw [hs]
  push_cast
  ring

lemma sum_range_div_rat' {p K : ℕ} (hp : 0 < p) :
    (∑ i ∈ Finset.range K, ((i/p : ℕ) : ℚ)) =
      (K : ℚ) * ((K/p : ℕ) : ℚ) -
        (p : ℚ) * ((K/p : ℕ) : ℚ) * (((K/p : ℕ) : ℚ)+1) / 2 := by
  apply sum_range_div_rat hp (Nat.mod_lt K hp)
  simpa [mul_comm] using (Nat.div_add_mod K p).symm

lemma normVal_eq_quotients {p n : ℕ} (hp : 0 < p) :
    normVal p n =
      2 * (n : ℚ) * ((((4*n)/p : ℕ) : ℚ) - 3 * ((n/p : ℕ) : ℚ)) -
      4 * (n : ℚ) * (((2*n)/p : ℕ) : ℚ) +
      (p : ℚ) * (((2*n)/p : ℕ) : ℚ) * ((((2*n)/p : ℕ) : ℚ)+1) := by
  rw [normVal, sum_range_div_rat' hp]
  push_cast
  ring

lemma normVal_of_quotients {p n A L B : ℕ} (hp : 0 < p)
    (hA : n/p = A) (hL : (4*n)/p = L) (hB : (2*n)/p = B) :
    normVal p n = 2*(n : ℚ)*((L : ℚ)-3*A) - 4*(n : ℚ)*B +
      (p : ℚ)*B*((B : ℚ)+1) := by
  rw [normVal_eq_quotients hp, hA, hL, hB]

end
end Li2

end
