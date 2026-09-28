module
public import Li2Unified.Modular.Base.Family

set_option backward.privateInPublic true

@[expose] public section

/-! Exact residue-class counts for the ORIGINAL numerator D_(p-1)^3 and
denominator D_(4p-4). These identify local factors; no asymptotic sample or
finite-prime test is used. -/
namespace Li2

lemma numerator_prime_factor_class (p a j : ℕ) (ha : a < p) :
    (j ∈ Finset.Icc 1 (p-1) ∧ j%p = a) ↔ (0 < a ∧ j = a) := by
  constructor
  · rintro ⟨hj, hm⟩
    have hj' := Finset.mem_Icc.mp hj
    rw [Nat.mod_eq_of_lt (by omega : j < p)] at hm
    omega
  · rintro ⟨ha0, rfl⟩
    exact ⟨Finset.mem_Icc.mpr ⟨ha0, by omega⟩, Nat.mod_eq_of_lt ha⟩

lemma denominator_zero_factor_class (p j : ℕ) (hp : 3 < p) :
    (j ∈ Finset.Icc 1 (4*(p-1)) ∧ j%p = 0) ↔
      (j = p ∨ j = 2*p ∨ j = 3*p) := by
  constructor
  · rintro ⟨hj, hm⟩
    have hj' := Finset.mem_Icc.mp hj
    have hq0 : 0 ≤ j/p := Nat.zero_le _
    have hq : j/p < 4 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    have he := Nat.mod_add_div j p
    rw [hm, zero_add] at he
    have hcases : j/p = 1 ∨ j/p = 2 ∨ j/p = 3 := by
      have hpos : j/p ≠ 0 := by intro h; rw [h, Nat.mul_zero] at he; omega
      omega
    rcases hcases with h | h | h <;> rw [h] at he <;> omega
  · intro h
    rcases h with rfl | rfl | rfl <;>
      constructor <;> first | (apply Finset.mem_Icc.mpr; constructor <;> omega) | simp

lemma denominator_low_factor_class (p a j : ℕ) (hp : 3 < p)
    (ha0 : 0 < a) (ha : a ≤ p-4) :
    (j ∈ Finset.Icc 1 (4*(p-1)) ∧ j%p = a) ↔
      (j = a ∨ j = a+p ∨ j = a+2*p ∨ j = a+3*p) := by
  have hap : a < p := by omega
  constructor
  · rintro ⟨hj, hm⟩
    have hj' := Finset.mem_Icc.mp hj
    have hq0 : 0 ≤ j/p := Nat.zero_le _
    have hq : j/p < 4 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    have he := Nat.mod_add_div j p
    rw [hm] at he
    have hcases : j/p = 0 ∨ j/p = 1 ∨ j/p = 2 ∨ j/p = 3 := by omega
    rcases hcases with h | h | h | h <;> rw [h] at he <;> omega
  · intro h
    rcases h with rfl | rfl | rfl | rfl <;>
      constructor <;> first | (apply Finset.mem_Icc.mpr; constructor <;> omega) |
        simp [Nat.add_mod, Nat.mod_eq_of_lt hap]

lemma denominator_high_factor_class (p a j : ℕ) (hp : 3 < p)
    (ha : p-3 ≤ a) (hap : a < p) :
    (j ∈ Finset.Icc 1 (4*(p-1)) ∧ j%p = a) ↔
      (j = a ∨ j = a+p ∨ j = a+2*p) := by
  have ha0 : 0 < a := by omega
  constructor
  · rintro ⟨hj, hm⟩
    have hj' := Finset.mem_Icc.mp hj
    have hq0 : 0 ≤ j/p := Nat.zero_le _
    have hq : j/p < 4 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    have he := Nat.mod_add_div j p
    rw [hm] at he
    have hnot : j/p ≠ 3 := by intro h; rw [h] at he; omega
    have hcases : j/p = 0 ∨ j/p = 1 ∨ j/p = 2 := by omega
    rcases hcases with h | h | h <;> rw [h] at he <;> omega
  · intro h
    rcases h with rfl | rfl | rfl <;>
      constructor <;> first | (apply Finset.mem_Icc.mpr; constructor <;> omega) |
        simp [Nat.add_mod, Nat.mod_eq_of_lt hap]

end Li2

end
