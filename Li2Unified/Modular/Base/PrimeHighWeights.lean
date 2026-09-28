module
public import Li2Unified.Modular.Base.PrimeFieldHighConstants
public import Li2Unified.Modular.Base.PrimeParameter

set_option backward.privateInPublic true

@[expose] public section

/-! Reduction of the three complete high-disc weights, including (-2)^a and -a. -/
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeField_two_ne_zero (hp4 : 3 < p) : (2:ZMod p) ≠ 0 := by
  intro he
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp he
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

lemma primeField_three_ne_zero (hp4 : 3 < p) : (3:ZMod p) ≠ 0 := by
  intro he
  have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp he
  have := Nat.le_of_dvd (by decide : 0 < 3) hd
  omega

end
end Li2

end
