module
public import Li2Unified.Modular.Base.ParameterMoments
public import Li2Unified.Modular.Base.PrimitiveReduction
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.FieldSimp

set_option backward.privateInPublic true

@[expose] public section

/-! Fermat congruence and the p-integral moment parameter z=(-1/2)^p. -/
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma VG.intCast_of_dvd {a : ℤ} (ha : (p:ℤ) ∣ a) : VG p (a:ℚ) 1 := by
  obtain ⟨b, rfl⟩ := ha
  rw [Int.cast_mul, Int.cast_natCast]
  have ht := (VG.primePow (p := p) (1:ℤ)).mul (VG.intCast (p := p) b)
  simpa using ht

lemma prime_nat_valuation_zero {l : ℕ} (hl : l.Prime) (hpl : p ≠ l) :
    padicValRat p (l:ℚ) = 0 := by
  have hnd : ¬p ∣ l := fun h => hpl ((Nat.prime_dvd_prime_iff_eq hp.out hl).mp h)
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
  rfl

lemma two_valuation_zero (hp2 : p ≠ 2) : padicValRat p (2:ℚ) = 0 :=
  prime_nat_valuation_zero (by decide) hp2

lemma three_valuation_zero (hp3 : p ≠ 3) : padicValRat p (3:ℚ) = 0 :=
  prime_nat_valuation_zero (by decide) hp3

end
end Li2

end
