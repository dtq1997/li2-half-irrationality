module
public import Li2Unified.Modular.Base.PrimeNormalizedCrossBlock
public import Li2Unified.Modular.Base.PrimeLowScaledBlock
public import Li2Unified.Modular.Base.PrimeTopEntry
public import Li2Unified.Modular.Base.PrimeEdgeNormValues
public import Li2Unified.Modular.Base.PrimeZeroRationalLeading
public import Li2Unified.Modular.Base.PrimeNormalizedMatrix
public import Li2Unified.Modular.Base.PrimeLowWeightUnit
public import Mathlib.Tactic.NormNum.GCD

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeReference_not_dvd_72 (hp4 : 3 < p) : ¬ p ∣ 72 := by
  have h2 : ¬ p ∣ 2 := by
    intro h
    have hh := Nat.le_of_dvd (by decide : 0 < 2) h
    omega
  have h3 : ¬ p ∣ 3 := by
    intro h
    have hh := Nat.le_of_dvd (by decide : 0 < 3) h
    omega
  rw [show (72:ℕ) = 2^3*3^2 by norm_num]
  intro h
  rcases hp.out.dvd_mul.mp h with h | h
  · exact h2 (hp.out.dvd_of_dvd_pow h)
  · exact h3 (hp.out.dvd_of_dvd_pow h)

lemma primeReference_rational_VG (hp4 : 3 < p) (q : ℚ) (hden : q.den ∣ 72) :
    VG p q 0 := by
  have hn : ¬ p ∣ q.den := fun h => primeReference_not_dvd_72 hp4 (dvd_trans h hden)
  right
  rw [padicValRat_def,padicValNat.eq_zero_of_not_dvd hn,Nat.cast_zero,sub_zero]
  positivity

end
end Li2

end
