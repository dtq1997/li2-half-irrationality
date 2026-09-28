module
public import Li2Unified.Modular.Base.PulledPoleValues
public import Li2Unified.Modular.Base.PrimePoleExtension

set_option backward.privateInPublic true

@[expose] public section

/-! In the literal prime-edge pole range, every matching local pole is one of
0,-1,-2,-3. Its U/V values are those of the existing bounded extension. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeMatchingPoleIndex_lt (j a : ℕ) (hj : j ≤ 4*p-4) (ha : a < p)
    (hm : p ∣ j+(p-1-a)+1) : (j+(p-1-a)+1)/p-1 < 4 := by
  have hpos : 0 < (j+(p-1-a)+1)/p :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hm) hp.out.pos
  have hlt : (j+(p-1-a)+1)/p < 5 := by
    apply (Nat.div_lt_iff_lt_mul hp.out.pos).mpr
    have hpp := hp.out.two_le
    omega
  omega

def primeMatchingPoleIndex (j a : ℕ) (hj : j ≤ 4*p-4) (ha : a < p)
    (hm : p ∣ j+(p-1-a)+1) : Fin 4 :=
  ⟨(j+(p-1-a)+1)/p-1, primeMatchingPoleIndex_lt j a hj ha hm⟩

end
end Li2

end
