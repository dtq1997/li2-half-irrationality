module
public import Li2Unified.Modular.Positive.Packed.P013
public import Li2Unified.Modular.Positive.Packed.P014
public import Li2Unified.Modular.Base.OriginalPulledRepresentation

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- Every matching original pole lies at the distinct center `-j/p` among
the `p` available centers. -/
def generalPulledPoleResidue (m j : ℕ) (hm : m < p * p)
    (hj : j ≤ m) (a : Fin p) : Fin p → ℚ_[p] :=
  if hmod : j % p = a.val then
    Pi.single (generalMatchingPoleIndex p m j a (Fact.out : p.Prime).pos hm hj hmod)
      (p : ℚ_[p])⁻¹
  else 0

theorem generalPulledPoleResidue_matching (m j : ℕ) (hm : m < p * p)
    (hj : j ≤ m) (a : Fin p) (hmod : j % p = a.val) :
    generalPulledPoleResidue m j hm hj a =
      Pi.single (generalMatchingPoleIndex p m j a (Fact.out : p.Prime).pos hm hj hmod)
        (p : ℚ_[p])⁻¹ := by
  simp [generalPulledPoleResidue, hmod]

theorem generalPulledPoleResidue_nonmatching (m j : ℕ) (hm : m < p * p)
    (hj : j ≤ m) (a : Fin p) (hmod : j % p ≠ a.val) :
    generalPulledPoleResidue m j hm hj a = 0 := by
  simp [generalPulledPoleResidue, hmod]

def generalOriginalPulledResidue (m : ℕ) (hm : m < p * p)
    (F : ℚ[X]) (a : Fin p) : Fin p → ℚ_[p] :=
  fun k => ∑ j : ↥(Finset.Icc 1 m),
    (originalResidue m F j.val : ℚ_[p]) *
      generalPulledPoleResidue m j.val hm (Finset.mem_Icc.mp j.property).2 a k

#print axioms generalPulledPoleResidue_matching
#print axioms generalPulledPoleResidue_nonmatching

end
end Li2Unified.Proofs.Hermite

end


end
