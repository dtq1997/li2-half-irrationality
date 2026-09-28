module
public import Li2Unified.Modular.Base.RationalPoleCongruence

set_option backward.privateInPublic true

@[expose] public section

/-! Every coefficient of the rational four-pole functional is congruent at
z=(-1/2)^p and z=-1/2, for p-integral regular part and residues. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma GV.mul_congr {A B C D : ℚ[X]} {s : ℚ}
    (hC : GV p C 0) (hB : GV p B 0)
    (hAB : GV p (A-B) s) (hCD : GV p (C-D) s) : GV p (A*C-B*D) s := by
  rw [show A*C-B*D = (A-B)*C+B*(C-D) by ring]
  have hleft : GV p ((A-B)*C) s := by simpa using hAB.mul hC
  have hright : GV p (B*(C-D)) s := by simpa using hB.mul hCD
  exact hleft.add hright

end
end Li2

end
