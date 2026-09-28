module
public import Li2Unified.Modular.Positive.Packed.P199
public import Li2Unified.Modular.Positive.Packed.P173
public import Li2Unified.Modular.Positive.Packed.P175

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Energy.CompactEnergy
open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.ReflectionProgram
open Li2Unified.Proofs.Potential.CompactAffine
noncomputable section

private theorem mapped_rat_sum_real {α : Type} (f : α → ℚ) (xs : List α) :
    (((xs.map f).sum : ℚ) : ℝ) = (xs.map (fun x => (f x : ℝ))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

end
end Li2Unified.Proofs.Energy.CompactEnergy

end

end
