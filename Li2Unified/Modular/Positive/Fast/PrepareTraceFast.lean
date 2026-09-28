module
public import Li2Unified.Modular.Positive.Packed.P110
public import Li2Unified.Modular.Positive.Fast.TraceTrie

set_option backward.privateInPublic true

@[expose] public section
namespace Li2Unified.Proofs.Potential.CompactAffine

open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.ReflectionProgram

def prepareTraceFast (steps : List Step) : Option Prepared :=
  if Domain.fastCheckTrace 10 (point qZero) steps then
    (reifyTrace steps).map (fun env => ⟨steps.reverse, env⟩)
  else none

theorem prepareTraceFast_sound {steps : List Step} {p : Prepared}
    (h : prepareTraceFast steps = some p) : prepareTrace steps = some p := by
  unfold prepareTraceFast at h
  split at h
  · rename_i hfast
    have hc : Domain.checkTrace (point qZero) steps = true := Domain.fastCheckTrace_sound hfast
    simpa [prepareTrace, hc] using h
  · simp at h

end Li2Unified.Proofs.Potential.CompactAffine

end
