module
public import Li2Unified.Modular.Positive.Packed.P111
public import Li2Unified.Modular.Positive.Packed.P112
public import Li2Unified.Modular.Positive.Packed.P113
public import Li2Unified.Modular.Positive.Packed.P114
public import Li2Unified.Modular.Positive.Packed.P115
public import Li2Unified.Modular.Positive.Packed.P116
public import Li2Unified.Modular.Positive.Packed.P117
public import Li2Unified.Modular.Positive.Packed.P118
public import Li2Unified.Modular.Positive.Packed.P119
public import Li2Unified.Modular.Positive.Packed.P120
public import Li2Unified.Modular.Positive.Packed.P121
public import Li2Unified.Modular.Positive.Packed.P122
public import Li2Unified.Modular.Positive.Packed.P123
public import Li2Unified.Modular.Positive.Packed.P124
public import Li2Unified.Modular.Positive.Packed.P125
public import Li2Unified.Modular.Positive.Packed.P126
public import Li2Unified.Modular.Positive.Packed.P127
public import Li2Unified.Modular.Positive.Packed.P128
public import Li2Unified.Modular.Positive.Packed.P129
public import Li2Unified.Modular.Positive.Packed.P130
public import Li2Unified.Modular.Positive.Packed.P131
public import Li2Unified.Modular.Positive.Packed.P132
public import Li2Unified.Modular.Positive.Packed.P133
public import Li2Unified.Modular.Positive.Packed.P134
public import Li2Unified.Modular.Positive.Packed.P135
public import Li2Unified.Modular.Positive.Packed.P136
public import Li2Unified.Modular.Positive.Packed.P137
public import Li2Unified.Modular.Positive.Packed.P138
public import Li2Unified.Modular.Positive.Packed.P139
public import Li2Unified.Modular.Positive.Packed.P140
public import Li2Unified.Modular.Positive.Packed.P141
public import Li2Unified.Modular.Positive.Packed.P142
public import Li2Unified.Modular.Positive.Packed.P143
public import Li2Unified.Modular.Positive.Packed.P144
public import Li2Unified.Modular.Positive.Packed.P145
public import Li2Unified.Modular.Positive.Packed.P146
public import Li2Unified.Modular.Positive.Packed.P147
public import Li2Unified.Modular.Positive.Packed.P148
public import Li2Unified.Modular.Positive.Packed.P149
public import Li2Unified.Modular.Positive.Packed.P150
public import Li2Unified.Modular.Positive.Packed.P151
public import Li2Unified.Modular.Positive.Packed.P152
public import Li2Unified.Modular.Positive.Packed.P153
public import Li2Unified.Modular.Positive.Packed.P154
public import Li2Unified.Modular.Positive.Packed.P155
public import Li2Unified.Modular.Positive.Packed.P156
public import Li2Unified.Modular.Positive.Packed.P157
public import Li2Unified.Modular.Positive.Packed.P158
public import Li2Unified.Modular.Positive.Packed.P159
public import Li2Unified.Modular.Positive.Packed.P160
public import Li2Unified.Modular.Positive.Packed.P161
public import Li2Unified.Modular.Positive.Packed.P162

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Potential.CompactAffine
open Li2Unified.Proofs.Potential.KernelReflectionSelf

def halfRayBoxes : List BoxData := [
  rayCover000Data, rayCover001Data, rayCover002Data, rayCover003Data, rayCover004Data, rayCover005Data, rayCover006Data, rayCover007Data, rayCover008Data, rayCover009Data, rayCover010Data, rayCover011Data, rayCover012Data, rayCover013Data, rayCover014Data, rayCover015Data, rayCover016Data, rayCover017Data, rayCover018Data, rayCover019Data, rayCover020Data, rayCover021Data, rayCover022Data, rayCover023Data, rayCover024Data, rayCover025Data, rayCover026Data, rayCover027Data, rayCover028Data, rayCover029Data, rayCover030Data, rayCover031Data, rayCover032Data, rayCover033Data, rayCover034Data, rayCover035Data, rayCover036Data, rayCover037Data, rayCover038Data, rayCover039Data, rayCover040Data, rayCover041Data, rayCover042Data, rayCover043Data, rayCover044Data
]

theorem halfRayBoxes_checked : checkAll halfRayTerms ⟨19, 10⟩ halfRayBoxes = true := by
  simp only [halfRayBoxes, checkAll, Bool.and_eq_true]
  exact ⟨rayCover000Checked_true, ⟨rayCover001Checked_true, ⟨rayCover002Checked_true, ⟨rayCover003Checked_true, ⟨rayCover004Checked_true, ⟨rayCover005Checked_true, ⟨rayCover006Checked_true, ⟨rayCover007Checked_true, ⟨rayCover008Checked_true, ⟨rayCover009Checked_true, ⟨rayCover010Checked_true, ⟨rayCover011Checked_true, ⟨rayCover012Checked_true, ⟨rayCover013Checked_true, ⟨rayCover014Checked_true, ⟨rayCover015Checked_true, ⟨rayCover016Checked_true, ⟨rayCover017Checked_true, ⟨rayCover018Checked_true, ⟨rayCover019Checked_true, ⟨rayCover020Checked_true, ⟨rayCover021Checked_true, ⟨rayCover022Checked_true, ⟨rayCover023Checked_true, ⟨rayCover024Checked_true, ⟨rayCover025Checked_true, ⟨rayCover026Checked_true, ⟨rayCover027Checked_true, ⟨rayCover028Checked_true, ⟨rayCover029Checked_true, ⟨rayCover030Checked_true, ⟨rayCover031Checked_true, ⟨rayCover032Checked_true, ⟨rayCover033Checked_true, ⟨rayCover034Checked_true, ⟨rayCover035Checked_true, ⟨rayCover036Checked_true, ⟨rayCover037Checked_true, ⟨rayCover038Checked_true, ⟨rayCover039Checked_true, ⟨rayCover040Checked_true, ⟨rayCover041Checked_true, ⟨rayCover042Checked_true, ⟨rayCover043Checked_true, ⟨rayCover044Checked_true, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem halfRayBoxes_cover :
    coverFrom qZero ⟨18, 1⟩ (halfRayBoxes.map BoxData.box) = true := by
  decide +kernel

def halfUpBoxes : List BoxData := [
  upCover000Data, upCover001Data, upCover002Data, upCover003Data, upCover004Data, upCover005Data, upCover006Data
]

theorem halfUpBoxes_checked : checkAll halfUpTerms ⟨19, 10⟩ halfUpBoxes = true := by
  simp only [halfUpBoxes, checkAll, Bool.and_eq_true]
  exact ⟨upCover000Checked_true, ⟨upCover001Checked_true, ⟨upCover002Checked_true, ⟨upCover003Checked_true, ⟨upCover004Checked_true, ⟨upCover005Checked_true, ⟨upCover006Checked_true, True.intro⟩⟩⟩⟩⟩⟩⟩

theorem halfUpBoxes_cover :
    coverFrom qZero ⟨2, 1⟩ (halfUpBoxes.map BoxData.box) = true := by
  decide +kernel

end Li2Unified.Proofs.Potential.CompactAffine

end


end
