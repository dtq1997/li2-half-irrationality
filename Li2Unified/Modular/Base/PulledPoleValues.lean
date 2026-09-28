module
public import Li2Unified.Modular.Base.DissectedSquare

set_option backward.privateInPublic true

@[expose] public section

/-! Identify each independently constructed square term with the U/V
contribution of the pulled-back simple pole 1/(pu+j-a). Matching factors
are scaled simple poles; nonmatching factors are actual restricted inverses. -/
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma polePullback_index (j a : ℕ) (ha : a < p) :
    j+(p-1-a)+1+a = j+p := by omega

lemma polePullback_denominator (j a : ℕ) (ha : a < p) :
    (((j+(p-1-a)+1:ℕ):ℚ)-(p:ℚ))+(a:ℚ) = (j:ℚ) := by
  have h := congrArg (fun n : ℕ => (n:ℚ)) (polePullback_index j a ha)
  push_cast at h ⊢
  linarith

end
end Li2

end
