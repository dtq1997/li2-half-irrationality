module
public import Li2Unified.Modular.Base.PrimeActualLowLeading

set_option backward.privateInPublic true

@[expose] public section

/-! Local indexing of the original product jets with the original top-degree
product appended. This does not change the globally fixed basis ordering. -/
open Polynomial
namespace Li2
noncomputable section

def primeAugmentedJet (p : ℕ) (a : Fin p) (i : Fin (primeMultiplicity p a+1)) : ℤ[X] :=
  if h : i.val < primeMultiplicity p a then primeJetPoly p ⟨a,⟨i.val,h⟩⟩ else primeProduct p

lemma primeAugmentedJet_of_lt (p : ℕ) (a : Fin p) (i : Fin (primeMultiplicity p a+1))
    (hi : i.val < primeMultiplicity p a) :
    primeAugmentedJet p a i = primeJetPoly p ⟨a,⟨i.val,hi⟩⟩ := by
  simp only [primeAugmentedJet,dif_pos hi]

theorem primeAugmentedJet_expansion (p : ℕ) (a : Fin p) (i : Fin (primeMultiplicity p a+1)) :
    ∃ E : ℤ[X], (primeAugmentedJet p a i).comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^i.val)*X^i.val*(C (primeLocalUnit p a)+C (p:ℤ)*E) := by
  by_cases hi : i.val < primeMultiplicity p a
  · rw [primeAugmentedJet_of_lt p a i hi]
    exact primeJetPoly_own_expansion p ⟨a,⟨i.val,hi⟩⟩
  · have he : i.val = primeMultiplicity p a := by have h := i.isLt; omega
    rw [primeAugmentedJet,dif_neg hi,he]
    exact primeProduct_expansion p a

theorem primeAugmentedJet_product_expansion (p : ℕ) (a : Fin p)
    (i j : Fin (primeMultiplicity p a+1)) :
    ∃ E : ℤ[X], (primeAugmentedJet p a i*primeAugmentedJet p a j).comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^(i.val+j.val))*X^(i.val+j.val)*
        (C (primeLocalUnit p a*primeLocalUnit p a)+C (p:ℤ)*E) := by
  rw [mul_comp]
  exact integerProductJet_expansion p i.val j.val _ _ _ _
    (primeAugmentedJet_expansion p a i) (primeAugmentedJet_expansion p a j)

variable {p : ℕ} [Fact p.Prime]

lemma primeAugmented_zero_pair_lt_five (hp4 : 3 < p)
    (i j : Fin (primeMultiplicity p ⟨0,by omega⟩+1)) : i.val+j.val < 5 := by
  have hm := primeMultiplicity_low hp4 (⟨0,by omega⟩:Fin p) (by simp)
  have hi := i.isLt
  have hj := j.isLt
  omega

lemma primeAugmented_high_pair_lt_three (hp4 : 3 < p) (a : Fin p)
    (ha : p-4 < a.val) (i j : Fin (primeMultiplicity p a+1)) : i.val+j.val < 3 := by
  have hm : primeMultiplicity p a = 1 := by unfold primeMultiplicity; rw [if_neg (by omega)]
  have hi := i.isLt
  have hj := j.isLt
  omega

end
end Li2

end
