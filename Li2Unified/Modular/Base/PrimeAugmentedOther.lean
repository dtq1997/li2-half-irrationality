module
public import Li2Unified.Modular.Base.PrimeAugmentedJets
public import Li2Unified.Modular.Base.PrimeLowEntry

set_option backward.privateInPublic true

@[expose] public section

/-! Other-disc estimates also include the original appended product. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem primeAugmentedJet_other_factor (a : Fin p) (i : Fin (primeMultiplicity p a+1))
    (b : Fin p) (hb : b ≠ a) :
    ∃ A : ℤ[X], (primeAugmentedJet p a i).comp (primeDiscSubstitution p b) =
      C ((p:ℤ)^(primeMultiplicity p b))*X^(primeMultiplicity p b)*A := by
  by_cases hi : i.val < primeMultiplicity p a
  · rw [primeAugmentedJet_of_lt p a i hi]
    exact primeJetPoly_other_expansion p ⟨a,⟨i.val,hi⟩⟩ b hb
  · rw [primeAugmentedJet,dif_neg hi]
    obtain ⟨A,hA⟩ := primeProduct_expansion p b
    exact ⟨C (primeLocalUnit p b)+C (p:ℤ)*A,hA⟩

theorem primeAugmentedJet_other_product_factor (a : Fin p)
    (i j : Fin (primeMultiplicity p a+1)) (b : Fin p) (hb : b ≠ a) :
    ∃ E : ℤ[X], (primeAugmentedJet p a i*primeAugmentedJet p a j).comp
      (primeDiscSubstitution p b) = C ((p:ℤ)^(2*primeMultiplicity p b))*E := by
  obtain ⟨A,hA⟩ := primeAugmentedJet_other_factor a i b hb
  obtain ⟨B,hB⟩ := primeAugmentedJet_other_factor a j b hb
  refine ⟨X^(2*primeMultiplicity p b)*(A*B),?_⟩
  rw [mul_comp,hA,hB]
  simp only [two_mul,pow_add,C_mul]
  ring

end
end Li2

end
