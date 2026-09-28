module
public import Li2Unified.Modular.Base.PrimeGlobalDissection

set_option backward.privateInPublic true

@[expose] public section

/-! Both jets vanish to the full local multiplicity on each other disc. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem primeJet_same_other_product_factor (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) (b : Fin p) (hb : b ≠ a) :
    ∃ E : ℤ[X], (primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩).comp
      (primeDiscSubstitution p b) = C ((p:ℤ)^(2*primeMultiplicity p b))*E := by
  obtain ⟨A,hA⟩ := primeJetPoly_other_expansion p ⟨a,i⟩ b hb
  obtain ⟨B,hB⟩ := primeJetPoly_other_expansion p ⟨a,j⟩ b hb
  refine ⟨X^(2*primeMultiplicity p b)*(A*B),?_⟩
  rw [mul_comp,hA,hB]
  simp only [two_mul,pow_add,C_mul]
  ring

end
end Li2

end
