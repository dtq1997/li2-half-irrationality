module
public import Li2Unified.Modular.Base.PrimeJets
public import Li2Unified.Modular.Base.PrimeOriginalBasis

set_option backward.privateInPublic true

@[expose] public section

/-! Literal integer product expansions for two basis vectors on every disc.
The original basis has its top-degree vector first, as in PrimeBasisChange. -/
open Polynomial
namespace Li2
noncomputable section

theorem integerProductJet_expansion (p i j : ℕ) (c d : ℤ) (F G : ℤ[X])
    (hF : ∃ A : ℤ[X], F = C ((p:ℤ)^i)*X^i*(C c+C (p:ℤ)*A))
    (hG : ∃ B : ℤ[X], G = C ((p:ℤ)^j)*X^j*(C d+C (p:ℤ)*B)) :
    ∃ E : ℤ[X], F*G = C ((p:ℤ)^(i+j))*X^(i+j)*(C (c*d)+C (p:ℤ)*E) := by
  obtain ⟨A,rfl⟩ := hF
  obtain ⟨B,rfl⟩ := hG
  refine ⟨C c*B+C d*A+C (p:ℤ)*A*B,?_⟩
  simp only [pow_add, C_mul]
  ring

theorem primeJet_same_product_expansion (p : ℕ) (a : Fin p)
    (i j : Fin (primeMultiplicity p a)) :
    ∃ E : ℤ[X], (primeJetPoly p ⟨a,i⟩ * primeJetPoly p ⟨a,j⟩).comp
      (primeDiscSubstitution p a) =
      C ((p:ℤ)^(i.val+j.val))*X^(i.val+j.val)*
        (C (primeLocalUnit p a * primeLocalUnit p a)+C (p:ℤ)*E) := by
  rw [mul_comp]
  exact integerProductJet_expansion p i.val j.val _ _ _ _
    (primeJetPoly_own_expansion p ⟨a,i⟩) (primeJetPoly_own_expansion p ⟨a,j⟩)

theorem primeProduct_square_expansion (p : ℕ) (a : Fin p) :
    ∃ E : ℤ[X], (primeProduct p * primeProduct p).comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^(primeMultiplicity p a+primeMultiplicity p a))*
      X^(primeMultiplicity p a+primeMultiplicity p a)*
        (C (primeLocalUnit p a * primeLocalUnit p a)+C (p:ℤ)*E) := by
  rw [mul_comp]
  exact integerProductJet_expansion p _ _ _ _ _ _
    (primeProduct_expansion p a) (primeProduct_expansion p a)

def primeJetLocalOrder (p : ℕ) (a : PrimeJet p) (b : Fin p) : ℕ :=
  if b = a.1 then a.2.val else primeMultiplicity p b

theorem primeJet_disc_factor (p : ℕ) (a : PrimeJet p) (b : Fin p) :
    ∃ A : ℤ[X], (primeJetPoly p a).comp (primeDiscSubstitution p b) =
      C ((p:ℤ)^(primeJetLocalOrder p a b))*X^(primeJetLocalOrder p a b)*A := by
  by_cases he : b = a.1
  · subst b
    obtain ⟨A,hA⟩ := primeJetPoly_own_expansion p a
    exact ⟨C (primeLocalUnit p a.1)+C (p:ℤ)*A, by simpa [primeJetLocalOrder] using hA⟩
  · simpa [primeJetLocalOrder, he] using primeJetPoly_other_expansion p a b he

end
end Li2

end
