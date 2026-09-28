module
public import Li2Unified.Modular.Base.PrimeHighScaledBlock
public import Li2Unified.Modular.Base.PrimeZeroScaledBlock

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma primeBlockWeight_top :
    primeBlockWeight (p := p) (Sum.inr 5) = 1/2 := by
  rfl

lemma primeLowBlock_pos (hp4 : 3 < p) (a : Fin (p-4)) (i : Fin 2) :
    0 < (primeLowBlockJet hp4 a i).1.val := by
  change 0 < a.val+1
  omega

lemma primeLowBlock_le (hp4 : 3 < p) (a : Fin (p-4)) (i : Fin 2) :
    (primeLowBlockJet hp4 a i).1.val ≤ p-4 := by
  change a.val+1 ≤ p-4
  have ha := a.isLt
  omega

lemma primeLowBlock_ne (hp4 : 3 < p) (a b : Fin (p-4))
    (i j : Fin 2) (hab : a ≠ b) :
    (primeLowBlockJet hp4 a i).1 ≠ (primeLowBlockJet hp4 b j).1 := by
  intro he
  have hv := congrArg Fin.val he
  have hval : a.val+1 = b.val+1 := hv
  exact hab (Fin.ext (by omega))

lemma primeHighBlock_ne (hp4 : 3 < p) (ell m : Fin 3) (hem : ell ≠ m) :
    (primeHighBlockJet hp4 ell).1 ≠ (primeHighBlockJet hp4 m).1 := by
  intro he
  have hv := congrArg Fin.val he
  have hval : p-(ell.val+1) = p-(m.val+1) := hv
  have hl := ell.isLt
  have hm := m.isLt
  exact hem (Fin.ext (by omega))

lemma primeEdgeSlot_cases (k : Fin 6) :
    (∃ ell : Fin 3, k = primeHighEdgeSlot ell) ∨
    (∃ i : Fin 2, k = primeZeroEdgeSlot i) ∨ k = 5 := by
  fin_cases k
  · exact Or.inl ⟨0,rfl⟩
  · exact Or.inl ⟨1,rfl⟩
  · exact Or.inl ⟨2,rfl⟩
  · exact Or.inr (Or.inl ⟨0,rfl⟩)
  · exact Or.inr (Or.inl ⟨1,rfl⟩)
  · exact Or.inr (Or.inr rfl)

end
end Li2

end
