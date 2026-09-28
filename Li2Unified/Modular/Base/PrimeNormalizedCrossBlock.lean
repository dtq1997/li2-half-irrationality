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

theorem primeNormalizedMatrix_low_cross_GV (hp4 : 3 < p)
    (a b : Fin (p-4)) (i j : Fin 2) (hab : a ≠ b) :
    GV p (primeNormalizedMatrix hp4 (Sum.inl (a,i)) (Sum.inl (b,j)))
      (primeBlockWeight (Sum.inl (a,i)) + primeBlockWeight (Sum.inl (b,j)) + 1) := by
  apply primeNormalizedMatrix_GV_of_original hp4
  have h := (primeOriginalBasis_low_cross_GV_strict hp4
    ((primeOriginalBlockEquiv hp4).symm (Sum.inl (a,i)))
    ((primeOriginalBlockEquiv hp4).symm (Sum.inl (b,j)))
    (primeLowBlockJet hp4 a i).1 (primeLowBlockJet hp4 b j).1
    (primeLowBlock_pos hp4 a i) (primeLowBlock_le hp4 a i)
    (primeLowBlock_pos hp4 b j) (primeLowBlock_le hp4 b j)
    (primeLowBlock_ne hp4 a b i j hab)
    (primeLowBlockJet hp4 a i).2 (primeLowBlockJet hp4 b j).2
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeLowBlockJet hp4 a i) rfl)
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeLowBlockJet hp4 b j) rfl)).1
  simpa only [primeBlockWeight_low,primeLowBlockJet,Fin.val_mk] using h

theorem primeNormalizedMatrix_low_zero_GV (hp4 : 3 < p)
    (a : Fin (p-4)) (i j : Fin 2) :
    GV p (primeNormalizedMatrix hp4 (Sum.inl (a,i)) (Sum.inr (primeZeroEdgeSlot j)))
      (primeBlockWeight (Sum.inl (a,i)) +
        primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot j)) + (3/2-(i.val:ℚ))) := by
  apply primeNormalizedMatrix_GV_of_original hp4
  have h := (primeOriginalBasis_low_zero_GV_strict hp4
    ((primeOriginalBlockEquiv hp4).symm (Sum.inl (a,i)))
    ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeZeroEdgeSlot j)))
    (primeLowBlockJet hp4 a i).1 (primeZeroBlockJet hp4 j).1
    (primeLowBlock_pos hp4 a i) (primeLowBlock_le hp4 a i) rfl
    (primeLowBlockJet hp4 a i).2 (primeZeroBlockJet hp4 j).2
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeLowBlockJet hp4 a i) rfl)
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeZeroBlockJet hp4 j)
      (primeZeroEdgeSlot_encode hp4 j))).1
  simpa only [primeBlockWeight_low,primeBlockWeight_zeroSlot,
    primeLowBlockJet,primeZeroBlockJet,Fin.val_mk] using h

theorem primeNormalizedMatrix_low_high_GV (hp4 : 3 < p)
    (a : Fin (p-4)) (i : Fin 2) (ell : Fin 3) :
    GV p (primeNormalizedMatrix hp4 (Sum.inl (a,i)) (Sum.inr (primeHighEdgeSlot ell)))
      (primeBlockWeight (Sum.inl (a,i)) +
        primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) + (3/2-(i.val:ℚ))) := by
  apply primeNormalizedMatrix_GV_of_original hp4
  have h := (primeOriginalBasis_low_high_GV_strict hp4
    ((primeOriginalBlockEquiv hp4).symm (Sum.inl (a,i)))
    ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot ell)))
    (primeLowBlockJet hp4 a i).1 (primeHighBlockJet hp4 ell).1
    (primeLowBlock_pos hp4 a i) (primeLowBlock_le hp4 a i)
    (primeHighBlock_above hp4 ell)
    (primeLowBlockJet hp4 a i).2 (primeHighBlockJet hp4 ell).2
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeLowBlockJet hp4 a i) rfl)
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeHighBlockJet hp4 ell)
      (primeHighEdgeSlot_encode hp4 ell))).1
  simpa only [primeBlockWeight_low,primeBlockWeight_highSlot,
    primeLowBlockJet,Fin.val_mk] using h

theorem primeNormalizedMatrix_zero_high_GV (hp4 : 3 < p)
    (i : Fin 2) (ell : Fin 3) :
    GV p (primeNormalizedMatrix hp4
      (Sum.inr (primeZeroEdgeSlot i)) (Sum.inr (primeHighEdgeSlot ell)))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) + 1) := by
  apply primeNormalizedMatrix_GV_of_original hp4
  have h := (primeOriginalBasis_zero_high_GV_strict hp4
    ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeZeroEdgeSlot i)))
    ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot ell)))
    (primeZeroBlockJet hp4 i).1 (primeHighBlockJet hp4 ell).1 rfl
    (primeHighBlock_above hp4 ell)
    (primeZeroBlockJet hp4 i).2 (primeHighBlockJet hp4 ell).2
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeZeroBlockJet hp4 i)
      (primeZeroEdgeSlot_encode hp4 i))
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeHighBlockJet hp4 ell)
      (primeHighEdgeSlot_encode hp4 ell))).1
  simpa only [primeBlockWeight_zeroSlot,primeBlockWeight_highSlot,
    primeZeroBlockJet,Fin.val_mk] using h

theorem primeNormalizedMatrix_high_cross_GV (hp4 : 3 < p)
    (ell m : Fin 3) (hem : ell ≠ m) :
    GV p (primeNormalizedMatrix hp4
      (Sum.inr (primeHighEdgeSlot ell)) (Sum.inr (primeHighEdgeSlot m)))
      (primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
        primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot m)) + 1) := by
  apply primeNormalizedMatrix_GV_of_original hp4
  have h := (primeOriginalBasis_high_cross_GV_strict hp4
    ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot ell)))
    ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot m)))
    (primeHighBlockJet hp4 ell).1 (primeHighBlockJet hp4 m).1
    (primeHighBlock_above hp4 ell) (primeHighBlock_above hp4 m)
    (primeHighBlock_ne hp4 ell m hem)
    (primeHighBlockJet hp4 ell).2 (primeHighBlockJet hp4 m).2
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeHighBlockJet hp4 ell)
      (primeHighEdgeSlot_encode hp4 ell))
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeHighBlockJet hp4 m)
      (primeHighEdgeSlot_encode hp4 m))).1
  simpa only [primeBlockWeight_highSlot] using h

theorem primeNormalizedMatrix_top_low_GV (hp4 : 3 < p)
    (a : Fin (p-4)) (i : Fin 2) :
    GV p (primeNormalizedMatrix hp4 (Sum.inr 5) (Sum.inl (a,i)))
      (primeBlockWeight (p := p) (Sum.inr 5) +
        primeBlockWeight (Sum.inl (a,i)) + 1/2) := by
  apply primeNormalizedMatrix_GV_of_original hp4
  rw [primeOriginalBlockEquiv_symm_top]
  have h := (primeOriginalBasis_top_low_GV_strict hp4
    ((primeOriginalBlockEquiv hp4).symm (Sum.inl (a,i)))
    (primeLowBlockJet hp4 a i).1
    (primeLowBlock_pos hp4 a i) (primeLowBlock_le hp4 a i)
    (primeLowBlockJet hp4 a i).2
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeLowBlockJet hp4 a i) rfl)).1
  simpa only [primeBlockWeight_top,primeBlockWeight_low,
    primeLowBlockJet,Fin.val_mk] using h

theorem primeNormalizedMatrix_low_edge_GV (hp4 : 3 < p)
    (a : Fin (p-4)) (i : Fin 2) (k : Fin 6) :
    GV p (primeNormalizedMatrix hp4 (Sum.inl (a,i)) (Sum.inr k))
      (primeBlockWeight (Sum.inl (a,i)) + primeBlockWeight (p := p) (Sum.inr k) + 1/2) := by
  have hi : (i.val:ℚ) ≤ 1 := by
    have h : i.val ≤ 1 := by have h := i.isLt; omega
    exact_mod_cast h
  rcases primeEdgeSlot_cases k with ⟨ell,rfl⟩ | ⟨j,rfl⟩ | rfl
  · exact (primeNormalizedMatrix_low_high_GV hp4 a i ell).mono (by linarith)
  · exact (primeNormalizedMatrix_low_zero_GV hp4 a i j).mono (by linarith)
  · rw [primeNormalizedMatrix_symm hp4 (Sum.inl (a,i)) (Sum.inr 5)]
    simpa only [add_comm] using primeNormalizedMatrix_top_low_GV hp4 a i

end
end Li2

end
