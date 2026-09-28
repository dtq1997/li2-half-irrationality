module
public import Li2Unified.Modular.Base.PrimeProductJets
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ}

abbrev PrimeBlockIndex (p : ℕ) := (Fin (p-4) × Fin 2) ⊕ Fin 6

def primeLowBlockJet (hp4 : 3 < p) (a : Fin (p-4)) (i : Fin 2) : PrimeJet p :=
  ⟨⟨a.val+1,by have h := a.isLt; omega⟩,
    ⟨i.val,by
      have h := a.isLt
      simpa only [primeMultiplicity,Fin.val_mk,
        if_pos (by omega : a.val+1 < p-3)] using i.isLt⟩⟩

def primeHighBlockJet (hp4 : 3 < p) (ell : Fin 3) : PrimeJet p :=
  ⟨⟨p-(ell.val+1),by have h := ell.isLt; omega⟩,
    ⟨0,by unfold primeMultiplicity; split_ifs <;> omega⟩⟩

def primeZeroBlockJet (hp4 : 3 < p) (i : Fin 2) : PrimeJet p :=
  ⟨⟨0,by omega⟩,
    ⟨i.val,by
      simpa only [primeMultiplicity,Fin.val_mk,
        if_pos (by omega : 0 < p-3)] using i.isLt⟩⟩

/-- High1, high2, high3, zero0, zero1, and the original top G. -/
def primeEdgeBlockJet (hp4 : 3 < p) : Fin 6 → Option (PrimeJet p) :=
  ![some (primeHighBlockJet hp4 0), some (primeHighBlockJet hp4 1),
    some (primeHighBlockJet hp4 2), some (primeZeroBlockJet hp4 0),
    some (primeZeroBlockJet hp4 1), none]

def primeBlockToJet (hp4 : 3 < p) : PrimeBlockIndex p → Option (PrimeJet p)
  | Sum.inl ai => some (primeLowBlockJet hp4 ai.1 ai.2)
  | Sum.inr k => primeEdgeBlockJet hp4 k

def primeBlockFromJet (hp4 : 3 < p) : Option (PrimeJet p) → PrimeBlockIndex p
  | none => Sum.inr 5
  | some a =>
      if hz : a.1.val = 0 then
        Sum.inr ⟨3+a.2.val,by
          have hi := a.2.isLt
          have hm : primeMultiplicity p a.1 = 2 := by
            simp only [primeMultiplicity,hz,if_pos (by omega : 0 < p-3)]
          omega⟩
      else if hl : a.1.val ≤ p-4 then
        Sum.inl (⟨a.1.val-1,by omega⟩,⟨a.2.val,by
          have hi := a.2.isLt
          have hm : primeMultiplicity p a.1 = 2 := by
            unfold primeMultiplicity
            rw [if_pos (by omega)]
          omega⟩)
      else
        Sum.inr ⟨p-a.1.val-1,by have ha := a.1.isLt; omega⟩

theorem primeBlockFromJet_toJet (hp4 : 3 < p) :
    Function.LeftInverse (primeBlockFromJet hp4) (primeBlockToJet hp4) := by
  intro x
  rcases x with ⟨a,i⟩ | k
  · have ha := a.isLt
    have h0 : a.val+1 ≠ 0 := by omega
    have hL : a.val+1 ≤ p-4 := by omega
    simp only [primeBlockToJet,primeLowBlockJet,primeBlockFromJet,
      Fin.val_mk,dif_neg h0,dif_pos hL]
    apply congrArg Sum.inl
    exact Prod.ext (Fin.ext (by dsimp only; omega)) (Fin.ext rfl)
  · have h10 : p-1 ≠ 0 := by omega
    have h20 : p-2 ≠ 0 := by omega
    have h30 : p-3 ≠ 0 := by omega
    have h1L : ¬ p-1 ≤ p-4 := by omega
    have h2L : ¬ p-2 ≤ p-4 := by omega
    have h3L : ¬ p-3 ≤ p-4 := by omega
    have hr1 : p-(p-1)-1 = 0 := by omega
    have hr2 : p-(p-2)-1 = 1 := by omega
    have hr3 : p-(p-3)-1 = 2 := by omega
    fin_cases k <;>
      norm_num [primeBlockToJet,primeEdgeBlockJet,primeHighBlockJet,
        primeZeroBlockJet,primeBlockFromJet,h10,h20,h30,h1L,h2L,h3L,
        hr1,hr2,hr3,Fin.ext_iff]

def primeBlockJetEquiv (hp4 : 3 < p) : PrimeBlockIndex p ≃ Option (PrimeJet p) where
  toFun := primeBlockToJet hp4
  invFun := primeBlockFromJet hp4
  left_inv := primeBlockFromJet_toJet hp4
  right_inv := by
    have hc : Fintype.card (PrimeBlockIndex p) = Fintype.card (Option (PrimeJet p)) := by
      simp only [PrimeBlockIndex,Fintype.card_sum,Fintype.card_prod,
        Fintype.card_fin,Fintype.card_option,primeJet_card p (by omega)]
      omega
    have hb : Function.Bijective (primeBlockToJet hp4) :=
      (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨(primeBlockFromJet_toJet hp4).injective,hc⟩
    intro a
    obtain ⟨x,rfl⟩ := hb.2 a
    rw [primeBlockFromJet_toJet hp4]

/-- Preserve the arbitrary original jet enumeration and original index zero for G. -/
def primeOriginalBlockEquiv (hp4 : 3 < p) :
    Fin (2*(p-1)) ≃ PrimeBlockIndex p :=
  (finCongr (primeBasisSize p (by omega))).trans
    ((finSuccEquiv (2*p-3)).trans
      ((Equiv.optionCongr (primeJetEquiv p (by omega))).trans
        (primeBlockJetEquiv hp4).symm))

lemma primeOriginalBlockEquiv_symm_full (hp4 : 3 < p) (x : PrimeBlockIndex p) :
    finCongr (primeBasisSize p (by omega)) ((primeOriginalBlockEquiv hp4).symm x) =
      (finSuccEquiv (2*p-3)).symm
        (Option.map (primeJetEquiv p (by omega)).symm (primeBlockToJet hp4 x)) := by
  simp only [primeOriginalBlockEquiv,Equiv.symm_trans_apply,Equiv.apply_symm_apply] <;> rfl

lemma primeOriginalBlockEquiv_symm_jet (hp4 : 3 < p)
    (x : PrimeBlockIndex p) (a : PrimeJet p) (hx : primeBlockToJet hp4 x = some a) :
    finCongr (primeBasisSize p (by omega)) ((primeOriginalBlockEquiv hp4).symm x) =
      ((primeJetEquiv p (by omega)).symm a).succ := by
  rw [primeOriginalBlockEquiv_symm_full,hx]
  simp

@[simp] lemma primeOriginalBlockEquiv_symm_top (hp4 : 3 < p) :
    (primeOriginalBlockEquiv hp4).symm (Sum.inr 5) =
      (⟨0,by omega⟩ : Fin (2*(p-1))) := by
  apply (finCongr (primeBasisSize p (by omega))).injective
  rw [primeOriginalBlockEquiv_symm_full]
  change (finSuccEquiv (2*p-3)).symm
    (Option.map (primeJetEquiv p (by omega)).symm
      (primeBlockToJet hp4 (Sum.inr 5))) = 0
  simp [primeBlockToJet,primeEdgeBlockJet]

@[simp] lemma primeOriginalBlockEquiv_zero (hp4 : 3 < p) :
    primeOriginalBlockEquiv hp4 (⟨0,by omega⟩ : Fin (2*(p-1))) = Sum.inr 5 := by
  apply (primeOriginalBlockEquiv hp4).apply_eq_iff_eq_symm_apply.mpr
  exact (primeOriginalBlockEquiv_symm_top hp4).symm

lemma primeBlock_original_basis_jet (hp4 : 3 < p)
    (x : PrimeBlockIndex p) (a : PrimeJet p) (hx : primeBlockToJet hp4 x = some a) :
    primeOriginalBasis p (by omega) ((primeOriginalBlockEquiv hp4).symm x) =
      primeJetPoly p a := by
  unfold primeOriginalBasis
  rw [primeOriginalBlockEquiv_symm_jet hp4 x a hx]
  simp only [primeFullBasis,Fin.cases_succ,primeIndexedPoly,Equiv.apply_symm_apply]

lemma primeBlock_original_basis_top (hp4 : 3 < p) :
    primeOriginalBasis p (by omega) ((primeOriginalBlockEquiv hp4).symm (Sum.inr 5)) =
      primeProduct p := by
  rw [primeOriginalBlockEquiv_symm_top]
  unfold primeOriginalBasis
  have hz : finCongr (primeBasisSize p (by omega))
      (⟨0,by omega⟩ : Fin (2*(p-1))) = 0 := Fin.ext rfl
  rw [hz]
  rfl

def primeEdgeIntegerWeight : Fin 6 → ℤ := ![-1,-1,-1,-2,-1,0]

def primeBlockWeight : PrimeBlockIndex p → ℚ
  | Sum.inl ai => (ai.2.val : ℚ)-1
  | Sum.inr k => ![-1/2,-1/2,-1/2,-3/2,-1/2,1/2] k

lemma primeBlockWeight_low (a : Fin (p-4)) (i : Fin 2) :
    primeBlockWeight (Sum.inl (a,i)) = (i.val : ℚ)-1 := rfl

lemma primeBlockWeight_edge (k : Fin 6) :
    primeBlockWeight (p := p) (Sum.inr k) = (primeEdgeIntegerWeight k : ℚ)+1/2 := by
  fin_cases k <;> norm_num [primeBlockWeight,primeEdgeIntegerWeight]

theorem primeBlockWeight_sum (hp4 : 3 < p) :
    (∑ x : PrimeBlockIndex p, primeBlockWeight x) = -((p-1 : ℕ) : ℚ) := by
  have hl : (∑ ai : Fin (p-4) × Fin 2, ((ai.2.val : ℚ)-1)) = -((p-4 : ℕ) : ℚ) := by
    rw [Fintype.sum_prod_type]
    simp [Fin.sum_univ_two] <;> ring
  have hr : (∑ k : Fin 6, primeBlockWeight (p := p) (Sum.inr k)) = -3 := by
    norm_num [primeBlockWeight,Fin.sum_univ_succ]
  rw [Fintype.sum_sum_type]
  change (∑ ai : Fin (p-4) × Fin 2, ((ai.2.val : ℚ)-1)) +
    (∑ k : Fin 6, primeBlockWeight (p := p) (Sum.inr k)) = _
  rw [hl,hr]
  have h4 : ((p-4 : ℕ) : ℚ) = (p : ℚ)-4 := Nat.cast_sub (by omega)
  have h1 : ((p-1 : ℕ) : ℚ) = (p : ℚ)-1 := Nat.cast_sub (by omega)
  rw [h4,h1]
  ring

/-- Only jet vectors are divided by actual product-basis local units; G is unchanged. -/
def primeBlockUnitScale (hp4 : 3 < p) (x : PrimeBlockIndex p) : ℚ :=
  match primeBlockToJet hp4 x with
  | none => 1
  | some a => (primeLocalUnit p a.1 : ℚ)⁻¹

lemma primeBlockUnitScale_jet (hp4 : 3 < p) (x : PrimeBlockIndex p)
    (a : PrimeJet p) (hx : primeBlockToJet hp4 x = some a) :
    primeBlockUnitScale hp4 x = (primeLocalUnit p a.1 : ℚ)⁻¹ := by
  simp only [primeBlockUnitScale,hx]

@[simp] lemma primeBlockUnitScale_top (hp4 : 3 < p) :
    primeBlockUnitScale hp4 (Sum.inr 5) = 1 := by
  simp [primeBlockUnitScale,primeBlockToJet,primeEdgeBlockJet]

theorem primeBlockUnitScale_unit [Fact p.Prime] (hp4 : 3 < p) (x : PrimeBlockIndex p) :
    primeBlockUnitScale hp4 x ≠ 0 ∧ padicValRat p (primeBlockUnitScale hp4 x) = 0 := by
  cases h : primeBlockToJet hp4 x with
  | none => simp [primeBlockUnitScale,h]
  | some a =>
      have hu := primeLocalUnit_unit p a.1
      constructor
      · simpa only [primeBlockUnitScale,h] using inv_ne_zero hu.1
      · simp only [primeBlockUnitScale,h,padicValRat.inv,hu.2,neg_zero]

end
end Li2

end
