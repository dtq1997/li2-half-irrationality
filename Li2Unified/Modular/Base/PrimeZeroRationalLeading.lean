module
public import Li2Unified.Modular.Base.PrimeAugmentedOther
public import Li2Unified.Modular.Base.PrimeEdgeNormValues
public import Li2Unified.Modular.Base.PrimeLowRationalLeading
public import Li2Unified.Modular.Base.PrimeBlockIndex

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def primeZeroAugmentedIndex (hp4 : 3 < p) (i : Fin 3) :
    Fin (primeMultiplicity p ⟨0,by omega⟩+1) :=
  ⟨i.val,by
    have hm := primeMultiplicity_low hp4 (⟨0,by omega⟩ : Fin p) (by simp)
    have hi := i.isLt
    omega⟩

def primeZeroBlockPoly (hp4 : 3 < p) (i : Fin 3) : ℤ[X] :=
  primeAugmentedJet p ⟨0,by omega⟩ (primeZeroAugmentedIndex hp4 i)

lemma primeZeroBlockPoly_jet (hp4 : 3 < p) (i : Fin 2) :
    primeZeroBlockPoly hp4 i.castSucc = primeJetPoly p (primeZeroBlockJet hp4 i) := by
  simp [primeZeroBlockPoly,primeZeroAugmentedIndex,primeAugmentedJet,
    primeZeroBlockJet,primeMultiplicity,show 0 < p-3 by omega,i.isLt]

lemma primeZeroBlockPoly_top (hp4 : 3 < p) :
    primeZeroBlockPoly hp4 2 = primeProduct p := by
  simp [primeZeroBlockPoly,primeZeroAugmentedIndex,primeAugmentedJet,
    primeMultiplicity,show 0 < p-3 by omega]

theorem GV_of_cube_padic_leading_bound (F : ℚ[X]) (r : ℚ) (k : ℕ)
    (h : ∀ n, ‖(C ((p:ℚ_[p])^3)*F.map (Rat.castHom ℚ_[p]) -
      C ((p:ℚ_[p])^k*(r:ℚ_[p]))).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(k+1)) :
    GV p (F-C ((p:ℚ)^((k:ℤ)-3)*r)) ((k:ℚ)-2) := by
  let E := F-C ((p:ℚ)^((k:ℤ)-3)*r)
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpow : (p:ℚ_[p])^3*(p:ℚ_[p])^((k:ℤ)-3) = (p:ℚ_[p])^k := by
    rw [zpow_sub₀ hp0,zpow_natCast,zpow_ofNat]
    field_simp <;> ring
  have he : C ((p:ℚ_[p])^3)*E.map (Rat.castHom ℚ_[p]) =
      C ((p:ℚ_[p])^3)*F.map (Rat.castHom ℚ_[p]) -
        C ((p:ℚ_[p])^k*(r:ℚ_[p])) := by
    simp only [E,Polynomial.map_sub,Polynomial.map_C,Rat.coe_castHom,
      Rat.cast_mul,Rat.cast_zpow,Rat.cast_natCast]
    rw [mul_sub,← C_mul,← mul_assoc,hpow]
  have hE := GV_of_cube_padic_norm_bound E (k+1) (by
    intro n
    rw [he]
    exact h n)
  exact hE.mono (by push_cast <;> linarith)

end
end Li2

end
