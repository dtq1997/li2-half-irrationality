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

def primeHighRationalLocalUnit : Fin 3 → ℚ := ![1/2,-1,1/2]

lemma primeHighBlock_above (hp4 : 3 < p) (ell : Fin 3) :
    p-4 < (primeHighBlockJet hp4 ell).1.val := by
  change p-4 < p-(ell.val+1)
  have hl := ell.isLt
  omega

lemma primeHighBlockMultiplicity (hp4 : 3 < p) (ell : Fin 3) :
    primeMultiplicity p (primeHighBlockJet hp4 ell).1 = 1 := by
  have hl := ell.isLt
  change (if p - (ell.val + 1) < p - 3 then 2 else 1) = 1
  rw [if_neg (by omega)]

def primeHighAugmentedIndex (hp4 : 3 < p) (ell : Fin 3) (i : Fin 2) :
    Fin (primeMultiplicity p (primeHighBlockJet hp4 ell).1+1) :=
  ⟨i.val,by
    have hm := primeHighBlockMultiplicity hp4 ell
    have hi := i.isLt
    omega⟩

def primeHighBlockPoly (hp4 : 3 < p) (ell : Fin 3) (i : Fin 2) : ℤ[X] :=
  primeAugmentedJet p (primeHighBlockJet hp4 ell).1
    (primeHighAugmentedIndex hp4 ell i)

lemma primeHighBlockPoly_jet (hp4 : 3 < p) (ell : Fin 3) :
    primeHighBlockPoly hp4 ell 0 = primeJetPoly p (primeHighBlockJet hp4 ell) := by
  simp only [primeHighBlockPoly,primeHighAugmentedIndex,primeAugmentedJet,Fin.val_mk]
  erw [dif_pos (by rw [primeHighBlockMultiplicity]; decide)]
  rfl

lemma primeHighBlockPoly_top (hp4 : 3 < p) (ell : Fin 3) :
    primeHighBlockPoly hp4 ell 1 = primeProduct p := by
  simp [primeHighBlockPoly,primeHighAugmentedIndex,primeAugmentedJet,
    primeHighBlockMultiplicity]

lemma primeHighRationalLocalUnit_norm (hp4 : 3 < p) (ell : Fin 3) :
    ‖(primeLocalUnit p (primeHighBlockJet hp4 ell).1:ℚ_[p])-
      ((primeHighRationalLocalUnit ell:ℚ):ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  fin_cases ell
  · simpa [primeHighBlockJet,primeHighRationalLocalUnit] using! primeLocalUnit_high_one_norm hp4
  · simpa [primeHighBlockJet,primeHighRationalLocalUnit] using! primeLocalUnit_high_two_norm hp4
  · simpa [primeHighBlockJet,primeHighRationalLocalUnit] using! primeLocalUnit_high_three_norm hp4

theorem GV_of_linear_padic_leading_bound (F : ℚ[X]) (r : ℚ) (k : ℕ)
    (h : ∀ n, ‖(C (p:ℚ_[p])*F.map (Rat.castHom ℚ_[p]) -
      C ((p:ℚ_[p])^k*(r:ℚ_[p]))).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(k+1)) :
    GV p (F-C ((p:ℚ)^((k:ℤ)-1)*r)) (k:ℚ) := by
  let E : ℚ[X] := C (p:ℚ)*F-C ((p:ℚ)^k*r)
  have hmap : E.map (Rat.castHom ℚ_[p]) =
      C (p:ℚ_[p])*F.map (Rat.castHom ℚ_[p]) -
        C ((p:ℚ_[p])^k*(r:ℚ_[p])) := by
    simp only [E,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
      Rat.coe_castHom,Rat.cast_pow,Rat.cast_natCast,Rat.cast_mul]
  have hE : GV p E ((k+1 : ℕ) : ℚ) := by
    intro n
    apply VG_of_padic_norm_pow_le _ (k+1)
    have hn := h n
    rw [← hmap] at hn
    simpa only [coeff_map,Rat.coe_castHom] using! hn
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp1 : (p:ℚ)^(-1:ℤ)*(p:ℚ) = 1 := by simp [zpow_neg,hpq]
  have hpk : (p:ℚ)^(-1:ℤ)*(p:ℚ)^k = (p:ℚ)^((k:ℤ)-1) := by
    rw [zpow_sub₀ hpq]
    simp only [zpow_neg,zpow_ofNat,zpow_natCast,pow_one,div_eq_mul_inv]
    ring
  have he : C ((p:ℚ)^(-1:ℤ))*E = F-C ((p:ℚ)^((k:ℤ)-1)*r) := by
    dsimp only [E]
    rw [mul_sub,← mul_assoc,← C_mul,hp1,C_1,one_mul,← C_mul]
    rw [← mul_assoc,hpk]
  have hh := GV.C_mul (VG.primePow (p := p) (-1)) hE
  rw [he] at hh
  exact hh.mono (by push_cast <;> linarith)

end
end Li2

end
