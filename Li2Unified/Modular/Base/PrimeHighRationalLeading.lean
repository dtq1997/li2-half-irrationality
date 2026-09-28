module
public import Li2Unified.Modular.Base.PrimeHighEntry
public import Li2Unified.Modular.Base.PrimeEdgeNormValues
public import Li2Unified.Modular.Base.PrimeLowRationalLeading
public import Li2Unified.Modular.Base.PrimeBlockIndex

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def primeHighRationalWeight : Fin 3 → ℚ := ![-2,-1/4,-1/6]
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

lemma primeHighRationalWeight_norm (hp4 : 3 < p) (ell : Fin 3) :
    ‖(primeHighDiscWeight (primeHighBlockJet hp4 ell).1:ℚ_[p])-
      ((primeHighRationalWeight ell:ℚ):ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  fin_cases ell
  · simpa [primeHighBlockJet,primeHighRationalWeight] using! primeHighDiscWeight_one_norm hp4
  · simpa [primeHighBlockJet,primeHighRationalWeight] using! primeHighDiscWeight_two_norm hp4
  · simpa [primeHighBlockJet,primeHighRationalWeight] using! primeHighDiscWeight_three_norm hp4

lemma primeHighRationalLocalUnit_norm (hp4 : 3 < p) (ell : Fin 3) :
    ‖(primeLocalUnit p (primeHighBlockJet hp4 ell).1:ℚ_[p])-
      ((primeHighRationalLocalUnit ell:ℚ):ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  fin_cases ell
  · simpa [primeHighBlockJet,primeHighRationalLocalUnit] using! primeLocalUnit_high_one_norm hp4
  · simpa [primeHighBlockJet,primeHighRationalLocalUnit] using! primeLocalUnit_high_two_norm hp4
  · simpa [primeHighBlockJet,primeHighRationalLocalUnit] using! primeLocalUnit_high_three_norm hp4

lemma primeHighRationalWeight_VG (hp4 : 3 < p) (ell : Fin 3) :
    VG p (primeHighRationalWeight ell) 0 := by
  have hv12 : padicValRat p (12:ℚ) = 0 := by
    rw [show (12:ℚ) = 4*3 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num),
      prime_four_valuation_zero hp4,three_valuation_zero (by omega)]
    norm_num
  have h12 : VG p (12:ℚ)⁻¹ 0 :=
    rational_unit_inverse_VG (12:ℚ) (by norm_num) hv12
  fin_cases ell
  · convert (VG.intCast (p := p) (-24)).mul h12 using 1 <;>
      norm_num [primeHighRationalWeight]
  · convert (VG.intCast (p := p) (-3)).mul h12 using 1 <;>
      norm_num [primeHighRationalWeight]
  · convert (VG.intCast (p := p) (-2)).mul h12 using 1 <;>
      norm_num [primeHighRationalWeight]

lemma primeHighMoment_VG (hp4 : 3 < p) (k : Fin 3) :
    VG p (![8,-46/3,266/9] k : ℚ) 0 := by
  have hv9 : padicValRat p (9:ℚ) = 0 := by
    rw [show (9:ℚ) = 3^2 by norm_num,padicValRat.pow,
      three_valuation_zero (by omega)]
    norm_num
  have h9 : VG p (9:ℚ)⁻¹ 0 :=
    rational_unit_inverse_VG (9:ℚ) (by norm_num) hv9
  fin_cases k
  · convert (VG.intCast (p := p) 72).mul h9 using 1 <;> norm_num
  · convert (VG.intCast (p := p) (-138)).mul h9 using 1 <;> norm_num
  · convert (VG.intCast (p := p) 266).mul h9 using 1 <;> norm_num

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

/-- Actual high/high and high/G entries; the full top/top sum is excluded. -/
theorem primeHigh_rational_entry_leading (hp4 : 3 < p) (ell : Fin 3)
    (i j : Fin 2) (hij : i.val+j.val < 2) (n : ℕ) :
    let k : Fin 3 := ⟨i.val+j.val,by omega⟩
    let c : ℚ := primeLocalUnit p (primeHighBlockJet hp4 ell).1
    ‖(C (p:ℚ_[p]) *
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
        (primeHighBlockPoly hp4 ell i*primeHighBlockPoly hp4 ell j).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p]) -
      C ((p:ℚ_[p])^(i.val+j.val) *
        ((c^2*primeHighRationalWeight ell*(![8,-46/3,266/9] k : ℚ) : ℚ):ℚ_[p]))).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  let a : Fin p := (primeHighBlockJet hp4 ell).1
  let k : ℕ := i.val+j.val
  let q : ℚ := ![8,-46/3,266/9] (⟨i.val+j.val,by omega⟩ : Fin 3)
  let c : ℤ := primeLocalUnit p a
  let u : ℤ_[p] := primeDiscUnitConstant a.val a.isLt
  let d : ℤ_[p] := (c:ℤ_[p])^2
  let e : ℤ_[p] := (p:ℤ_[p])^k * ((c*c:ℤ):ℤ_[p])
  let s : ℚ_[p] := (-2:ℚ_[p])^a.val *
    ((e:ℚ_[p]) * (-(a.val:ℚ_[p])*((u:ℚ_[p])*(q:ℚ_[p]))))
  let t : ℚ_[p] := (p:ℚ_[p])^k *
    (((c:ℚ)^2*primeHighRationalWeight ell*q : ℚ):ℚ_[p])
  have hq : ‖(q:ℚ_[p])‖ ≤ 1 := padic_norm_le_one_of_VG (primeHighMoment_VG hp4 _)
  have hfac : ‖(d:ℚ_[p])*(q:ℚ_[p])‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1*1 := mul_le_mul (PadicInt.norm_le_one d) hq (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hunit : ‖(primeHighDiscWeight a:ℚ_[p])-
      ((primeHighRationalWeight ell:ℚ):ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ :=
    primeHighRationalWeight_norm hp4 ell
  have hdelta : ‖(d:ℚ_[p])*(q:ℚ_[p]) *
      ((primeHighDiscWeight a:ℚ_[p])-((primeHighRationalWeight ell:ℚ):ℚ_[p]))‖ ≤
      ‖(p:ℚ_[p])‖ := by
    rw [norm_mul]
    calc
      _ ≤ 1*‖(p:ℚ_[p])‖ := mul_le_mul hfac hunit (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have he : s-t = (p:ℚ_[p])^k * ((d:ℚ_[p])*(q:ℚ_[p]) *
      ((primeHighDiscWeight a:ℚ_[p])-((primeHighRationalWeight ell:ℚ):ℚ_[p]))) := by
    dsimp only [s,t,d,e,u,primeHighDiscWeight]
    simp only [PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_natCast,
      PadicInt.coe_intCast,PadicInt.coe_neg,Int.cast_mul,Rat.cast_mul,
      Rat.cast_pow,Rat.cast_intCast]
    have htwo : ((2:ℤ_[p]):ℚ_[p]) = 2 := rfl
    simp only [htwo]
    ring
  have hst : ‖s-t‖ ≤ ‖(p:ℚ_[p])‖^(k+1) := by
    rw [he,norm_mul,norm_pow,pow_succ]
    exact mul_le_mul_of_nonneg_left hdelta (by positivity)
  apply fieldPolynomial_replace_leading_bound _ s t _ (by positivity) ?_ hst n
  intro l
  simpa only [primeHighBlockPoly,primeHighAugmentedIndex,Fin.val_mk,s,e,k,q,c,u,a]
    using! primeHigh_original_entry_leading hp4 (primeHighBlockJet hp4 ell).1
      (primeHighBlock_above hp4 ell)
      (primeHighAugmentedIndex hp4 ell i) (primeHighAugmentedIndex hp4 ell j)
      (by simpa only [primeHighAugmentedIndex,Fin.val_mk] using! hij) l

theorem primeHigh_rational_entry_GV (hp4 : 3 < p) (ell : Fin 3)
    (i j : Fin 2) (hij : i.val+j.val < 2) :
    let k : Fin 3 := ⟨i.val+j.val,by omega⟩
    let c : ℚ := primeLocalUnit p (primeHighBlockJet hp4 ell).1
    GV p
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
        (primeHighBlockPoly hp4 ell i*primeHighBlockPoly hp4 ell j).map
          (Int.castRingHom ℚ)) -
        C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-1) *
          (c^2*primeHighRationalWeight ell*(![8,-46/3,266/9] k : ℚ))))
      ((i.val:ℚ)+(j.val:ℚ)) := by
  dsimp only
  have h := GV_of_linear_padic_leading_bound
    (numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
      (primeHighBlockPoly hp4 ell i*primeHighBlockPoly hp4 ell j).map
        (Int.castRingHom ℚ)))
    ((primeLocalUnit p (primeHighBlockJet hp4 ell).1:ℚ)^2 *
      primeHighRationalWeight ell *
      (![8,-46/3,266/9] (⟨i.val+j.val,by omega⟩ : Fin 3) : ℚ)) (i.val+j.val)
    (primeHigh_rational_entry_leading hp4 ell i j hij)
  convert h using 1 <;> push_cast <;> ring

end
end Li2

end
