module
public import Li2Unified.Modular.Base.PrimeZeroEntry
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

lemma primeZeroMoment_VG (hp4 : 3 < p) (k : Fin 5) :
    VG p (![-113/12,95/4,-253/4,2093/12,-17773/36] k : ℚ) 0 := by
  have hv36 : padicValRat p (36:ℚ) = 0 := by
    rw [show (36:ℚ) = 6^2 by norm_num,padicValRat.pow (by norm_num),
      prime_six_valuation_zero hp4]
    norm_num
  have h36 : VG p (36:ℚ)⁻¹ 0 :=
    rational_unit_inverse_VG (36:ℚ) (by norm_num) hv36
  fin_cases k
  · convert (VG.intCast (p := p) (-339)).mul h36 using 1 <;> norm_num
  · convert (VG.intCast (p := p) 855).mul h36 using 1 <;> norm_num
  · convert (VG.intCast (p := p) (-2277)).mul h36 using 1 <;> norm_num
  · convert (VG.intCast (p := p) 6279).mul h36 using 1 <;> norm_num
  · convert (VG.intCast (p := p) (-17773)).mul h36 using 1 <;> norm_num

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

/-- Full zero/zero or zero/G entries; i=j=2 is excluded and requires the full top sum. -/
theorem primeZero_rational_entry_leading (hp4 : 3 < p) (i j : Fin 3)
    (hij : i.val+j.val < 4) (n : ℕ) :
    let k : Fin 5 := ⟨i.val+j.val,by omega⟩
    let c : ℚ := primeLocalUnit p ⟨0,by omega⟩
    ‖(C ((p:ℚ_[p])^3) *
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
        (primeZeroBlockPoly hp4 i*primeZeroBlockPoly hp4 j).map (Int.castRingHom ℚ))).map
          (Rat.castHom ℚ_[p]) -
      C ((p:ℚ_[p])^(i.val+j.val) *
        ((c^2*6*(![-113/12,95/4,-253/4,2093/12,-17773/36] k : ℚ) : ℚ) : ℚ_[p]))).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  let k : ℕ := i.val+j.val
  let q : ℚ := ![-113/12,95/4,-253/4,2093/12,-17773/36]
    (⟨i.val+j.val,by omega⟩ : Fin 5)
  let c : ℤ := primeLocalUnit p ⟨0,by omega⟩
  let u : ℤ_[p] := primeDiscUnitConstant 0 (by omega)
  let d : ℤ_[p] := (c:ℤ_[p])^2
  let e : ℤ_[p] := (p:ℤ_[p])^k * ((c*c:ℤ):ℤ_[p])
  let s : ℚ_[p] := (e:ℚ_[p]) * ((u:ℚ_[p])*(q:ℚ_[p]))
  let t : ℚ_[p] := (p:ℚ_[p])^k * (((c:ℚ)^2*6*q : ℚ) : ℚ_[p])
  have hq : ‖(q:ℚ_[p])‖ ≤ 1 := padic_norm_le_one_of_VG (primeZeroMoment_VG hp4 _)
  have hfac : ‖(d:ℚ_[p])*(q:ℚ_[p])‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1*1 := mul_le_mul (PadicInt.norm_le_one d) hq (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hunit : ‖(u:ℚ_[p])-6‖ ≤ ‖(p:ℚ_[p])‖ := primeDiscUnitConstant_zero_norm hp4
  have hdelta : ‖(d:ℚ_[p])*(q:ℚ_[p])*((u:ℚ_[p])-6)‖ ≤ ‖(p:ℚ_[p])‖ := by
    rw [norm_mul]
    calc
      _ ≤ 1*‖(p:ℚ_[p])‖ := mul_le_mul hfac hunit (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have he : s-t = (p:ℚ_[p])^k*((d:ℚ_[p])*(q:ℚ_[p])*((u:ℚ_[p])-6)) := by
    dsimp only [s,t,d,e]
    simp only [PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_natCast,
      PadicInt.coe_intCast,Int.cast_mul,Rat.cast_mul,Rat.cast_pow,
      Rat.cast_intCast,Rat.cast_ofNat]
    ring
  have hst : ‖s-t‖ ≤ ‖(p:ℚ_[p])‖^(k+1) := by
    rw [he,norm_mul,norm_pow,pow_succ]
    exact mul_le_mul_of_nonneg_left hdelta (by positivity)
  apply fieldPolynomial_replace_leading_bound _ s t _ (by positivity) ?_ hst n
  intro l
  simpa only [primeZeroBlockPoly,primeZeroAugmentedIndex,Fin.val_mk,s,t,e,k,q,c,u]
    using primeZero_original_entry_leading hp4
      (primeZeroAugmentedIndex hp4 i) (primeZeroAugmentedIndex hp4 j)
      (by simpa only [primeZeroAugmentedIndex,Fin.val_mk] using hij) l

theorem primeZero_rational_entry_GV (hp4 : 3 < p) (i j : Fin 3)
    (hij : i.val+j.val < 4) :
    let k : Fin 5 := ⟨i.val+j.val,by omega⟩
    let c : ℚ := primeLocalUnit p ⟨0,by omega⟩
    GV p
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
        (primeZeroBlockPoly hp4 i*primeZeroBlockPoly hp4 j).map (Int.castRingHom ℚ)) -
        C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-3) *
          (c^2*6*(![-113/12,95/4,-253/4,2093/12,-17773/36] k : ℚ))))
      ((i.val:ℚ)+(j.val:ℚ)-2) := by
  dsimp only
  have h := GV_of_cube_padic_leading_bound
    (numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
      (primeZeroBlockPoly hp4 i*primeZeroBlockPoly hp4 j).map (Int.castRingHom ℚ)))
    ((primeLocalUnit p ⟨0,by omega⟩:ℚ)^2*6*
      (![-113/12,95/4,-253/4,2093/12,-17773/36]
        (⟨i.val+j.val,by omega⟩ : Fin 5) : ℚ)) (i.val+j.val)
    (primeZero_rational_entry_leading hp4 i j hij)
  convert h using 1 <;> push_cast <;> ring

end
end Li2

end
