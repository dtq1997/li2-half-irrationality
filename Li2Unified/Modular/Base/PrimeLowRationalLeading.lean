module
public import Li2Unified.Modular.Base.PrimeLowEntry
public import Li2Unified.Modular.Base.PrimeRationalNormReduction
public import Li2Unified.Modular.Base.PrimeCubeValuationBridge
public import Li2Unified.Modular.Base.FiniteCertificates

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def primeLowRationalUnit (a : ℕ) : ℚ :=
  ((a:ℚ)+1)*((a:ℚ)+2)*((a:ℚ)+3)/(a:ℚ)^2

def primeLowRationalWeight (a : ℕ) : ℚ :=
  (-2:ℚ)^a * (-(a:ℚ)) * primeLowRationalUnit a

lemma primeDiscUnitConstant_low_rational_norm (hp4 : 3 < p)
    (a : Fin p) (ha0 : 0 < a.val) (ha : a.val ≤ p-4) :
    ‖(primeDiscUnitConstant a.val a.isLt : ℚ_[p]) -
      ((primeLowRationalUnit a.val : ℚ) : ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  have hnd : ¬ p ∣ a.val := Nat.not_dvd_of_pos_of_lt ha0 a.isLt
  have haq : (a.val:ℚ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hai : (a.val:ℤ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hav : padicValRat p (a.val:ℚ) = 0 := by
    rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd hnd]
    rfl
  have had : padicValRat p (((a.val:ℤ)^2 : ℤ) : ℚ) = 0 := by
    simp only [Int.cast_pow,Int.cast_natCast]
    rw [padicValRat.pow,hav]
    norm_num
  have haz : (a.val:ZMod p) ≠ 0 := by
    intro hz
    exact hnd ((ZMod.natCast_eq_zero_iff a.val p).mp hz)
  have hr : PadicInt.toZMod (primeDiscUnitConstant a.val a.isLt) *
      (a.val:ZMod p)^2 =
      ((a.val:ZMod p)+1)*((a.val:ZMod p)+2)*((a.val:ZMod p)+3) := by
    rw [primeDiscUnitConstant_reduction,primeFieldLeadingUnit_low hp4 a.val ha0 ha]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 haz)
  have h := integral_norm_sub_rational_of_cleared_reduction
    (primeDiscUnitConstant a.val a.isLt)
    (((a.val:ℤ)+1)*((a.val:ℤ)+2)*((a.val:ℤ)+3)) ((a.val:ℤ)^2)
    (pow_ne_zero 2 hai) had
    (by simpa only [Int.cast_mul,Int.cast_add,Int.cast_pow,Int.cast_natCast,
      Int.cast_one,Int.cast_ofNat] using! hr)
  simpa only [primeLowRationalUnit,Rat.cast_div,Rat.cast_mul,Rat.cast_add,
    Rat.cast_pow,Rat.cast_natCast,Rat.cast_one,Rat.cast_ofNat,
    Int.cast_mul,Int.cast_add,Int.cast_pow,Int.cast_natCast,Int.cast_one,Int.cast_ofNat] using! h

lemma primeLowMoment_VG (hp4 : 3 < p) (k : Fin 3) :
    VG p (![95/4,-253/4,2093/12] k : ℚ) 0 := by
  have hv12 : padicValRat p (12:ℚ) = 0 := by
    rw [show (12:ℚ) = 4*3 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num),
      prime_four_valuation_zero hp4,three_valuation_zero (by omega)]
    norm_num
  have h12 : VG p (12:ℚ)⁻¹ 0 :=
    rational_unit_inverse_VG (12:ℚ) (by norm_num) hv12
  fin_cases k
  · convert (VG.intCast (p := p) 285).mul h12 using 1 <;> norm_num
  · convert (VG.intCast (p := p) (-759)).mul h12 using 1 <;> norm_num
  · convert (VG.intCast (p := p) 2093).mul h12 using 1 <;> norm_num

lemma primeLowMoment_eq_lowBlock (i j : Fin 2) (h : i.val+j.val < 3) :
    (![95/4,-253/4,2093/12] (⟨i.val+j.val,h⟩ : Fin 3) : ℚ) = lowBlock i j := by
  fin_cases i <;> fin_cases j <;> norm_num [lowBlock]

theorem fieldPolynomial_replace_leading_bound (F : (ℚ_[p])[X])
    (s t : ℚ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ n, ‖(F-C s).coeff n‖ ≤ B) (hst : ‖s-t‖ ≤ B) (n : ℕ) :
    ‖(F-C t).coeff n‖ ≤ B := by
  have he : F-C t = (F-C s)+C (s-t) := by rw [C_sub]; ring
  rw [he,coeff_add]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le (hF n)
  by_cases hn : n = 0
  · subst n
    simpa using! hst
  · simpa only [coeff_C,if_neg hn,norm_zero] using! hB

/-- Original entry after all discs, with both actual product units retained. -/
theorem primeLow_rational_entry_leading (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (i j : Fin (primeMultiplicity p a)) (n : ℕ) :
    let k : Fin 3 := ⟨i.val+j.val,primeLow_pair_lt_three hp4 a ha i j⟩
    ‖(C ((p:ℚ_[p])^2) *
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
        (primeJetPoly p ⟨a,i⟩ * primeJetPoly p ⟨a,j⟩).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p]) -
      C ((p:ℚ_[p])^(i.val+j.val) *
        ((((primeLocalUnit p a:ℚ)^2 * primeLowRationalWeight a.val *
          (![95/4,-253/4,2093/12] k : ℚ)) : ℚ) : ℚ_[p]))).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  let k : ℕ := i.val+j.val
  let q : ℚ := ![95/4,-253/4,2093/12]
    (⟨i.val+j.val,primeLow_pair_lt_three hp4 a ha i j⟩ : Fin 3)
  let c : ℤ := primeLocalUnit p a
  let u : ℤ_[p] := primeDiscUnitConstant a.val a.isLt
  let d : ℤ_[p] := (-2:ℤ_[p])^a.val * (-(a.val:ℤ_[p])) * (c:ℤ_[p])^2
  let s : ℚ_[p] := (-2:ℚ_[p])^a.val *
    ((p:ℚ_[p])^k * ((c*c:ℤ):ℚ_[p]) *
      (-(a.val:ℚ_[p])*((u:ℚ_[p])*(q:ℚ_[p]))))
  let t : ℚ_[p] := (p:ℚ_[p])^k *
    (((c:ℚ)^2 * primeLowRationalWeight a.val * q : ℚ) : ℚ_[p])
  have hq : ‖(q:ℚ_[p])‖ ≤ 1 :=
    padic_norm_le_one_of_VG (primeLowMoment_VG hp4 _)
  have hfac : ‖(d:ℚ_[p])*(q:ℚ_[p])‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1*1 := mul_le_mul (PadicInt.norm_le_one d) hq (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hunit : ‖(u:ℚ_[p])-((primeLowRationalUnit a.val:ℚ):ℚ_[p])‖ ≤
      ‖(p:ℚ_[p])‖ := primeDiscUnitConstant_low_rational_norm hp4 a ha0 ha
  have hdelta : ‖(d:ℚ_[p])*(q:ℚ_[p])*
      ((u:ℚ_[p])-((primeLowRationalUnit a.val:ℚ):ℚ_[p]))‖ ≤ ‖(p:ℚ_[p])‖ := by
    rw [norm_mul]
    calc
      _ ≤ 1*‖(p:ℚ_[p])‖ := mul_le_mul hfac hunit (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have he : s-t = (p:ℚ_[p])^k * ((d:ℚ_[p])*(q:ℚ_[p])*
      ((u:ℚ_[p])-((primeLowRationalUnit a.val:ℚ):ℚ_[p]))) := by
    dsimp only [s,t,d,primeLowRationalWeight]
    simp only [Rat.cast_mul,Rat.cast_pow,Rat.cast_neg,Rat.cast_ofNat,
      Rat.cast_natCast,Rat.cast_intCast,Int.cast_mul,PadicInt.coe_mul,
      PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast,PadicInt.coe_intCast]
    have htwo : ((2 : ℤ_[p]) : ℚ_[p]) = 2 := rfl
    simp only [htwo]
    ring
  have hst : ‖s-t‖ ≤ ‖(p:ℚ_[p])‖^(k+1) := by
    rw [he,norm_mul,norm_pow,pow_succ]
    exact mul_le_mul_of_nonneg_left hdelta (by positivity)
  apply fieldPolynomial_replace_leading_bound _ s t _ (by positivity) ?_ hst n
  intro l
  simpa only [s,k,q,c,u] using! primeLow_original_entry_leading hp4 a ha0 ha i j l

end
end Li2

end
