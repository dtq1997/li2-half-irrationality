module
public import Li2Unified.Modular.Positive.Packed.P057
public import Li2Unified.Modular.Base.PrimeHighRationalLeading

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def parameterHighDiscWeight (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0) (a : Fin p) : ℤ_[p] :=
  integralParameterInvPow lam hu.1 hu.2 a.val *
    (-(a.val:ℤ_[p])) * primeDiscUnitConstant a.val a.isLt

def parameterHighRationalWeight (lam : ℚ) : Fin 3 → ℚ := ![-2,lam/2,-2*lam^2/3]

theorem parameterInverse_high_VG (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hferm : VG p (lam^p-lam) 1) (ell : ℕ) (he : 1 ≤ ell) (hep : ell ≤ p) :
    VG p (lam⁻¹^(p-ell)-lam^(ell-1)) 1 := by
  have hi : VG p (lam⁻¹^p) 0 := by
    simpa using (rational_unit_inverse_VG lam hu.1 hu.2).pow p
  have hl : VG p (lam^(ell-1)) 0 := by
    have h : VG p lam 0 := Or.inr (by rw [hu.2]; norm_num)
    simpa using h.pow (ell-1)
  have ha : lam^(ell-1)*lam = lam^ell := by
    rw [← pow_succ, Nat.sub_add_cancel he]
  have hb : lam^(p-ell)*lam^ell = lam^p := by
    rw [← pow_add, Nat.sub_add_cancel hep]
  have hx : lam⁻¹^(p-ell)-lam^(ell-1) =
      -(lam^p-lam)*lam⁻¹^p*lam^(ell-1) := by
    rw [inv_pow, inv_pow]
    field_simp [hu.1]
    nlinarith [hb, congrArg (fun q : ℚ => q*lam^(p-ell)) ha]
  rw [hx]
  simpa using (hferm.neg.mul hi).mul hl

private def highUnitWeight (hp4 : 3 < p) (ell : Fin 3) : ℤ_[p] :=
  (-((primeHighBlockJet hp4 ell).1.val:ℤ_[p])) *
    primeDiscUnitConstant (primeHighBlockJet hp4 ell).1.val (primeHighBlockJet hp4 ell).1.isLt

private def highUnitRationalWeight : Fin 3 → ℚ := ![-2,1/2,-2/3]

private theorem highUnitWeight_norm (hp4 : 3 < p) (ell : Fin 3) :
    ‖(highUnitWeight hp4 ell:ℚ_[p])-(highUnitRationalWeight ell:ℚ_[p])‖ ≤
      ‖(p:ℚ_[p])‖ := by
  have hr (ell : Fin 3) : PadicInt.toZMod (highUnitWeight hp4 ell) =
      ((ell.val+1:ℕ):ZMod p) * primeFieldLeadingUnit (p-(ell.val+1)) := by
    simp only [highUnitWeight, primeHighBlockJet, Fin.val_mk,
      map_mul, map_neg, map_natCast, primeDiscUnitConstant_reduction]
    rw [primeField_cast_sub (ell.val+1) (by have h := ell.isLt; omega)]
    ring
  fin_cases ell
  · have h := integral_norm_sub_rational_of_cleared_reduction
      (highUnitWeight hp4 0) (-2) 1 (by decide) (by norm_num) (by
        rw [hr]
        norm_num only [Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceAdd] 
        rw [primeFieldLeadingUnit_high hp4 1 (by omega) (by omega)]
        norm_num)
    simpa [highUnitRationalWeight] using h
  · have h := integral_norm_sub_rational_of_cleared_reduction
      (highUnitWeight hp4 1) 1 2 (by decide) (two_valuation_zero (by omega)) (by
        rw [hr]
        norm_num only [Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceAdd] 
        rw [primeFieldLeadingUnit_high hp4 2 (by omega) (by omega)]
        have h2 := primeField_two_ne_zero (p := p) hp4
        have h4 : (4:ZMod p) ≠ 0 := by convert pow_ne_zero 2 h2 using 1 <;> ring
        norm_num
        field_simp [h4]
        <;> ring)
    simpa [highUnitRationalWeight] using h
  · have h := integral_norm_sub_rational_of_cleared_reduction
      (highUnitWeight hp4 2) (-2) 3 (by decide) (three_valuation_zero (by omega)) (by
        rw [hr]
        norm_num
        rw [primeFieldLeadingUnit_high hp4 3 (by omega) (by omega)]
        have h3 := primeField_three_ne_zero (p := p) hp4
        have h9 : (9:ZMod p) ≠ 0 := by convert pow_ne_zero 2 h3 using 1 <;> ring
        norm_num
        field_simp [h9]
        <;> ring)
    simpa [highUnitRationalWeight] using h

theorem parameterHighRationalWeight_norm (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (ell : Fin 3) :
    ‖(parameterHighDiscWeight lam hu (primeHighBlockJet hp4 ell).1:ℚ_[p])-
      (parameterHighRationalWeight lam ell:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  let x : ℚ_[p] := (lam:ℚ_[p])⁻¹^(p-(ell.val+1))
  let a : ℚ_[p] := (lam:ℚ_[p])^ell.val
  let y : ℚ_[p] := (highUnitWeight hp4 ell:ℚ_[p])
  let b : ℚ_[p] := (highUnitRationalWeight ell:ℚ_[p])
  have hxa : ‖x-a‖ ≤ ‖(p:ℚ_[p])‖ := by
    have h := padic_norm_le_prime_of_VG (parameterInverse_high_VG lam hu hferm
      (ell.val+1) (by omega) (by have h := ell.isLt; omega))
    simpa only [x,a,Nat.add_sub_cancel,Rat.cast_sub,Rat.cast_pow,Rat.cast_inv] using h
  have ha : ‖a‖ ≤ 1 := by
    have hv : VG p lam 0 := Or.inr (by rw [hu.2]; norm_num)
    simpa only [a,Rat.cast_pow] using padic_norm_le_one_of_VG (by
      simpa using hv.pow ell.val : VG p (lam^ell.val) 0)
  have hy : ‖y‖ ≤ 1 := PadicInt.norm_le_one _
  have hyb : ‖y-b‖ ≤ ‖(p:ℚ_[p])‖ := highUnitWeight_norm hp4 ell
  have hprod : ‖x*y-a*b‖ ≤ ‖(p:ℚ_[p])‖ := by
    rw [show x*y-a*b = (x-a)*y+a*(y-b) by ring]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    apply max_le
    · rw [norm_mul]
      simpa using mul_le_mul hxa hy (norm_nonneg _) (norm_nonneg _)
    · rw [norm_mul]
      simpa using mul_le_mul ha hyb (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have he : parameterHighRationalWeight lam ell = lam^ell.val*highUnitRationalWeight ell := by
    fin_cases ell <;> norm_num [parameterHighRationalWeight,highUnitRationalWeight] <;> ring
  rw [he]
  simpa only [x,a,y,b,parameterHighDiscWeight,highUnitWeight,primeHighBlockJet,
    Fin.val_mk,integralParameterInvPow,integralRational,PadicInt.coe_mul,
    PadicInt.coe_neg,PadicInt.coe_natCast,Rat.cast_mul,Rat.cast_pow,Rat.cast_inv,
    mul_assoc] using hprod

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterInverse_high_VG

#print axioms Li2Unified.Proofs.PrimeEdge.parameterHighRationalWeight_norm

end


end
