module
public import Li2Unified.Modular.Base.PrimeLowEntry
public import Li2Unified.Modular.Base.PrimeRationalNormReduction
public import Li2Unified.Modular.Base.PrimeCubeValuationBridge
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

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

end
end Li2

end
