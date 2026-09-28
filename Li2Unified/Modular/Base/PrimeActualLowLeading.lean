module
public import Li2Unified.Modular.Base.PrimeJetDivision

set_option backward.privateInPublic true

@[expose] public section

/-! Actual products of two basis jets on their own low disc. Contributions
from the other discs must still be included before identifying a matrix block. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem integralPolynomial_scaled_rational_leading
    (F H : (ℤ_[p])[X]) (c : ℤ_[p]) (m : ℕ) (r : ℚ_[p])
    (hFH : ∀ n, ‖(F-C ((p:ℤ_[p])^m*c)*H).coeff n‖ ≤ ‖(p:ℤ_[p])^(m+1)‖)
    (hH : ∀ n, ‖(H.map (algebraMap ℤ_[p] ℚ_[p])-C r).coeff n‖ ≤ ‖(p:ℚ_[p])‖)
    (n : ℕ) :
    ‖(F.map (algebraMap ℤ_[p] ℚ_[p])-C ((((p:ℤ_[p])^m*c:ℤ_[p]):ℚ_[p])*r)).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(m+1) := by
  let q : ℤ_[p] := (p:ℤ_[p])^m*c
  have he : F.map (algebraMap ℤ_[p] ℚ_[p])-C ((q:ℚ_[p])*r) =
      (F-C q*H).map (algebraMap ℤ_[p] ℚ_[p])+
        C (q:ℚ_[p])*(H.map (algebraMap ℤ_[p] ℚ_[p])-C r) := by
    simp only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
      PadicInt.algebraMap_apply,C_mul]
    ring
  change ‖(F.map (algebraMap ℤ_[p] ℚ_[p])-C ((q:ℚ_[p])*r)).coeff n‖ ≤ _
  rw [he,coeff_add]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · simpa only [coeff_map,norm_pow] using hFH n
  · rw [coeff_C_mul,norm_mul]
    have hq : ‖(q:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖^m := by
      simpa only [norm_pow] using integral_coeff_mul_norm_le ((p:ℤ_[p])^m) c
    calc
      _ ≤ ‖(p:ℚ_[p])‖^m*‖(p:ℚ_[p])‖ :=
        mul_le_mul hq (hH n) (norm_nonneg _) (pow_nonneg (norm_nonneg _) m)
      _ = _ := (pow_succ _ _).symm

def primeDiscTestScaled (hp4 : 3 < p) (a : Fin p) (T : ℤ[X]) (eta : ℤ_[p]) : (ℤ_[p])[X] :=
  C (p:ℤ_[p])*(primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
    (C ((p:ℤ_[p])^2)*(X-C eta)) -
  C (a.val:ℤ_[p])*(primePoleV hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).comp
    (C ((p:ℤ_[p])^2)*(X-C eta))

def primeDiscMonomialScaled (hp4 : 3 < p) (a : Fin p) (k : ℕ) (eta : ℤ_[p]) : (ℤ_[p])[X] :=
  C (p:ℤ_[p])*(primePoleU hp4 (primeDiscMonomialRegular hp4 a k)
    (primeDiscMonomialResidue hp4 a k)).comp (C ((p:ℤ_[p])^2)*(X-C eta)) -
  C (a.val:ℤ_[p])*(primePoleV hp4 (primeDiscMonomialRegular hp4 a k)
    (primeDiscMonomialResidue hp4 a k)).comp (C ((p:ℤ_[p])^2)*(X-C eta))

lemma primeMultiplicity_low (hp4 : 3 < p) (a : Fin p) (ha : a.val ≤ p-4) :
    primeMultiplicity p a = 2 := by
  rw [primeMultiplicity,if_pos (by omega)]

lemma primeLow_pair_lt_three (hp4 : 3 < p) (a : Fin p) (ha : a.val ≤ p-4)
    (i j : Fin (primeMultiplicity p a)) : i.val+j.val < 3 := by
  have hi := i.isLt
  have hj := j.isLt
  have hm := primeMultiplicity_low hp4 a ha
  omega

theorem primeJet_actual_low_scaled_leading (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (i j : Fin (primeMultiplicity p a))
    (eta : ℤ_[p]) (n : ℕ) :
    let k : Fin 3 := ⟨i.val+j.val,primeLow_pair_lt_three hp4 a ha i j⟩
    let c : ℤ_[p] := ((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℤ_[p])
    let r : ℚ_[p] := -(a.val:ℚ_[p])*((primeDiscUnitConstant a.val a.isLt:ℚ_[p]) *
      ((![95/4,-253/4,2093/12] k:ℚ):ℚ_[p]))
    ‖((primeDiscTestScaled hp4 a (primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩) eta).map
      (algebraMap ℤ_[p] ℚ_[p])-C ((((p:ℤ_[p])^(i.val+j.val)*c:ℤ_[p]):ℚ_[p])*r)).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  apply integralPolynomial_scaled_rational_leading _ (primeDiscMonomialScaled hp4 a (i.val+j.val) eta)
  · exact primeJet_same_UV_substituted_error hp4 a i j eta
  · intro k
    simpa only [primeDiscMonomialScaled,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
      PadicInt.algebraMap_apply,PadicInt.coe_natCast] using
      primeDiscMonomial_low_scaled_leading hp4 a ha0 ha
        ⟨i.val+j.val,primeLow_pair_lt_three hp4 a ha i j⟩ eta k

end
end Li2

end
