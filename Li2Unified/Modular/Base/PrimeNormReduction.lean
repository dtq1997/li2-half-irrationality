module
public import Li2Unified.Modular.Base.PrimeDiscUnitReduction
public import Li2Unified.Modular.Base.PadicValuationBridge

set_option backward.privateInPublic true

@[expose] public section

/-! Translate exact residue reduction and rational valuation bounds into the
norm bounds used by the integral local functional. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem padic_norm_le_prime_of_VG {q : ℚ} (h : VG p q 1) :
    ‖(q:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  simpa only [Rat.cast_one, Real.rpow_neg_one, Padic.norm_p] using
    (VG_iff_padic_norm_le q 1).mp h

theorem integral_norm_sub_le_prime_of_reduction (x y : ℤ_[p])
    (h : PadicInt.toZMod x = PadicInt.toZMod y) :
    ‖x-y‖ ≤ ‖(p:ℤ_[p])‖ := by
  have hz : x-y ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
    rw [RingHom.mem_ker, map_sub, h, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p] at hz
  have hb := (PadicInt.norm_le_pow_iff_mem_span_pow (x-y) 1).mpr
    (by simpa using hz)
  simpa using hb

theorem primeDiscUnitConstant_zero_norm (hp4 : 3 < p) :
    ‖primeDiscUnitConstant (p := p) 0 (by omega)-6‖ ≤ ‖(p:ℤ_[p])‖ := by
  apply integral_norm_sub_le_prime_of_reduction
  rw [primeDiscUnitConstant_reduction, primeFieldLeadingUnit_zero hp4]
  exact (map_ofNat _ _).symm

lemma integralPolynomial_eval_zero_cast (F : (ℤ_[p])[X]) :
    F.eval₂ (algebraMap ℤ_[p] ℚ_[p]) 0 = ((F.eval 0:ℤ_[p]):ℚ_[p]) := by
  simpa using eval₂_at_apply (p := F) (algebraMap ℤ_[p] ℚ_[p]) 0

lemma rationalPolynomial_eval_zero_cast (F : ℚ[X]) :
    F.eval₂ (Rat.castHom ℚ_[p]) 0 = ((F.eval 0:ℚ):ℚ_[p]) := by
  simpa using eval₂_at_apply (p := F) (Rat.castHom ℚ_[p]) 0

theorem integralPolynomial_eval_zero_norm_of_rational
    (F : (ℤ_[p])[X]) (G : ℚ[X]) (q : ℚ)
    (he : F.eval₂ (algebraMap ℤ_[p] ℚ_[p]) 0 = G.eval₂ (Rat.castHom ℚ_[p]) 0)
    (hG : VG p (G.eval 0-q) 1) :
    ‖((F.eval 0:ℤ_[p]):ℚ_[p])-(q:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  rw [integralPolynomial_eval_zero_cast, rationalPolynomial_eval_zero_cast] at he
  rw [he, ← Rat.cast_sub]
  exact padic_norm_le_prime_of_VG hG

end
end Li2

end
