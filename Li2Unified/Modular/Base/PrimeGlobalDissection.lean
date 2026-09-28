module
public import Li2Unified.Modular.Base.PrimeActualLowLeading

set_option backward.privateInPublic true

@[expose] public section

/-! The actual original numerator is the sum of all disc polynomials. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def primeDiscTestFieldUV (hp4 : 3 < p) (a : Fin p) (T : ℤ[X]) (eta : ℤ_[p]) : (ℚ_[p])[X] :=
  ((primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).map
    (algebraMap ℤ_[p] ℚ_[p])).comp (C ((p:ℚ_[p])^2)*(X-C (eta:ℚ_[p]))) -
  C ((a.val:ℚ_[p])/(p:ℚ_[p])) *
    ((primePoleV hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).map
      (algebraMap ℤ_[p] ℚ_[p])).comp (C ((p:ℚ_[p])^2)*(X-C (eta:ℚ_[p])))

def primeDiscContribution (hp4 : 3 < p) (a : Fin p) (T : ℤ[X]) : (ℚ_[p])[X] :=
  C ((primeDiscScale a)⁻¹) * primeDiscTestFieldUV hp4 a T
    (primeEta (p := p) (by omega) (by omega))

lemma primeDiscScale_ne_zero (hp4 : 3 < p) (a : Fin p) : primeDiscScale a ≠ 0 := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold primeDiscScale
  split_ifs <;> simp_all only [ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true, one_ne_zero]

lemma primeDiscContribution_eval (hp4 : 3 < p) (a : Fin p) (T : ℤ[X]) (x : ℚ_[p]) :
    (primeDiscContribution hp4 a T).eval x =
      numeratorPulledValue (by omega) (by omega)
        ((p:ℚ_[p])^2*(x-(primeEta (p := p) (by omega) (by omega):ℚ_[p])))
        (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ)) a := by
  have h := numeratorPulledValue_all_integer_tests hp4
    ((p:ℚ_[p])^2*(x-(primeEta (p := p) (by omega) (by omega):ℚ_[p]))) a T
  simp only [primeDiscContribution,primeDiscTestFieldUV,eval_mul,eval_C,eval_sub,
    eval_comp,eval_X,eval_map]
  rw [← h]
  exact inv_mul_cancel_left₀ (primeDiscScale_ne_zero hp4 a) _

theorem primeNumerator_global_dissection (hp4 : 3 < p) (T : ℤ[X]) :
    (numeratorFunctional (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
      (Rat.castHom ℚ_[p]) =
      ∑ a : Fin p, C ((-2:ℚ_[p])^a.val)*primeDiscContribution hp4 a T := by
  apply Polynomial.funext
  intro x
  rw [eval_map,numeratorFunctional_dissection_eval (by omega : p ≠ 2) (by omega : p ≠ 3)]
  simp only [eval_finset_sum,eval_mul,eval_C,primeDiscContribution_eval]

lemma primeDiscTestFieldUV_eq_div_scaled (hp4 : 3 < p) (a : Fin p)
    (T : ℤ[X]) (eta : ℤ_[p]) :
    primeDiscTestFieldUV hp4 a T eta = C ((p:ℚ_[p])⁻¹)*
      (primeDiscTestScaled hp4 a T eta).map (algebraMap ℤ_[p] ℚ_[p]) := by
  have h := polynomial_divide_scaled_UV
    (((primePoleU hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).map
      (algebraMap ℤ_[p] ℚ_[p])).comp (C ((p:ℚ_[p])^2)*(X-C (eta:ℚ_[p]))))
    (((primePoleV hp4 (primeDiscTestRegular hp4 a T) (primeDiscTestResidue hp4 a T)).map
      (algebraMap ℤ_[p] ℚ_[p])).comp (C ((p:ℚ_[p])^2)*(X-C (eta:ℚ_[p]))))
    0 0 (a.val:ℚ_[p]) 0
  simpa only [primeDiscTestFieldUV,primeDiscTestScaled,Polynomial.map_sub,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_comp,Polynomial.map_X,PadicInt.algebraMap_apply,
    PadicInt.coe_natCast,PadicInt.coe_pow,C_0,zero_mul,mul_zero,sub_zero] using h.symm

lemma primeDiscContribution_scaled (hp4 : 3 < p) (a : Fin p) (T : ℤ[X]) :
    C ((p:ℚ_[p])^2)*primeDiscContribution hp4 a T =
      C ((p:ℚ_[p])/primeDiscScale a)*
        (primeDiscTestScaled hp4 a T (primeEta (p := p) (by omega) (by omega))).map
          (algebraMap ℤ_[p] ℚ_[p]) := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [primeDiscContribution,primeDiscTestFieldUV_eq_div_scaled]
  rw [← mul_assoc,← mul_assoc,← C_mul,← C_mul]
  congr 2
  field_simp

end
end Li2

end
