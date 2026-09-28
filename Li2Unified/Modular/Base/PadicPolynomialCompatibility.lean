module
public import Li2Unified.Modular.Base.ParameterDifferentialDissection
public import Li2Unified.Modular.Base.PrimePoleExtension

set_option backward.privateInPublic true

@[expose] public section

/-! Compatibility for any integral p-adic polynomial representing a rational
polynomial. This is not restricted to integer coefficients. -/
open Polynomial
namespace Li2
noncomputable section

lemma sequenceG_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (μ : ℕ → R) (P : R[X]) :
    sequenceG (fun n => φ (μ n)) (P.map φ) = φ (sequenceG μ P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.map_add, sequenceG_add, map_add, hP, hQ]
  | monomial n a => simp [sequenceG, Polynomial.sum_monomial_index]

variable {p : ℕ} [Fact p.Prime]

theorem padicParameterG_of_polynomial_map (z : ℚ) (hz : VG p (z/(1-z)) 0)
    (P : (ℤ_[p])[X]) (Q : ℚ[X])
    (he : P.map (algebraMap ℤ_[p] ℚ_[p]) = Q.map (Rat.castHom ℚ_[p])) :
    (padicParameterG z hz (P : PowerSeries ℤ_[p]) : ℚ_[p]) = (parameterG z Q : ℚ_[p]) := by
  unfold padicParameterG
  rw [restrictedMoment_polynomial]
  change algebraMap ℤ_[p] ℚ_[p] (sequenceG (integralParameterMoment z hz) P) =
    (Rat.castHom ℚ_[p]) (sequenceG (parameterMoment z) Q)
  rw [← sequenceG_map, ← sequenceG_map, he]
  rfl

theorem padicParameterU_of_polynomial_map (z : ℚ) (hz : VG p (z/(1-z)) 0)
    (P : (ℤ_[p])[X]) (Q : ℚ[X])
    (he : P.map (algebraMap ℤ_[p] ℚ_[p]) = Q.map (Rat.castHom ℚ_[p])) :
    (restrictedU (integralParameterMoment z hz) (P : PowerSeries ℤ_[p]) : ℚ_[p]) =
      (parameterU z Q : ℚ_[p]) := by
  rw [restrictedU_derivative, ← Polynomial.coe_X, ← Polynomial.coe_mul, PowerSeries.derivative_coe]
  apply padicParameterG_of_polynomial_map
  simp only [← derivative_map, Polynomial.map_mul, map_X, he]

theorem padicParameterV_of_polynomial_map (z : ℚ) (hz : VG p (z/(1-z)) 0)
    (P : (ℤ_[p])[X]) (Q : ℚ[X])
    (he : P.map (algebraMap ℤ_[p] ℚ_[p]) = Q.map (Rat.castHom ℚ_[p])) :
    (restrictedV (integralParameterMoment z hz) (P : PowerSeries ℤ_[p]) : ℚ_[p]) =
      (parameterV z Q : ℚ_[p]) := by
  rw [restrictedV_derivative _ _ (polynomial_isRestricted P), PowerSeries.derivative_coe]
  apply padicParameterG_of_polynomial_map
  simp only [← derivative_map, he]

end
end Li2

end
