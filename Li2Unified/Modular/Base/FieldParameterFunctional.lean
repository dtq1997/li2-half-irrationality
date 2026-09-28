module
public import Li2Unified.Modular.Base.FieldRestrictedEvaluation
public import Li2Unified.Modular.Base.PadicPolynomialCompatibility

set_option backward.privateInPublic true

@[expose] public section

/-! Compatibility of the Q_p extension with the actual rational parameter
polynomials. No integral-coefficient representative is assumed for the polynomial. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def fieldRestrictedU (μ : ℕ → ℤ_[p]) (f : PowerSeries ℚ_[p]) : ℚ_[p] :=
  fieldRestrictedMoment (fun n => (n+1:ℕ)*μ n) f

def fieldRestrictedV (μ : ℕ → ℤ_[p]) (f : PowerSeries ℚ_[p]) : ℚ_[p] :=
  fieldRestrictedMoment (derivativeMoments μ) f

theorem fieldRestrictedU_integral (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    fieldRestrictedU μ (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) f) =
      (restrictedU μ f : ℚ_[p]) := fieldRestrictedMoment_integral _ _ hf

theorem fieldRestrictedV_integral (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    fieldRestrictedV μ (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) f) =
      (restrictedV μ f : ℚ_[p]) := fieldRestrictedMoment_integral _ _ hf

theorem fieldRestrictedU_derivative (μ : ℕ → ℤ_[p]) (f : PowerSeries ℚ_[p]) :
    fieldRestrictedU μ f = fieldRestrictedMoment μ
      (PowerSeries.derivative (R := ℚ_[p]) (PowerSeries.X*f)) := by
  unfold fieldRestrictedU fieldRestrictedMoment
  apply tsum_congr
  intro n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_succ_X_mul]
  push_cast
  ring

theorem fieldRestrictedV_derivative (μ : ℕ → ℤ_[p]) (f : PowerSeries ℚ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    fieldRestrictedV μ f = fieldRestrictedMoment μ (PowerSeries.derivative (R := ℚ_[p]) f) := by
  have he := (fieldRestrictedMoment_summable (derivativeMoments μ) f hf).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, derivativeMoments, PadicInt.coe_zero, mul_zero, zero_add] at he
  unfold fieldRestrictedV fieldRestrictedMoment derivativeMoments
  rw [← he]
  apply tsum_congr
  intro n
  rw [PowerSeries.coeff_derivative]
  push_cast
  ring

theorem fieldParameterG_polynomial (z : ℚ) (hz : VG p (z/(1-z)) 0) (P : ℚ[X]) :
    fieldRestrictedMoment (integralParameterMoment z hz)
      (P.map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p]) = (parameterG z P : ℚ_[p]) := by
  rw [fieldRestrictedMoment_polynomial]
  change sequenceG (fun n => (parameterMoment z n:ℚ_[p])) (P.map (Rat.castHom ℚ_[p])) = _
  exact sequenceG_map (Rat.castHom ℚ_[p]) (parameterMoment z) P

theorem fieldParameterU_polynomial (z : ℚ) (hz : VG p (z/(1-z)) 0) (P : ℚ[X]) :
    fieldRestrictedU (integralParameterMoment z hz)
      (P.map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p]) = (parameterU z P : ℚ_[p]) := by
  rw [fieldRestrictedU_derivative, ← Polynomial.coe_X, ← Polynomial.coe_mul,
    PowerSeries.derivative_coe]
  have he : (X*P.map (Rat.castHom ℚ_[p])).derivative =
      ((X*P).derivative).map (Rat.castHom ℚ_[p]) := by
    rw [← derivative_map, Polynomial.map_mul, map_X]
  rw [he]
  exact fieldParameterG_polynomial z hz _

theorem fieldParameterV_polynomial (z : ℚ) (hz : VG p (z/(1-z)) 0) (P : ℚ[X]) :
    fieldRestrictedV (integralParameterMoment z hz)
      (P.map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p]) = (parameterV z P : ℚ_[p]) := by
  rw [fieldRestrictedV_derivative _ _ (field_polynomial_isRestricted _),
    PowerSeries.derivative_coe, derivative_map]
  exact fieldParameterG_polynomial z hz _

end
end Li2

end
