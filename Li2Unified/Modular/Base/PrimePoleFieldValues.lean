module
public import Li2Unified.Modular.Base.PrimePoleExtension

set_option backward.privateInPublic true

@[expose] public section

/-! The existing integral pole polynomials evaluated at arbitrary Qp values.
This keeps the field-valued dissection tied to the actual integral extension. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem primeUPole_eval₂ (hp2 : p ≠ 2) (j : ℕ) (hj : j < p) (Y : ℚ_[p]) :
    (primeUPole hp2 j hj).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
      (j:ℚ_[p])*(primeParameter p:ℚ_[p])⁻¹^j*
        (Y-(parameterTau (primeParameter p) j:ℚ_[p])) := by
  simp [primeUPole, integralUPole, integralParameterInvPow, integralParameterTau,
    integralRational]

theorem primeVPole_eval₂ (hp2 : p ≠ 2) (j : ℕ) (hj : j < p) (Y : ℚ_[p]) :
    (primeVPole hp2 j hj).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
      -(primeParameter p:ℚ_[p])⁻¹^j*
        (Y-(parameterTau (primeParameter p) j:ℚ_[p])) := by
  simp [primeVPole, integralVPole, integralParameterInvPow, integralParameterTau,
    integralRational]

theorem primePoleU_single_eval₂ (hp4 : 3 < p) (j : Fin 4) (Y : ℚ_[p]) :
    (primePoleU hp4 0 (Pi.single j 1)).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
      (j.val:ℚ_[p])*(primeParameter p:ℚ_[p])⁻¹^j.val*
        (Y-(parameterTau (primeParameter p) j.val:ℚ_[p])) := by
  rw [primePoleU_single, primeUPole_eval₂]

theorem primePoleV_single_eval₂ (hp4 : 3 < p) (j : Fin 4) (Y : ℚ_[p]) :
    (primePoleV hp4 0 (Pi.single j 1)).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
      -(primeParameter p:ℚ_[p])⁻¹^j.val*
        (Y-(parameterTau (primeParameter p) j.val:ℚ_[p])) := by
  rw [primePoleV_single, primeVPole_eval₂]

end
end Li2

end
