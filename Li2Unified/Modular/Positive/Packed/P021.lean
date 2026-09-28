module
public import Li2Unified.Modular.Positive.Packed.P020
public import Li2Unified.Modular.Positive.Packed.P016
public import Li2Unified.Modular.Positive.Packed.P013
public import Li2Unified.Modular.Positive.Packed.P019
public import Li2Unified.Modular.Positive.Packed.P010
public import Li2Unified.Modular.Base.OriginalIntegerTests
public import Li2Unified.Modular.Base.RestrictedPoleMultiplierBounds

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- The exact unit hypothesis of `HermitePreparation.actual_functional`
supplies every condition needed by the general pole window. -/
theorem parameterPoleHypotheses_of_hunit (lam : ℚ)
    (hunit : (lam ≠ 0 ∧ padicValRat p lam = 0) ∧
      (1 - lam ≠ 0 ∧ padicValRat p (1 - lam) = 0)) :
    lam ≠ 0 ∧ Li2.VG p (lam ^ p) 0 ∧
      Li2.VG p (lam ^ p / (1 - lam ^ p)) 0 ∧ lam ^ p ≠ 1 := by
  have hp := Li2Unified.LambdaLift.parameter_power_unit lam hunit.1
  have h1 := Li2Unified.Proofs.Arithmetic.one_sub_power_unit_of_hunit lam hunit
  have hv : Li2.VG p (lam ^ p) 0 := Or.inr (by rw [hp.2]; norm_num)
  have hi : Li2.VG p (1 - lam ^ p)⁻¹ 0 :=
    Li2.rational_unit_inverse_VG (1 - lam ^ p) h1.1 h1.2
  have hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0 := by
    simpa only [div_eq_mul_inv, zero_add] using hv.mul hi
  have hne : lam ^ p ≠ 1 := by
    intro he
    apply h1.1
    rw [he]
    ring
  exact ⟨hunit.1.1, hv, hz, hne⟩

#print axioms parameterPoleHypotheses_of_hunit

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem actual_general_integer_tests (lam : ℚ) (n : ℕ)
    (a : Fin p) (Y : ℚ_[p]) (T : ℤ[X])
    (hsq : 4 * n < p * p)
    (hunit : (lam ≠ 0 ∧ padicValRat p lam = 0) ∧
      (1 - lam ≠ 0 ∧ padicValRat p (1 - lam) = 0)) :
    ∃ g : PowerSeries ℤ_[p], ∃ r : Fin p → ℤ_[p],
      PowerSeries.IsRestricted 1 g ∧
      generalPoleScale n a *
        parameterPulledValue lam
          (parameterPoleHypotheses_of_hunit lam hunit).2.2.1 Y (4 * n)
          (((D n) ^ 3) * T.map (Int.castRingHom ℚ)) a =
      (generalPoleU (lam ^ p)
          (Li2Unified.LambdaLift.parameter_power_unit lam hunit.1)
          (parameterPoleHypotheses_of_hunit lam hunit).2.2.1 g r).eval₂
            (algebraMap ℤ_[p] ℚ_[p]) Y -
        (a.val : ℚ_[p]) / (p : ℚ_[p]) *
          (generalPoleV (lam ^ p)
            (Li2Unified.LambdaLift.parameter_power_unit lam hunit.1)
            (parameterPoleHypotheses_of_hunit lam hunit).2.2.1 g r).eval₂
              (algebraMap ℤ_[p] ℚ_[p]) Y := by
  classical
  have hp : 0 < p := by have := a.isLt; omega
  obtain ⟨g₀, r₀, hg₀, he⟩ := general_original_integral_cleared n a hp hsq
  let hu := Li2Unified.LambdaLift.parameter_power_unit lam hunit.1
  let hr := (parameterPoleHypotheses_of_hunit lam hunit).2.2.1
  let g := integralPoleMulRegular (generalPoleCenters (p := p))
    (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) g₀ r₀
  let r := integralPoleMulResidue (generalPoleCenters (p := p))
    (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) r₀
  refine ⟨g, r, ?_, ?_⟩
  · exact integralPoleMulRegular_isRestricted _ _ _
      (polynomial_isRestricted _) hg₀ _
  · simpa only [g, r, hu, hr] using
      (parameterPulledValue_integer_test lam hu hr Y (4 * n) hsq
        ((D n) ^ 3) a (generalPoleScale n a) g₀ hg₀ r₀ he T)

#print axioms actual_general_integer_tests

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalPoleTest_U_coeff_bound (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : VG p (z / (1 - z)) 0)
    (f : PowerSeries ℤ_[p]) (r : Fin p → ℤ_[p])
    (T : ℤ[X]) (a : Fin p) (B : ℝ) (hB : 0 ≤ B)
    (hT : ∀ k, ‖(integralDiscTestPolynomial T a).coeff k‖ ≤ B)
    (k : ℕ) :
    ‖(generalPoleU z hu hz
      (integralPoleMulRegular (generalPoleCenters (p := p))
        (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) f r)
      (integralPoleMulResidue (generalPoleCenters (p := p))
        (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) r)).coeff k‖ ≤ B := by
  classical
  apply generalPoleU_coeff_bound z hu hz _ _ B hB
  · apply integralPoleMulRegular_bound_left _ _ _ _ B hB
    simpa only [Polynomial.coeff_coe] using hT
  · apply integralPoleMulResidue_bound_left _ _ _ B
    simpa only [Polynomial.coeff_coe] using hT

theorem generalPoleTest_V_coeff_bound (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : VG p (z / (1 - z)) 0)
    (f : PowerSeries ℤ_[p]) (r : Fin p → ℤ_[p])
    (T : ℤ[X]) (a : Fin p) (B : ℝ) (hB : 0 ≤ B)
    (hT : ∀ k, ‖(integralDiscTestPolynomial T a).coeff k‖ ≤ B)
    (k : ℕ) :
    ‖(generalPoleV z hu hz
      (integralPoleMulRegular (generalPoleCenters (p := p))
        (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) f r)
      (integralPoleMulResidue (generalPoleCenters (p := p))
        (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) r)).coeff k‖ ≤ B := by
  classical
  apply generalPoleV_coeff_bound z hu hz _ _ B hB
  · apply integralPoleMulRegular_bound_left _ _ _ _ B hB
    simpa only [Polynomial.coeff_coe] using hT
  · apply integralPoleMulResidue_bound_left _ _ _ B
    simpa only [Polynomial.coeff_coe] using hT

#print axioms generalPoleTest_U_coeff_bound
#print axioms generalPoleTest_V_coeff_bound

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem actual_general_integer_tests_bounded (lam : ℚ) (n : ℕ)
    (a : Fin p) (Y : ℚ_[p]) (T : ℤ[X])
    (hsq : 4 * n < p * p)
    (hunit : (lam ≠ 0 ∧ padicValRat p lam = 0) ∧
      (1 - lam ≠ 0 ∧ padicValRat p (1 - lam) = 0))
    (B : ℝ) (hB : 0 ≤ B)
    (hT : ∀ k, ‖(integralDiscTestPolynomial T a).coeff k‖ ≤ B) :
    ∃ g : PowerSeries ℤ_[p], ∃ r : Fin p → ℤ_[p],
      PowerSeries.IsRestricted 1 g ∧
      (∀ k, ‖(generalPoleU (lam ^ p)
        (Li2Unified.LambdaLift.parameter_power_unit lam hunit.1)
        (parameterPoleHypotheses_of_hunit lam hunit).2.2.1 g r).coeff k‖ ≤ B) ∧
      (∀ k, ‖(generalPoleV (lam ^ p)
        (Li2Unified.LambdaLift.parameter_power_unit lam hunit.1)
        (parameterPoleHypotheses_of_hunit lam hunit).2.2.1 g r).coeff k‖ ≤ B) ∧
      generalPoleScale n a *
        parameterPulledValue lam
          (parameterPoleHypotheses_of_hunit lam hunit).2.2.1 Y (4 * n)
          (((D n) ^ 3) * T.map (Int.castRingHom ℚ)) a =
        (generalPoleU (lam ^ p)
          (Li2Unified.LambdaLift.parameter_power_unit lam hunit.1)
          (parameterPoleHypotheses_of_hunit lam hunit).2.2.1 g r).eval₂
            (algebraMap ℤ_[p] ℚ_[p]) Y -
          (a.val : ℚ_[p]) / (p : ℚ_[p]) *
            (generalPoleV (lam ^ p)
              (Li2Unified.LambdaLift.parameter_power_unit lam hunit.1)
              (parameterPoleHypotheses_of_hunit lam hunit).2.2.1 g r).eval₂
                (algebraMap ℤ_[p] ℚ_[p]) Y := by
  classical
  have hp : 0 < p := by have := a.isLt; omega
  obtain ⟨g₀, r₀, hg₀, he⟩ := general_original_integral_cleared n a hp hsq
  let hu := Li2Unified.LambdaLift.parameter_power_unit lam hunit.1
  let hr := (parameterPoleHypotheses_of_hunit lam hunit).2.2.1
  let g := integralPoleMulRegular (generalPoleCenters (p := p))
    (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) g₀ r₀
  let r := integralPoleMulResidue (generalPoleCenters (p := p))
    (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) r₀
  refine ⟨g, r, ?_, ?_, ?_, ?_⟩
  · exact integralPoleMulRegular_isRestricted _ _ _
      (polynomial_isRestricted _) hg₀ _
  · intro k
    exact generalPoleTest_U_coeff_bound (lam ^ p) hu hr g₀ r₀ T a
      B hB hT k
  · intro k
    exact generalPoleTest_V_coeff_bound (lam ^ p) hu hr g₀ r₀ T a
      B hB hT k
  · simpa only [g, r, hu, hr] using
      (parameterPulledValue_integer_test lam hu hr Y (4 * n) hsq
        ((D n) ^ 3) a (generalPoleScale n a) g₀ hg₀ r₀ he T)

#print axioms actual_general_integer_tests_bounded

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem actual_general_integer_tests_uniform (lam : ℚ) (n : ℕ)
    (a : Fin p) (T : ℤ[X])
    (hsq : 4 * n < p * p)
    (hunit : (lam ≠ 0 ∧ padicValRat p lam = 0) ∧
      (1 - lam ≠ 0 ∧ padicValRat p (1 - lam) = 0))
    (B : ℝ) (hB : 0 ≤ B)
    (hT : ∀ k, ‖(integralDiscTestPolynomial T a).coeff k‖ ≤ B) :
    ∃ g : PowerSeries ℤ_[p], ∃ r : Fin p → ℤ_[p],
      PowerSeries.IsRestricted 1 g ∧
      (∀ k, ‖(generalPoleU (lam ^ p)
        (Li2Unified.LambdaLift.parameter_power_unit lam hunit.1)
        (parameterPoleHypotheses_of_hunit lam hunit).2.2.1 g r).coeff k‖ ≤ B) ∧
      (∀ k, ‖(generalPoleV (lam ^ p)
        (Li2Unified.LambdaLift.parameter_power_unit lam hunit.1)
        (parameterPoleHypotheses_of_hunit lam hunit).2.2.1 g r).coeff k‖ ≤ B) ∧
      ∀ Y : ℚ_[p],
        generalPoleScale n a *
          parameterPulledValue lam
            (parameterPoleHypotheses_of_hunit lam hunit).2.2.1 Y (4 * n)
            (((D n) ^ 3) * T.map (Int.castRingHom ℚ)) a =
          (generalPoleU (lam ^ p)
            (Li2Unified.LambdaLift.parameter_power_unit lam hunit.1)
            (parameterPoleHypotheses_of_hunit lam hunit).2.2.1 g r).eval₂
              (algebraMap ℤ_[p] ℚ_[p]) Y -
            (a.val : ℚ_[p]) / (p : ℚ_[p]) *
              (generalPoleV (lam ^ p)
                (Li2Unified.LambdaLift.parameter_power_unit lam hunit.1)
                (parameterPoleHypotheses_of_hunit lam hunit).2.2.1 g r).eval₂
                  (algebraMap ℤ_[p] ℚ_[p]) Y := by
  classical
  have hp : 0 < p := by have := a.isLt; omega
  obtain ⟨g₀, r₀, hg₀, he⟩ := general_original_integral_cleared n a hp hsq
  let hu := Li2Unified.LambdaLift.parameter_power_unit lam hunit.1
  let hr := (parameterPoleHypotheses_of_hunit lam hunit).2.2.1
  let g := integralPoleMulRegular (generalPoleCenters (p := p))
    (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) g₀ r₀
  let r := integralPoleMulResidue (generalPoleCenters (p := p))
    (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) r₀
  refine ⟨g, r, ?_, ?_, ?_, ?_⟩
  · exact integralPoleMulRegular_isRestricted _ _ _
      (polynomial_isRestricted _) hg₀ _
  · intro k
    exact generalPoleTest_U_coeff_bound (lam ^ p) hu hr g₀ r₀ T a
      B hB hT k
  · intro k
    exact generalPoleTest_V_coeff_bound (lam ^ p) hu hr g₀ r₀ T a
      B hB hT k
  · intro Y
    simpa only [g, r, hu, hr] using
      (parameterPulledValue_integer_test lam hu hr Y (4 * n) hsq
        ((D n) ^ 3) a (generalPoleScale n a) g₀ hg₀ r₀ he T)

#print axioms actual_general_integer_tests_uniform

end
end Li2Unified.Proofs.Hermite

end


end
