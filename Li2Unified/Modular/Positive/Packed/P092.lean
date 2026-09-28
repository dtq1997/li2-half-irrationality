module
public import Li2Unified.Modular.Positive.Packed.P090
public import Li2Unified.Modular.Positive.Packed.P091

set_option backward.privateInPublic true

@[expose] public section

section
/-! Exact finite three-arm integration by parts, including endpoint cancellation. -/

open Polynomial MeasureTheory
open scoped Interval
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

def rayEndpoint (d : ℕ) (F : ℚ[X]) (N : ℕ) : ℂ :=
  power (((N : ℝ) + 1 / 2 : ℝ) : ℂ) *
    Li2.originalContourG d F ((((N : ℝ) + 1 / 2 : ℝ) : ℂ))

def upEndpoint (d : ℕ) (F : ℚ[X]) (T : ℝ) : ℂ :=
  (power (Li2.originalContourPoint T) * kappaPlus (Li2.originalContourPoint T)) *
    Li2.originalContourG d F (Li2.originalContourPoint T)

def downEndpoint (d : ℕ) (F : ℚ[X]) (T : ℝ) : ℂ :=
  (power (Li2.originalContourPoint (-T)) * kappaMinus (Li2.originalContourPoint (-T))) *
    Li2.originalContourG d F (Li2.originalContourPoint (-T))

private lemma center_endpoint_balance (d : ℕ) (F : ℚ[X]) :
    -(power (1 / 2 : ℂ) * Li2.originalContourG d F (1 / 2 : ℂ)) +
      (power (1 / 2 : ℂ) * kappaMinus (1 / 2 : ℂ)) *
        Li2.originalContourG d F (1 / 2 : ℂ) +
      (power (1 / 2 : ℂ) * kappaPlus (1 / 2 : ℂ)) *
        Li2.originalContourG d F (1 / 2 : ℂ) = 0 := by
  have h := endpoint_balance
  linear_combination (power (1 / 2 : ℂ) *
    Li2.originalContourG d F (1 / 2 : ℂ)) * h

theorem finite_three_arm_ibp (d : ℕ) (F : ℚ[X]) (N : ℕ) (T : ℝ) :
    plainRealIntegral d F N +
        Complex.I * lowerLeftLowerIntegral d F T -
        Complex.I * upperLeftUpperIntegral d F T =
      rayDensityFinite d F N + downDensityFinite d F T + upDensityFinite d F T +
        rayEndpoint d F N - downEndpoint d F T - upEndpoint d F T := by
  have h0 : Li2.originalContourPoint 0 = (1 / 2 : ℂ) := by
    simp [Li2.originalContourPoint]
  have hR : plainRealIntegral d F N =
      rayEndpoint d F N -
        power (1 / 2 : ℂ) * Li2.originalContourG d F (1 / 2 : ℂ) +
        rayDensityFinite d F N := by
    rw [rayDensityFinite_eq]
    exact ray_finite_ibp d F N
  have hL : Complex.I * lowerLeftLowerIntegral d F T =
      (power (1 / 2 : ℂ) * kappaMinus (1 / 2 : ℂ)) *
        Li2.originalContourG d F (1 / 2 : ℂ) -
      downEndpoint d F T + downDensityFinite d F T := by
    rw [downDensityFinite_eq]
    simpa only [h0, downEndpoint, sub_neg_eq_add] using!
      lowerLeftLower_finite_ibp d F T
  have hU : -(Complex.I * upperLeftUpperIntegral d F T) =
      -(upEndpoint d F T) +
        (power (1 / 2 : ℂ) * kappaPlus (1 / 2 : ℂ)) *
          Li2.originalContourG d F (1 / 2 : ℂ) +
        upDensityFinite d F T := by
    rw [upDensityFinite_eq]
    have h := upperLeftUpper_finite_ibp d F T
    rw [h0] at h
    dsimp [upEndpoint]
    linear_combination -h
  have hC := center_endpoint_balance d F
  linear_combination hR + hL + hU + hC

end
end Li2Unified.Proofs.Contour

end


end
