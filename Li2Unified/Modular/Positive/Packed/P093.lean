module
public import Li2Unified.Modular.Positive.Packed.P092
public import Li2Unified.Modular.Positive.Packed.P083
public import Li2Unified.Modular.Positive.Packed.P088

set_option backward.privateInPublic true

@[expose] public section

section
/-! The finite literal star-density integrals converge to the original
numerator functional, after all three actual endpoint terms vanish. -/

open Polynomial Filter
open scoped Topology
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Instances.PosHalf Li2Unified.ParameterFamily

lemma three_arm_endpoint_diagonal_limit (d : ℕ) (F : ℚ[X]) :
    Tendsto (fun N : ℕ => rayEndpoint d F N - downEndpoint d F (N : ℝ) -
      upEndpoint d F (N : ℝ)) atTop (𝓝 0) := by
  have hR : Tendsto (fun N : ℕ => rayEndpoint d F N) atTop (𝓝 0) :=
    ray_actual_G_endpoint_nat d F
  have hU : Tendsto (fun N : ℕ => upEndpoint d F (N : ℝ)) atTop (𝓝 0) := by
    have h := (upper_actual_G_endpoint d F).comp tendsto_natCast_atTop_atTop
    simpa only [upEndpoint, point_up, mul_assoc] using! h
  have hD : Tendsto (fun N : ℕ => downEndpoint d F (N : ℝ)) atTop (𝓝 0) := by
    have h := (lower_actual_G_endpoint d F).comp tendsto_natCast_atTop_atTop
    simpa only [downEndpoint, point_down, mul_assoc] using! h
  simpa only [sub_zero] using! (hR.sub hD).sub hU

theorem three_arm_density_diagonal_limit (d : ℕ) (F : ℚ[X]) :
    Tendsto (fun N : ℕ => rayDensityFinite d F N +
      downDensityFinite d F (N : ℝ) + upDensityFinite d F (N : ℝ))
      atTop
      (𝓝 ((numeratorFunctional lambda d F).eval₂ (Rat.castHom ℂ) (value : ℂ))) := by
  have hderiv := three_arm_derivative_diagonal_limit d F
  have hboundary := three_arm_endpoint_diagonal_limit d F
  have hsub := hderiv.sub hboundary
  have hlimit : Tendsto (fun N : ℕ =>
      (plainRealIntegral d F N +
        Complex.I * lowerLeftLowerIntegral d F (N : ℝ) -
        Complex.I * upperLeftUpperIntegral d F (N : ℝ)) -
      (rayEndpoint d F N - downEndpoint d F (N : ℝ) -
        upEndpoint d F (N : ℝ))) atTop
      (𝓝 ((numeratorFunctional lambda d F).eval₂ (Rat.castHom ℂ) (value : ℂ))) := by
    simpa only [sub_zero] using! hsub
  apply (tendsto_congr' _).mpr hlimit
  filter_upwards [] with N
  have h := finite_three_arm_ibp d F N (N : ℝ)
  linear_combination -h

end
end Li2Unified.Proofs.Contour

end

section
/-! The convergent finite three-arm contour is the literal star moment. -/

open Polynomial MeasureTheory Set Filter
open scoped Topology
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic
open Li2Unified.Instances.PosHalf Li2Unified.ParameterFamily

private lemma ray_density_finite_tendsto (d : ℕ) (F : ℚ[X]) :
    Tendsto (rayDensityFinite d F) atTop
      (𝓝 (∫ t : ℝ, density ⟨0, by decide⟩ t *
        Li2.originalComplexQuotient d F (point ⟨0, by decide⟩ t)
          ∂(volume.restrict (Ioi (0 : ℝ))))) := by
  simpa only [rayDensityFinite] using!
    (intervalIntegral_tendsto_integral_Ioi (f := fun t : ℝ =>
      density ⟨0, by decide⟩ t *
        Li2.originalComplexQuotient d F (point ⟨0, by decide⟩ t))
      (0 : ℝ) (ray_density_integrableOn d F) tendsto_natCast_atTop_atTop)

private lemma up_density_finite_tendsto (d : ℕ) (F : ℚ[X]) :
    Tendsto (fun N : ℕ => upDensityFinite d F (N : ℝ)) atTop
      (𝓝 (∫ t : ℝ, density ⟨1, by decide⟩ t *
        Li2.originalComplexQuotient d F (point ⟨1, by decide⟩ t)
          ∂(volume.restrict (Ioi (0 : ℝ))))) := by
  simpa only [upDensityFinite] using!
    (intervalIntegral_tendsto_integral_Ioi (f := fun t : ℝ =>
      density ⟨1, by decide⟩ t *
        Li2.originalComplexQuotient d F (point ⟨1, by decide⟩ t))
      (0 : ℝ) (up_density_integrableOn d F) tendsto_natCast_atTop_atTop)

private lemma down_density_finite_tendsto (d : ℕ) (F : ℚ[X]) :
    Tendsto (fun N : ℕ => downDensityFinite d F (N : ℝ)) atTop
      (𝓝 (∫ t : ℝ, density ⟨2, by decide⟩ t *
        Li2.originalComplexQuotient d F (point ⟨2, by decide⟩ t)
          ∂(volume.restrict (Ioi (0 : ℝ))))) := by
  simpa only [downDensityFinite] using!
    (intervalIntegral_tendsto_integral_Ioi (f := fun t : ℝ =>
      density ⟨2, by decide⟩ t *
        Li2.originalComplexQuotient d F (point ⟨2, by decide⟩ t))
      (0 : ℝ) (down_density_integrableOn d F) tendsto_natCast_atTop_atTop)

theorem three_arm_density_star_limit (d : ℕ) (F : ℚ[X]) :
    Tendsto (fun N : ℕ => rayDensityFinite d F N +
      downDensityFinite d F (N : ℝ) + upDensityFinite d F (N : ℝ))
      atTop (𝓝 (starMoment d F)) := by
  have hstar : starMoment d F =
      (∫ t : ℝ, density ⟨0, by decide⟩ t *
        Li2.originalComplexQuotient d F (point ⟨0, by decide⟩ t)
          ∂(volume.restrict (Ioi (0 : ℝ)))) +
      (∫ t : ℝ, density ⟨2, by decide⟩ t *
        Li2.originalComplexQuotient d F (point ⟨2, by decide⟩ t)
          ∂(volume.restrict (Ioi (0 : ℝ)))) +
      (∫ t : ℝ, density ⟨1, by decide⟩ t *
        Li2.originalComplexQuotient d F (point ⟨1, by decide⟩ t)
          ∂(volume.restrict (Ioi (0 : ℝ)))) := by
    rw [starMoment_eq_arm_integrals, Fin.sum_univ_three]
    have h0 : (⟨0, by decide⟩ : Fin 3) = 0 := by decide
    have h1 : (⟨1, by decide⟩ : Fin 3) = 1 := by decide
    have h2 : (⟨2, by decide⟩ : Fin 3) = 2 := by decide
    simp only [h0, h1, h2]
    ring
  rw [hstar]
  exact ((ray_density_finite_tendsto d F).add
    (down_density_finite_tendsto d F)).add (up_density_finite_tendsto d F)

theorem actual_original_functional_star (d : ℕ) (F : ℚ[X]) :
    (numeratorFunctional lambda d F).eval₂ (Rat.castHom ℂ) (value : ℂ) =
      starMoment d F := by
  exact tendsto_nhds_unique
    (three_arm_density_diagonal_limit d F)
    (three_arm_density_star_limit d F)

end
end Li2Unified.Proofs.Contour

end


end
