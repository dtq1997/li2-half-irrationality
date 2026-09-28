module
public import Li2Unified.Modular.Positive.Packed.P084
public import Li2Unified.Modular.Positive.Packed.P087

set_option backward.privateInPublic true

@[expose] public section

section
/-! The three literal star arms are integrable for the product measure. -/

open Polynomial MeasureTheory Set
namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

private def armMeasure (b : Fin 3) : Measure (Fin 3 × ℝ) :=
  Measure.map (Prod.mk b) (volume.restrict (Ioi (0 : ℝ)))

private lemma contourMeasure_eq_arm_sum :
    contourMeasure = Measure.sum armMeasure := by
  unfold contourMeasure Measure.count armMeasure
  rw [Measure.prod_sum_left]
  simp_rw [Measure.dirac_prod]

private lemma arm_embedding (b : Fin 3) : MeasurableEmbedding (Prod.mk b : ℝ → Fin 3 × ℝ) :=
  measurableEmbedding_prodMk_left b

private lemma arm_integrable (d : ℕ) (F : ℚ[X]) (b : Fin 3) :
    Integrable (fun v : Fin 3 × ℝ => density v.1 v.2 *
      Li2.originalComplexQuotient d F (point v.1 v.2)) (armMeasure b) := by
  rw [armMeasure, (arm_embedding b).integrable_map_iff]
  fin_cases b
  · simpa using ray_density_integrableOn d F
  · simpa using up_density_integrableOn d F
  · simpa using down_density_integrableOn d F

lemma actual_star_moment_integrable (d : ℕ) (F : ℚ[X]) :
    Integrable (fun v : Fin 3 × ℝ => density v.1 v.2 *
      Li2.originalComplexQuotient d F (point v.1 v.2)) contourMeasure := by
  rw [contourMeasure_eq_arm_sum]
  apply integrable_sum_measure (arm_integrable d F)
  exact summable_of_hasFiniteSupport (Set.finite_univ.subset (by simp))

lemma starMoment_eq_arm_integrals (d : ℕ) (F : ℚ[X]) :
    starMoment d F = ∑ b : Fin 3, ∫ t : ℝ,
      density b t * Li2.originalComplexQuotient d F (point b t)
        ∂(volume.restrict (Ioi (0 : ℝ))) := by
  unfold starMoment
  rw [contourMeasure_eq_arm_sum]
  rw [integral_sum_measure (by
    simpa only [← contourMeasure_eq_arm_sum] using actual_star_moment_integrable d F)]
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro b _
  simpa only [armMeasure] using
    (arm_embedding b).integral_map
      (fun v : Fin 3 × ℝ => density v.1 v.2 *
        Li2.originalComplexQuotient d F (point v.1 v.2))

end
end Li2Unified.Proofs.Contour

end


end
