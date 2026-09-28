module
public import Li2Unified.Modular.Positive.Packed.P107

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Potential
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

private lemma ray_tail_scalar_linear (x : ℝ) (hx : 18 ≤ x) :
    4*Real.log 4-1-Real.log x-x*Real.log 2+4*Real.log (x+2/25) ≤
      19/10-(x-18)/10 := by
  have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    convert Real.log_pow (2:ℝ) 2 using 1 <;> norm_num
  have h16 : Real.log (16:ℝ) = 4*Real.log 2 := by
    convert Real.log_pow (2:ℝ) 4 using 1 <;> norm_num
  have hxmin := Real.log_le_log (by norm_num : (0:ℝ)<16)
    (show (16:ℝ) ≤ x by linarith)
  rw [h16] at hxmin
  have htan := log_tangent_upper (x+2/25) 20 (by linarith) (by norm_num)
  have hlog2 := Real.log_two_gt_d9
  have hp := mul_nonneg (show 0 ≤ x-18 by linarith)
    (show 0 ≤ Real.log 2-3/10 by linarith)
  rw [h4]
  nlinarith [log_twenty_upper]

private lemma vertical_tail_scalar_linear (y : ℝ) (hy : 2 ≤ y) :
    4*Real.log 4-1-Real.log y-2*Real.pi*y+4*Real.log (56/5+y) ≤
      19/10-(y-2) := by
  have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    convert Real.log_pow (2:ℝ) 2 using 1 <;> norm_num
  have hymin := Real.log_le_log (by norm_num : (0:ℝ)<2) hy
  have htan := log_tangent_upper (56/5+y) (66/5) (by linarith) (by norm_num)
  have hlog2 := Real.log_two_lt_d9
  have hpi := Real.pi_gt_d2
  have hp := mul_nonneg (show 0 ≤ y-2 by linarith)
    (show 0 ≤ 2*Real.pi-43/33 by linarith)
  rw [h4]
  nlinarith [log_sixty_six_fifths_upper]

theorem actual_ray_tail_linear (x : ℝ) (hx : 18 ≤ x) :
    psiRay x ≤ 19/10-(x-18)/10 := by
  have hb := baseRay_tail_upper x (by linarith)
  have hp := comparisonPotential_ray_tail x hx
  have hs := ray_tail_scalar_linear x hx
  unfold psiRay Vray
  linarith

theorem actual_up_tail_linear (y : ℝ) (hy : 2 ≤ y) :
    psiUp y ≤ 19/10-(y-2) := by
  have hb := baseVertical_tail_upper y (by linarith)
  have hp := comparisonPotential_vertical_tail y hy
  have hs := vertical_tail_scalar_linear y hy
  unfold psiUp Vvertical
  rw [abs_of_nonneg (show 0 ≤ y by linarith)]
  linarith

end
end Li2Unified.Proofs.Potential

#print axioms Li2Unified.Proofs.Potential.actual_ray_tail_linear
#print axioms Li2Unified.Proofs.Potential.actual_up_tail_linear

end


end
