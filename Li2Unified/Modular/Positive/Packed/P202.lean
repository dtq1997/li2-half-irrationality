module
public import Li2Unified.Modular.Positive.Packed.P109

set_option backward.privateInPublic true

@[expose] public section

section
/-! Pair logarithmic integrals for the actual horizontal and vertical star layers. -/

open MeasureTheory Set
namespace Li2Unified.Proofs.Energy
noncomputable section
open Li2Unified.ParameterFamily.Energy

theorem horizontal_horizontal (r s : ℝ) (_hr : 0 ≤ r) (_hs : 0 ≤ s) :
    (∫ x in (0:ℝ)..r, ∫ y in (0:ℝ)..s,
      Real.log ‖(x:ℂ)-(y:ℂ)‖) =
      logSecondPrimitive r + logSecondPrimitive s - logSecondPrimitive (r-s) := by
  have heq :
      (∫ x in (0:ℝ)..r, ∫ y in (0:ℝ)..s,
        Real.log ‖(x:ℂ)-(y:ℂ)‖) =
      ∫ x in (0:ℝ)..r, ∫ y in (0:ℝ)..s, Real.log (y-x) := by
    apply intervalIntegral.integral_congr
    intro x _
    apply intervalIntegral.integral_congr
    intro y _
    change Real.log ‖(x:ℂ)-(y:ℂ)‖ = Real.log (y-x)
    rw [log_norm_real_sub_real, show x-y = -(y-x) by ring, Real.log_neg_eq_log]
  rw [heq]
  have h := integral_integral_log_sub 0 s 0 r
  have hz : logSecondPrimitive 0 = 0 := by simp [logSecondPrimitive]
  have hswap : logSecondPrimitive (s-r) = logSecondPrimitive (r-s) := by
    rw [show s-r = -(r-s) by ring, logSecondPrimitive_neg]
  simp only [sub_zero, zero_sub, logSecondPrimitive_neg, hz, hswap] at h
  convert h using 1; ring

theorem vertical_vertical (r s : ℝ) (_hr : 0 ≤ r) (_hs : 0 ≤ s) :
    (∫ x in -r..r, ∫ y in -s..s,
      Real.log ‖(x:ℂ)*Complex.I-(y:ℂ)*Complex.I‖) =
      2*(logSecondPrimitive (r+s)-logSecondPrimitive (r-s)) := by
  have heq :
      (∫ x in -r..r, ∫ y in -s..s,
        Real.log ‖(x:ℂ)*Complex.I-(y:ℂ)*Complex.I‖) =
      ∫ x in -r..r, ∫ y in -s..s, Real.log (y-x) := by
    apply intervalIntegral.integral_congr
    intro x _
    apply intervalIntegral.integral_congr
    intro y _
    change Real.log ‖(x:ℂ)*Complex.I-(y:ℂ)*Complex.I‖ = Real.log (y-x)
    rw [log_norm_imag_sub_imag, show x-y = -(y-x) by ring, Real.log_neg_eq_log]
  rw [heq]
  have h := integral_integral_log_sub (-s) s (-r) r
  have hsum : logSecondPrimitive (s+r) = logSecondPrimitive (r+s) := by
    rw [add_comm]
  have hdiff : logSecondPrimitive (s-r) = logSecondPrimitive (r-s) := by
    rw [show s-r = -(r-s) by ring, logSecondPrimitive_neg]
  have hdiff' : logSecondPrimitive (-s+r) = logSecondPrimitive (r-s) := by
    congr 1
    ring
  have hsum' : logSecondPrimitive (-s-r) = logSecondPrimitive (r+s) := by
    rw [show -s-r = -(r+s) by ring, logSecondPrimitive_neg]
  simp only [sub_neg_eq_add] at h
  rw [hsum, hdiff, hdiff', hsum'] at h
  convert h using 1; ring

theorem horizontal_vertical (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (∫ x in (0:ℝ)..r, ∫ y in -s..s,
      Real.log ‖(x:ℂ)-(y:ℂ)*Complex.I‖) =
      2*(if s = 0 then 0 else perpendicularPrimitive s r) := by
  by_cases hs0 : s = 0
  · subst s
    simp
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  simp only [if_neg hs0]
  have hinner (x : ℝ) (hx : 0 ≤ x) :
      (∫ y in -s..s, Real.log ‖(x:ℂ)-(y:ℂ)*Complex.I‖) =
      2*perpendicularSlice s x := by
    simp_rw [log_norm_real_sub_imag]
    exact integral_log_norm_symmetric_perpendicular hx hspos
  calc
    _ = ∫ x in (0:ℝ)..r, 2*perpendicularSlice s x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hr] at hx
      exact hinner x hx.1
    _ = 2 * ∫ x in (0:ℝ)..r, perpendicularSlice s x := by
      rw [intervalIntegral.integral_const_mul]
    _ = 2*perpendicularPrimitive s r := by
      rw [integral_perpendicularSlice hspos]
      simp [perpendicularPrimitive]

private lemma perpendicularPrimitive_swap {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    perpendicularPrimitive r s = perpendicularPrimitive s r := by
  rw [perpendicularPrimitive_symmetricForm hs.le hr,
    perpendicularPrimitive_symmetricForm hr.le hs]
  ring_nf

theorem vertical_horizontal (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (∫ y in -s..s, ∫ x in (0:ℝ)..r,
      Real.log ‖(y:ℂ)*Complex.I-(x:ℂ)‖) =
      2*(if s = 0 then 0 else perpendicularPrimitive s r) := by
  by_cases hs0 : s = 0
  · subst s
    simp
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  simp only [if_neg hs0]
  by_cases hr0 : r = 0
  · subst r
    simp [perpendicularPrimitive]
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  let f : ℝ → ℝ := fun y => ∫ x in (0:ℝ)..r,
    Real.log ‖(y:ℂ)*Complex.I-(x:ℂ)‖
  have hinner (y : ℝ) (hy : 0 ≤ y) : f y = perpendicularSlice r y := by
    dsimp only [f]
    calc
      _ = ∫ x in (0:ℝ)..r, Real.log ‖(y:ℂ)+(x:ℂ)*Complex.I‖ := by
        apply intervalIntegral.integral_congr
        intro x _
        change Real.log ‖(y:ℂ)*Complex.I-(x:ℂ)‖ =
          Real.log ‖(y:ℂ)+(x:ℂ)*Complex.I‖
        rw [log_norm_imag_sub_real x y, log_norm_coordinate_swap x y]
      _ = _ := integral_log_norm_perpendicular hrpos hy
  have heven (y : ℝ) : f (-y) = f y := by
    apply intervalIntegral.integral_congr
    intro x _
    change Real.log ‖((-y:ℝ):ℂ)*Complex.I-(x:ℂ)‖ =
      Real.log ‖(y:ℂ)*Complex.I-(x:ℂ)‖
    rw [log_norm_imag_sub_real x (-y), log_norm_imag_sub_real x y]
    simp only [Li2.log_norm_real_add_imag, neg_sq]
  have hfun (y : ℝ) : f y = perpendicularSlice r |y| := by
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]
      exact hinner y hy
    · have hy' : 0 ≤ -y := by linarith
      rw [abs_of_neg (lt_of_not_ge hy)]
      calc
        f y = f (-y) := by simpa only [neg_neg] using heven (-y)
        _ = perpendicularSlice r (-y) := hinner (-y) hy'
  have hcont : Continuous (fun y : ℝ => perpendicularSlice r |y|) :=
    (continuous_perpendicularSlice hrpos).comp continuous_abs
  have hf (a b : ℝ) : IntervalIntegrable f volume a b := by
    have hfeq : f = fun y => perpendicularSlice r |y| := funext hfun
    rw [hfeq]
    exact hcont.intervalIntegrable a b
  have hneg : (∫ y in -s..(0:ℝ), f y) = ∫ y in (0:ℝ)..s, f y := by
    have h := intervalIntegral.integral_comp_neg (f := f) (a := (0:ℝ)) (b := s)
    simpa only [heven, neg_zero] using h.symm
  calc
    _ = 2 * ∫ y in (0:ℝ)..s, f y := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hf (-s) 0) (hf 0 s), hneg]
      ring
    _ = 2 * ∫ y in (0:ℝ)..s, perpendicularSlice r y := by
      congr 1
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hs] at hy
      exact hinner y hy.1
    _ = 2*perpendicularPrimitive r s := by
      rw [integral_perpendicularSlice hrpos]
      simp [perpendicularPrimitive]
    _ = 2*perpendicularPrimitive s r := by
      rw [perpendicularPrimitive_swap hrpos hspos]

end
end Li2Unified.Proofs.Energy

end


end
