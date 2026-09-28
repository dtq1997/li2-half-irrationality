module
public import Li2Unified.Modular.Positive.Packed.P078

set_option backward.privateInPublic true

@[expose] public section

section
/-! Exact derivatives of the two star kernels away from their poles. -/

namespace Li2Unified.Proofs.Contour
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

lemma kappaPlus_deriv (z : ℂ)
    (hz : 1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * z) ≠ 0) :
    deriv kappaPlus z =
      (-(2 * (Real.pi : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * z)) /
        (1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * z)) ^ 2 := by
  let c : ℂ := -(2 * (Real.pi : ℂ) * Complex.I)
  have he : HasDerivAt (fun w : ℂ => Complex.exp (c * w))
      (Complex.exp (c * z) * c) z := by
    simpa only [mul_one] using ((hasDerivAt_id z).const_mul c).cexp
  have hd : HasDerivAt (fun w : ℂ => 1 - Complex.exp (c * w))
      (-(Complex.exp (c * z) * c)) z := by
    simpa using (hasDerivAt_const z (1 : ℂ)).sub he
  have hi := hd.inv (by simpa only [c] using hz)
  have hfun : kappaPlus = (fun w : ℂ => (1 - Complex.exp (c * w))⁻¹) := by
    funext w
    simp only [kappaPlus, one_div, c]
  rw [hfun]
  calc
    deriv (fun w : ℂ => (1 - Complex.exp (c * w))⁻¹) z =
        -(-(Complex.exp (c * z) * c)) /
          (1 - Complex.exp (c * z)) ^ 2 := hi.deriv
    _ = _ := by dsimp [c]; ring

lemma kappaMinus_deriv (z : ℂ)
    (hz : 1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z) ≠ 0) :
    deriv kappaMinus z =
      ((2 * (Real.pi : ℂ) * Complex.I) *
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) /
        (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) ^ 2 := by
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have he : HasDerivAt (fun w : ℂ => Complex.exp (c * w))
      (Complex.exp (c * z) * c) z := by
    simpa only [mul_one] using ((hasDerivAt_id z).const_mul c).cexp
  have hd : HasDerivAt (fun w : ℂ => 1 - Complex.exp (c * w))
      (-(Complex.exp (c * z) * c)) z := by
    simpa using (hasDerivAt_const z (1 : ℂ)).sub he
  have hi := hd.inv (by simpa only [c] using hz)
  have hfun : kappaMinus = (fun w : ℂ => (1 - Complex.exp (c * w))⁻¹) := by
    funext w
    simp only [kappaMinus, one_div, c]
  rw [hfun]
  calc
    deriv (fun w : ℂ => (1 - Complex.exp (c * w))⁻¹) z =
        -(-(Complex.exp (c * z) * c)) /
          (1 - Complex.exp (c * z)) ^ 2 := hi.deriv
    _ = _ := by dsimp [c]; ring

private lemma exp_ratio_bound (a : ℝ) :
    Real.exp a / (1 + Real.exp a) ^ 2 ≤ Real.exp (-a) := by
  have he : 0 < Real.exp a := Real.exp_pos a
  have hsq : (Real.exp a) ^ 2 ≤ (1 + Real.exp a) ^ 2 := by
    nlinarith [he]
  calc
    Real.exp a / (1 + Real.exp a) ^ 2 ≤
        Real.exp a / (Real.exp a) ^ 2 :=
      div_le_div_of_nonneg_left he.le (sq_pos_of_pos he) hsq
    _ = (Real.exp a)⁻¹ := by field_simp [ne_of_gt he]
    _ = Real.exp (-a) := (Real.exp_neg a).symm

private lemma plus_den_upper_ne (y : ℝ) :
    1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
      point ⟨1, by decide⟩ y) ≠ 0 := by
  rw [exp_upper_arm]
  have h : (1 + Real.exp (2 * Real.pi * y) : ℝ) ≠ 0 :=
    ne_of_gt (by positivity)
  have hc : (1 : ℂ) + ((Real.exp (2 * Real.pi * y) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h
  simpa only [sub_neg_eq_add] using hc

private lemma minus_den_lower_ne (y : ℝ) :
    1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
      point ⟨2, by decide⟩ y) ≠ 0 := by
  rw [exp_lower_arm]
  have h : (1 + Real.exp (2 * Real.pi * y) : ℝ) ≠ 0 :=
    ne_of_gt (by positivity)
  have hc : (1 : ℂ) + ((Real.exp (2 * Real.pi * y) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h
  simpa only [sub_neg_eq_add] using hc

lemma kappaPlus_deriv_upper_norm_le (y : ℝ) :
    ‖deriv kappaPlus (point ⟨1, by decide⟩ y)‖ ≤
      2 * Real.pi * Real.exp (-2 * Real.pi * y) := by
  have hE : 0 < Real.exp (2 * Real.pi * y) := Real.exp_pos _
  have hden : 0 < 1 + Real.exp (2 * Real.pi * y) := by linarith
  have hnorm : ‖(1 : ℂ) + ((Real.exp (2 * Real.pi * y) : ℝ) : ℂ)‖ =
      1 + Real.exp (2 * Real.pi * y) := by
    calc
      _ = ‖((1 + Real.exp (2 * Real.pi * y) : ℝ) : ℂ)‖ := by
        congr 1
        push_cast
        ring
      _ = |1 + Real.exp (2 * Real.pi * y)| := Complex.norm_real _
      _ = _ := abs_of_pos hden
  calc
    ‖deriv kappaPlus (point ⟨1, by decide⟩ y)‖ =
        2 * Real.pi *
          (Real.exp (2 * Real.pi * y) /
            (1 + Real.exp (2 * Real.pi * y)) ^ 2) := by
      rw [kappaPlus_deriv _ (plus_den_upper_ne y), exp_upper_arm]
      simp only [norm_div, norm_mul, norm_neg, norm_pow, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        abs_of_pos hE, sub_neg_eq_add, hnorm]
      rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
      ring
    _ ≤ 2 * Real.pi * Real.exp (-2 * Real.pi * y) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [show -2 * Real.pi * y = -(2 * Real.pi * y) by ring] using
        exp_ratio_bound (2 * Real.pi * y)

lemma kappaMinus_deriv_lower_norm_le (y : ℝ) :
    ‖deriv kappaMinus (point ⟨2, by decide⟩ y)‖ ≤
      2 * Real.pi * Real.exp (-2 * Real.pi * y) := by
  have hE : 0 < Real.exp (2 * Real.pi * y) := Real.exp_pos _
  have hden : 0 < 1 + Real.exp (2 * Real.pi * y) := by linarith
  have hnorm : ‖(1 : ℂ) + ((Real.exp (2 * Real.pi * y) : ℝ) : ℂ)‖ =
      1 + Real.exp (2 * Real.pi * y) := by
    calc
      _ = ‖((1 + Real.exp (2 * Real.pi * y) : ℝ) : ℂ)‖ := by
        congr 1
        push_cast
        ring
      _ = |1 + Real.exp (2 * Real.pi * y)| := Complex.norm_real _
      _ = _ := abs_of_pos hden
  calc
    ‖deriv kappaMinus (point ⟨2, by decide⟩ y)‖ =
        2 * Real.pi *
          (Real.exp (2 * Real.pi * y) /
            (1 + Real.exp (2 * Real.pi * y)) ^ 2) := by
      rw [kappaMinus_deriv _ (minus_den_lower_ne y), exp_lower_arm]
      simp only [norm_div, norm_mul, norm_neg, norm_pow, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        abs_of_pos hE, sub_neg_eq_add, hnorm]
      rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
      ring
    _ ≤ 2 * Real.pi * Real.exp (-2 * Real.pi * y) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [show -2 * Real.pi * y = -(2 * Real.pi * y) by ring] using
        exp_ratio_bound (2 * Real.pi * y)

end
end Li2Unified.Proofs.Contour

end


end
