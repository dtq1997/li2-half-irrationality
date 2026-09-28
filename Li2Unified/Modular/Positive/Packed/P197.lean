module
public import Li2Unified.Modular.Base.FiniteSignedEnergyBound
public import Mathlib.Tactic

set_option backward.privateInPublic true

@[expose] public section

section
/-! The finite signed-energy algebra for complex rather than real points.
The hypotheses are the actual circle/measure estimates still to be supplied. -/

open scoped BigOperators
namespace Li2Unified.Proofs.Contour
noncomputable section

theorem complex_signed_energy_circle_sum_lower {h : ℕ} (x : Fin h → ℂ)
    (T ε : ℝ) (E : Option (Fin h) → Option (Fin h) → ℝ)
    (hEsym : ∀ k l, E k l = E l k)
    (hdiag : ∀ i : Fin h, E (some i) (some i) = T ^ 2 * Real.log ε)
    (hoff : ∀ i j : Fin h, i ≠ j →
      T ^ 2 * Real.log ‖x j - x i‖ ≤ E (some i) (some j)) :
    (h : ℝ) * T ^ 2 * Real.log ε +
      2 * T ^ 2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i,
        Real.log ‖x j - x i‖) ≤
      ∑ i : Fin h, ∑ j : Fin h, E (some i) (some j) := by
  classical
  have hdiag_sum : (∑ i : Fin h, E (some i) (some i)) =
      (h : ℝ) * T ^ 2 * Real.log ε := by
    simp only [hdiag, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  have htri : T ^ 2 *
      (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log ‖x j - x i‖) ≤
      ∑ i : Fin h, ∑ j ∈ Finset.Ioi i, E (some i) (some j) := by
    calc
      _ = ∑ i : Fin h, ∑ j ∈ Finset.Ioi i,
          T ^ 2 * Real.log ‖x j - x i‖ := by
        simp only [Finset.mul_sum]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j hj
        exact hoff i j (ne_of_lt (Finset.mem_Ioi.mp hj))
  calc
    _ = (∑ i : Fin h, E (some i) (some i)) +
      2 * (T ^ 2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i,
        Real.log ‖x j - x i‖)) := by
        rw [hdiag_sum]
        ring
    _ ≤ (∑ i : Fin h, E (some i) (some i)) +
      2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, E (some i) (some j)) := by
        have hm := mul_le_mul_of_nonneg_left htri
          (by norm_num : (0 : ℝ) ≤ 2)
        linarith only [hm]
    _ = _ := (Li2.symmetric_double_sum_eq_diag_add_two_Ioi
      (fun i j : Fin h => E (some i) (some j))
      (fun i j => hEsym (some i) (some j))).symm

private theorem complex_signed_energy_clear_denominator
    {d S B I : ℝ} (hd : 0 < d)
    (he : (1 / d) ^ 2 * S - (1 / d) * B - (1 / d) * B + I ≤ 0) :
    S - 2 * d * B + d ^ 2 * I ≤ 0 := by
  calc
    _ = d ^ 2 * ((1 / d) ^ 2 * S - (1 / d) * B -
        (1 / d) * B + I) := by
      field_simp [ne_of_gt hd]
      ring
    _ ≤ 0 := by
      simpa only [mul_zero] using
        (mul_le_mul_of_nonneg_left he (sq_nonneg d))

theorem complex_signed_energy_log_bound {h : ℕ} (hh : 0 < h)
    (T ε M : ℝ) (hT : 0 < T) (_hε : 0 < ε) (_hM : 0 ≤ M)
    (x : Fin h → ℂ) (L : Fin h → ℝ) (I : ℝ)
    (E : Option (Fin h) → Option (Fin h) → ℝ)
    (hEsym : ∀ k l, E k l = E l k)
    (henergy : let w : Option (Fin h) → ℝ := fun k => match k with
      | none => -1 | some _ => 1 / ((h : ℝ) * T)
      (∑ k : Option (Fin h), ∑ l : Option (Fin h),
        w k * w l * E k l) ≤ 0)
    (h00 : E none none = I)
    (hcross : ∀ i : Fin h, E (some i) none ≤
      T * (L i + 2 * M * ε))
    (hdiag : ∀ i : Fin h, E (some i) (some i) =
      T ^ 2 * Real.log ε)
    (hoff : ∀ i j : Fin h, i ≠ j →
      T ^ 2 * Real.log ‖x j - x i‖ ≤ E (some i) (some j)) :
    2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i,
      Real.log ‖x j - x i‖) ≤
      2 * (h : ℝ) * (∑ i : Fin h, L i) -
        (h : ℝ) ^ 2 * I - (h : ℝ) * Real.log ε +
        4 * M * (h : ℝ) ^ 2 * ε := by
  classical
  have hhR : 0 < (h : ℝ) := Nat.cast_pos.mpr hh
  have hd : 0 < (h : ℝ) * T := mul_pos hhR hT
  have hcross_sym : (∑ i : Fin h, E none (some i)) =
      ∑ i : Fin h, E (some i) none := by
    apply Finset.sum_congr rfl
    intro i _
    exact hEsym none (some i)
  have he := henergy
  have hoption := Li2.option_signed_weight_double_sum
    (1 / ((h : ℝ) * T)) E
  dsimp only at he hoption
  have he' := hoption.symm.le.trans he
  rw [h00, hcross_sym] at he'
  have hscaled : (∑ i : Fin h, ∑ j : Fin h,
      E (some i) (some j)) -
      2 * ((h : ℝ) * T) * (∑ i : Fin h, E (some i) none) +
      ((h : ℝ) * T) ^ 2 * I ≤ 0 :=
    complex_signed_energy_clear_denominator hd he'
  have hcircle := complex_signed_energy_circle_sum_lower
    x T ε E hEsym hdiag hoff
  have hcross_sum := Li2.finite_signed_energy_cross_sum_upper
    T M ε L E hcross
  have hblock : (∑ i : Fin h, ∑ j : Fin h,
      E (some i) (some j)) ≤
      2 * ((h : ℝ) * T) *
        (T * ((∑ i : Fin h, L i) + 2 * M * ε * (h : ℝ))) -
      ((h : ℝ) * T) ^ 2 * I := by
    calc
      _ ≤ 2 * ((h : ℝ) * T) *
          (∑ i : Fin h, E (some i) none) -
          ((h : ℝ) * T) ^ 2 * I := by
        linarith only [hscaled]
      _ ≤ _ := sub_le_sub_right
        (mul_le_mul_of_nonneg_left hcross_sum
          (show 0 ≤ 2 * ((h : ℝ) * T) by positivity)) _
  refine le_of_mul_le_mul_left (a := T ^ 2) ?_
    (sq_pos_of_pos hT)
  calc
    T ^ 2 * (2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i,
      Real.log ‖x j - x i‖)) =
      ((h : ℝ) * T ^ 2 * Real.log ε +
        2 * T ^ 2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i,
          Real.log ‖x j - x i‖)) -
        (h : ℝ) * T ^ 2 * Real.log ε := by ring
    _ ≤ (∑ i : Fin h, ∑ j : Fin h, E (some i) (some j)) -
      (h : ℝ) * T ^ 2 * Real.log ε :=
      sub_le_sub_right hcircle _
    _ ≤ (2 * ((h : ℝ) * T) *
      (T * ((∑ i : Fin h, L i) + 2 * M * ε * (h : ℝ))) -
      ((h : ℝ) * T) ^ 2 * I) -
      (h : ℝ) * T ^ 2 * Real.log ε :=
      sub_le_sub_right hblock _
    _ = T ^ 2 * (2 * (h : ℝ) * (∑ i : Fin h, L i) -
      (h : ℝ) ^ 2 * I - (h : ℝ) * Real.log ε +
      4 * M * (h : ℝ) ^ 2 * ε) := by ring

end
end Li2Unified.Proofs.Contour

end


end
