module
public import Li2Unified.Modular.Base.FiniteSignedEnergyAlgebra
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

set_option backward.privateInPublic true

@[expose] public section
open scoped BigOperators
namespace Li2
theorem finite_signed_energy_circle_sum_lower {h : ℕ} (x : Fin h → ℝ) (T ε : ℝ)
    (E : Option (Fin h) → Option (Fin h) → ℝ)
    (hEsym : ∀ k l, E k l = E l k)
    (hdiag : ∀ i : Fin h, E (some i) (some i) = T ^ 2 * Real.log ε)
    (hoff : ∀ i j : Fin h, i ≠ j → T ^ 2 * Real.log |x j - x i| ≤ E (some i) (some j)) :
    (h : ℝ) * T ^ 2 * Real.log ε +
      2 * T ^ 2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) ≤
      ∑ i : Fin h, ∑ j : Fin h, E (some i) (some j) := by
  classical
  have hdiag_sum : (∑ i : Fin h, E (some i) (some i)) = (h : ℝ) * T ^ 2 * Real.log ε := by
    simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  have htri : T ^ 2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) ≤
      ∑ i : Fin h, ∑ j ∈ Finset.Ioi i, E (some i) (some j) := by
    calc
      _ = ∑ i : Fin h, ∑ j ∈ Finset.Ioi i, T ^ 2 * Real.log |x j - x i| := by
        simp only [Finset.mul_sum]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j hj
        exact hoff i j (ne_of_lt (Finset.mem_Ioi.mp hj))
  calc
    _ = (∑ i : Fin h, E (some i) (some i)) +
      2 * (T ^ 2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|)) := by
        rw [hdiag_sum]; ring
    _ ≤ (∑ i : Fin h, E (some i) (some i)) +
      2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, E (some i) (some j)) :=
        by
          have hm := mul_le_mul_of_nonneg_left htri (by norm_num : (0 : ℝ) ≤ 2)
          linarith only [hm]
    _ = _ := (symmetric_double_sum_eq_diag_add_two_Ioi
      (fun i j : Fin h => E (some i) (some j)) (fun i j => hEsym (some i) (some j))).symm
theorem finite_signed_energy_cross_sum_upper {h : ℕ} (T M ε : ℝ) (L : Fin h → ℝ)
    (E : Option (Fin h) → Option (Fin h) → ℝ)
    (hcross : ∀ i : Fin h, E (some i) none ≤ T * (L i + 2 * M * ε)) :
    (∑ i : Fin h, E (some i) none) ≤ T * ((∑ i : Fin h, L i) + 2 * M * ε * (h : ℝ)) := by
  classical
  calc
    _ ≤ ∑ i : Fin h, T * (L i + 2 * M * ε) := by
      apply Finset.sum_le_sum; intro i _; exact hcross i
    _ = T * (∑ i : Fin h, (L i + 2 * M * ε)) := by rw [Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
private theorem finite_signed_energy_clear_denominator {d S B I : ℝ} (hd : 0 < d)
    (he : (1 / d) ^ 2 * S - (1 / d) * B - (1 / d) * B + I ≤ 0) :
    S - 2 * d * B + d ^ 2 * I ≤ 0 := by
  calc
    _ = d ^ 2 * ((1 / d) ^ 2 * S - (1 / d) * B - (1 / d) * B + I) := by
      field_simp [ne_of_gt hd] <;> ring
    _ ≤ 0 := by
      simpa only [mul_zero] using (mul_le_mul_of_nonneg_left he (sq_nonneg d))
theorem finite_signed_energy_log_bound {h : ℕ} (hh : 0 < h)
    (T ε M : ℝ) (hT : 0 < T) (_hε : 0 < ε) (_hM : 0 ≤ M)
    (x L : Fin h → ℝ) (_hx : Function.Injective x) (I : ℝ)
    (E : Option (Fin h) → Option (Fin h) → ℝ)
    (hEsym : ∀ k l, E k l = E l k)
    (henergy : let w : Option (Fin h) → ℝ := fun k => match k with
      | none => -1 | some _ => 1 / ((h : ℝ) * T)
      (∑ k : Option (Fin h), ∑ l : Option (Fin h), w k * w l * E k l) ≤ 0)
    (h00 : E none none = I)
    (hcross : ∀ i : Fin h, E (some i) none ≤ T * (L i + 2 * M * ε))
    (hdiag : ∀ i : Fin h, E (some i) (some i) = T ^ 2 * Real.log ε)
    (hoff : ∀ i j : Fin h, i ≠ j → T ^ 2 * Real.log |x j - x i| ≤ E (some i) (some j)) :
    2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) ≤
      2 * (h : ℝ) * (∑ i : Fin h, L i) - (h : ℝ) ^ 2 * I - (h : ℝ) * Real.log ε +
      4 * M * (h : ℝ) ^ 2 * ε := by
  classical
  have hhR : 0 < (h : ℝ) := Nat.cast_pos.mpr hh
  have hd : 0 < (h : ℝ) * T := mul_pos hhR hT
  have hcross_sym : (∑ i : Fin h, E none (some i)) = ∑ i : Fin h, E (some i) none := by
    apply Finset.sum_congr rfl; intro i _; exact hEsym none (some i)
  have he := henergy
  have hoption := option_signed_weight_double_sum (1 / ((h : ℝ) * T)) E
  dsimp only at he hoption
  have he' := hoption.symm.le.trans he
  rw [h00, hcross_sym] at he'
  have hscaled : (∑ i : Fin h, ∑ j : Fin h, E (some i) (some j)) -
      2 * ((h : ℝ) * T) * (∑ i : Fin h, E (some i) none) + ((h : ℝ) * T) ^ 2 * I ≤ 0 :=
    finite_signed_energy_clear_denominator hd he'
  have hcircle := finite_signed_energy_circle_sum_lower x T ε E hEsym hdiag hoff
  have hcross_sum := finite_signed_energy_cross_sum_upper T M ε L E hcross
  have hblock : (∑ i : Fin h, ∑ j : Fin h, E (some i) (some j)) ≤
      2 * ((h : ℝ) * T) * (T * ((∑ i : Fin h, L i) + 2 * M * ε * (h : ℝ))) -
      ((h : ℝ) * T) ^ 2 * I := by
    calc
      _ ≤ 2 * ((h : ℝ) * T) * (∑ i : Fin h, E (some i) none) - ((h : ℝ) * T) ^ 2 * I := by
        linarith only [hscaled]
      _ ≤ _ := sub_le_sub_right (mul_le_mul_of_nonneg_left hcross_sum
        (show 0 ≤ 2 * ((h : ℝ) * T) by positivity)) _
  refine le_of_mul_le_mul_left (a := T ^ 2) ?_ (sq_pos_of_pos hT)
  calc
    T ^ 2 * (2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|)) =
      ((h : ℝ) * T ^ 2 * Real.log ε +
        2 * T ^ 2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|)) -
        (h : ℝ) * T ^ 2 * Real.log ε := by ring
    _ ≤ (∑ i : Fin h, ∑ j : Fin h, E (some i) (some j)) - (h : ℝ) * T ^ 2 * Real.log ε :=
      sub_le_sub_right hcircle _
    _ ≤ (2 * ((h : ℝ) * T) * (T * ((∑ i : Fin h, L i) + 2 * M * ε * (h : ℝ))) -
        ((h : ℝ) * T) ^ 2 * I) - (h : ℝ) * T ^ 2 * Real.log ε := sub_le_sub_right hblock _
    _ = T ^ 2 * (2 * (h : ℝ) * (∑ i : Fin h, L i) - (h : ℝ) ^ 2 * I -
      (h : ℝ) * Real.log ε + 4 * M * (h : ℝ) ^ 2 * ε) := by ring
end Li2

end
