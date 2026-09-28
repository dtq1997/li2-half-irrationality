module
public import Li2Unified.Modular.Base.DecayTwoAdic
public import Li2Unified.Modular.Base.PrimeEndpointTerms
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecificLimits.Basic

set_option backward.privateInPublic true

@[expose] public section

open Finset Filter Topology
namespace Li2.PrimeSums
noncomputable section

lemma natLog_seven_sub_two_div_tendsto_zero (b : ℕ) :
    Tendsto (fun n : ℕ => (Nat.log b (7*n-2) : ℝ)/(n : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (7*(n : ℝ))/(n : ℝ))
      atTop (𝓝 (0 : ℝ)) :=
    (log_scaled_div_tendsto_zero (c := (7 : ℝ)) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n : ℕ =>
      (Real.log (7*(n : ℝ))/(n : ℝ))/Real.log (b : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_div] using! hlog.div_const (Real.log (b : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu ?_ ?_
  · intro n
    positivity
  · intro n
    have hL : (Nat.log b (7*n-2) : ℝ) ≤
        Real.log (7*(n : ℝ))/Real.log (b : ℝ) := by
      calc
        (Nat.log b (7*n-2) : ℝ) ≤ (Nat.log b (7*n) : ℝ) := by
          exact_mod_cast (Nat.log_mono_right (Nat.sub_le (7*n) 2))
        _ ≤ Real.log (7*(n : ℝ))/Real.log (b : ℝ) := by
          simpa only [Real.logb, Nat.cast_mul, Nat.cast_ofNat] using! (Real.natLog_le_logb (7*n) b)
    calc
      (Nat.log b (7*n-2) : ℝ)/(n : ℝ) ≤
          (Real.log (7*(n : ℝ))/Real.log (b : ℝ))/(n : ℝ) :=
        div_le_div_of_nonneg_right hL (Nat.cast_nonneg n)
      _ = (Real.log (7*(n : ℝ))/(n : ℝ))/Real.log (b : ℝ) := by ring

lemma natLog_error_square_tendsto_zero (b : ℕ) :
    Tendsto (fun n : ℕ =>
      (4*(n : ℝ)*(Nat.log b (7*n-2) : ℝ))/(n : ℝ)^2)
      atTop (𝓝 (0 : ℝ)) := by
  have h : Tendsto (fun n : ℕ => 4*((Nat.log b (7*n-2) : ℝ)/(n : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using! (natLog_seven_sub_two_div_tendsto_zero b).const_mul (4 : ℝ)
  apply (tendsto_congr' ?_).mp h
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hn0] <;> ring

#check natLog_error_square_tendsto_zero

lemma A2_upper_quadratic (n : ℕ) (hn : 1 ≤ n) : 3*A2 n ≤ 8*n^2 := by
  have hk : ∀ k ∈ Finset.range (2*n-1),
      3*(n+1+k/3) ≤ 3*n+3+k := by
    intro k hk
    omega
  have hs : 3*A2 n ≤ (2*n-1)*(3*n+3) + ∑ k ∈ Finset.range (2*n-1), k := by
    calc
      _ = ∑ k ∈ Finset.range (2*n-1), 3*(n+1+k/3) := by
        rw [← Finset.mul_sum]
        rfl
      _ ≤ ∑ k ∈ Finset.range (2*n-1), (3*n+3+k) := Finset.sum_le_sum hk
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hid := Finset.sum_range_id_mul_two (2*n-1)
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2*(1+t)-1 = 2*t+1 by omega] at hs hid
  rw [show 2*t+1-1 = 2*t by omega] at hid
  nlinarith only [hs, hid]

#check A2_upper_quadratic

lemma A2_ratio_tendsto :
    Tendsto (fun n : ℕ => (A2 n : ℝ)/(n : ℝ)^2)
      atTop (𝓝 (8/3 : ℝ)) := by
  have hlo : Tendsto (fun n : ℕ => (8/3 : ℝ)-(4/3 : ℝ)/(n : ℝ))
      atTop (𝓝 (8/3 : ℝ)) := by
    simpa only [sub_zero] using!
      (tendsto_const_nhds (x := (8/3 : ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat (4/3 : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hA : 8*(n : ℝ)^2 ≤ 3*(A2 n : ℝ)+4*(n : ℝ) := by
      exact_mod_cast (Li2.A2_lower n hn)
    rw [le_div_iff₀ (sq_pos_of_pos hnpos)]
    rw [show ((8/3 : ℝ)-(4/3 : ℝ)/(n : ℝ))*(n : ℝ)^2 =
        (8*(n : ℝ)^2-4*(n : ℝ))/3 by
      field_simp [hnpos.ne'] <;> ring]
    linarith only [hA]
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hA : 3*(A2 n : ℝ) ≤ 8*(n : ℝ)^2 := by
      exact_mod_cast (A2_upper_quadratic n hn)
    rw [div_le_iff₀ (sq_pos_of_pos hnpos)]
    linarith only [hA]

/-- The literal rational lower bound in Qtilde_GV_two. -/
def twoAdicLowerBound (n : ℕ) : ℚ :=
  (A2 n : ℚ)-4*(n : ℚ)*(Nat.log 2 (7*n-2) : ℚ)

lemma twoAdicLowerBound_tendsto :
    Tendsto (fun n : ℕ => (twoAdicLowerBound n : ℝ)/(n : ℝ)^2)
      atTop (𝓝 (8/3 : ℝ)) := by
  simpa [twoAdicLowerBound, sub_div] using!
    A2_ratio_tendsto.sub (natLog_error_square_tendsto_zero 2)

end
end Li2.PrimeSums

end
