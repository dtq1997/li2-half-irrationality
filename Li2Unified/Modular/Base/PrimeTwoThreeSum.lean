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
    simpa only [zero_div] using hlog.div_const (Real.log (b : ℝ))
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
          simpa only [Real.logb, Nat.cast_mul, Nat.cast_ofNat] using (Real.natLog_le_logb (7*n) b)
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
    simpa only [mul_zero] using (natLog_seven_sub_two_div_tendsto_zero b).const_mul (4 : ℝ)
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
    simpa only [sub_zero] using
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

lemma S3_ratio_tendsto :
    Tendsto (fun n : ℕ => (S3 n : ℝ)/(n : ℝ)^2)
      atTop (𝓝 (9/4 : ℝ)) := by
  have hunit : Tendsto (fun n : ℕ => (1 : ℝ)/(n : ℝ)^2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa [div_pow] using (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).pow 2
  have hrem : Tendsto (fun n : ℕ => ((n%2 : ℕ) : ℝ)/(n : ℝ)^2)
      atTop (𝓝 (0 : ℝ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hunit ?_ ?_
    · intro n
      positivity
    · intro n
      have hm : ((n%2 : ℕ) : ℝ) ≤ 1 := by
        exact_mod_cast (show n%2 ≤ 1 by omega)
      exact div_le_div_of_nonneg_right hm (sq_nonneg (n : ℝ))
  have h : Tendsto (fun n : ℕ => (9/4 : ℝ)-(((n%2 : ℕ) : ℝ)/(n : ℝ)^2)/4)
      atTop (𝓝 (9/4 : ℝ)) := by
    simpa only [zero_div, sub_zero] using
      (tendsto_const_nhds (x := (9/4 : ℝ))).sub (hrem.div_const (4 : ℝ))
  apply (tendsto_congr' ?_).mp h
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hclosed : 4*(S3 n : ℝ)+((n%2 : ℕ) : ℝ) = 9*(n : ℝ)^2 := by
    exact_mod_cast (Li2.S3_closed n)
  field_simp [hn0] <;> nlinarith only [hclosed]

/-- The literal rational lower bound in Qtilde_GV_two. -/
def twoAdicLowerBound (n : ℕ) : ℚ :=
  (A2 n : ℚ)-4*(n : ℚ)*(Nat.log 2 (7*n-2) : ℚ)

/-- The literal rational lower bound in Qtilde_GV_three. -/
def threeAdicLowerBound (n : ℕ) : ℚ :=
  -(S3 n : ℚ)-4*(n : ℚ)*(Nat.log 3 (7*n-2) : ℚ)

lemma Qtilde_GV_twoAdicLowerBound {n : ℕ} (hn : 1 ≤ n) :
    GV 2 (Qtilde n) (twoAdicLowerBound n) := Qtilde_GV_two hn

lemma Qtilde_GV_threeAdicLowerBound {n : ℕ} (hn : 1 ≤ n) :
    GV 3 (Qtilde n) (threeAdicLowerBound n) := Qtilde_GV_three hn

lemma twoAdicLowerBound_tendsto :
    Tendsto (fun n : ℕ => (twoAdicLowerBound n : ℝ)/(n : ℝ)^2)
      atTop (𝓝 (8/3 : ℝ)) := by
  simpa [twoAdicLowerBound, sub_div] using
    A2_ratio_tendsto.sub (natLog_error_square_tendsto_zero 2)

lemma threeAdicLowerBound_tendsto :
    Tendsto (fun n : ℕ => (threeAdicLowerBound n : ℝ)/(n : ℝ)^2)
      atTop (𝓝 (-(9/4 : ℝ))) := by
  simpa [threeAdicLowerBound, sub_div, neg_div] using
    S3_ratio_tendsto.neg.sub (natLog_error_square_tendsto_zero 3)

def twoThreeWeightedBound (n : ℕ) : ℝ :=
  (twoAdicLowerBound n : ℝ)*Real.log 2 +
    (threeAdicLowerBound n : ℝ)*Real.log 3

theorem twoThreeWeightedBound_tendsto :
    Tendsto (fun n : ℕ => twoThreeWeightedBound n/(n : ℝ)^2) atTop
      (𝓝 ((8/3 : ℝ)*Real.log 2-(9/4 : ℝ)*Real.log 3)) := by
  have h := (twoAdicLowerBound_tendsto.mul_const (Real.log 2)).add
    (threeAdicLowerBound_tendsto.mul_const (Real.log 3))
  have hmass : (8/3 : ℝ)*Real.log 2+(-(9/4 : ℝ))*Real.log 3 =
      (8/3 : ℝ)*Real.log 2-(9/4 : ℝ)*Real.log 3 := by ring
  rw [hmass] at h
  apply (tendsto_congr' ?_).mp h
  exact Filter.Eventually.of_forall (fun n => by
    dsimp [twoThreeWeightedBound]
    ring)

end
end Li2.PrimeSums

end
