module
public import Li2Unified.Modular.Base.DecayPNTInterface
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

set_option backward.privateInPublic true

@[expose] public section

open Finset Filter Topology Asymptotics
namespace Li2.PrimeSums
noncomputable section
set_option maxHeartbeats 400000

def cPrime (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

def logSum (a b : ℝ) : ℝ := ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, cPrime k

lemma theta_eq_sum_cPrime (t : ℝ) :
    Chebyshev.theta t = ∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, cPrime k := by
  rw [Chebyshev.theta, Finset.sum_filter]
  rfl

#check theta_eq_sum_cPrime

lemma logSum_eq_theta_sub {a b : ℝ} (hab : a ≤ b) :
    logSum a b = Chebyshev.theta b-Chebyshev.theta a := by
  have hsplit :
      (∑ k ∈ Finset.Ioc 0 ⌊a⌋₊, cPrime k)+
        (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, cPrime k) =
      ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, cPrime k :=
    Finset.sum_Ioc_consecutive cPrime (Nat.zero_le _) (Nat.floor_le_floor hab)
  rw [← theta_eq_sum_cPrime, ← theta_eq_sum_cPrime] at hsplit
  unfold logSum
  linarith

#check logSum_eq_theta_sub

lemma theta_ratio_tendsto :
    Tendsto (fun x : ℝ => Chebyshev.theta x/x) atTop (𝓝 1) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp Li2.theta_isEquivalent_id
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact ne_of_gt hx

#check theta_ratio_tendsto

lemma theta_scaled_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Chebyshev.theta (c*x)/x) atTop (𝓝 c) := by
  have hs : Tendsto (fun x : ℝ => c*x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).2 tendsto_id
  have h := (theta_ratio_tendsto.comp hs).const_mul c
  have he : (fun x : ℝ => c*(Chebyshev.theta (c*x)/(c*x))) =ᶠ[atTop]
      (fun x : ℝ => Chebyshev.theta (c*x)/x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hc.ne', hx.ne']
  simpa only [mul_one] using (tendsto_congr' he).mp h

#check theta_scaled_tendsto

lemma theta_interval_tendsto {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun x : ℝ => (Chebyshev.theta (b*x)-Chebyshev.theta (a*x))/x)
      atTop (𝓝 (b-a)) := by
  simpa only [← sub_div] using (theta_scaled_tendsto hb).sub (theta_scaled_tendsto ha)

#check theta_interval_tendsto

lemma logSum_scaled_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ => logSum (a*x) (b*x)/x) atTop (𝓝 (b-a)) := by
  have h := theta_interval_tendsto ha (ha.trans_le hab)
  apply (tendsto_congr' ?_).mp h
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [logSum_eq_theta_sub (mul_le_mul_of_nonneg_right hab hx)]

#check logSum_scaled_tendsto

lemma theta_interval_nat_tendsto {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ =>
      (Chebyshev.theta (b*(n : ℝ))-Chebyshev.theta (a*(n : ℝ)))/(n : ℝ))
      atTop (𝓝 (b-a)) :=
  (theta_interval_tendsto ha hb).comp tendsto_natCast_atTop_atTop

#check theta_interval_nat_tendsto

lemma logSum_scaled_nat_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ => logSum (a*(n : ℝ)) (b*(n : ℝ))/(n : ℝ))
      atTop (𝓝 (b-a)) :=
  (logSum_scaled_tendsto ha hab).comp tendsto_natCast_atTop_atTop

end
end Li2.PrimeSums

end
