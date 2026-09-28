module
public import Li2Unified.Modular.Base.PrimePowerTail
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Ring

set_option backward.privateInPublic true

@[expose] public section

open Finset Filter Topology
namespace Li2.PrimeSums
noncomputable section

def smallFallbackPrimes (n : ℕ) : Finset ℕ :=
  (Finset.Ioc 4 ⌊(1/4 : ℝ)*(n : ℝ)⌋₊).filter Nat.Prime

lemma mem_smallFallbackPrimes {n p : ℕ} :
    p ∈ smallFallbackPrimes n ↔
      p.Prime ∧ 4 < p ∧ (p : ℝ) ≤ (1/4 : ℝ)*(n : ℝ) := by
  simp only [smallFallbackPrimes, Finset.mem_filter, Finset.mem_Ioc]
  rw [Nat.le_floor_iff (show 0 ≤ (1/4 : ℝ)*(n : ℝ) by positivity)]
  constructor
  · rintro ⟨⟨hp4, hpn⟩, hp⟩
    exact ⟨hp, hp4, hpn⟩
  · rintro ⟨hp, hp4, hpn⟩
    exact ⟨⟨hp4, hpn⟩, hp⟩

lemma smallFallback_natLog_one_le {n p : ℕ}
    (hp : p ∈ smallFallbackPrimes n) : 1 ≤ Nat.log p (7*n-2) := by
  obtain ⟨hpp, hp4, hpR⟩ := mem_smallFallbackPrimes.mp hp
  have hp4R : (4 : ℝ) < (p : ℝ) := by exact_mod_cast hp4
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith only [hp4R, hpR]
  have hn : 0 < n := by exact_mod_cast hnR
  have hpnR : (p : ℝ) ≤ (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith only [hpR, hn0]
  have hpn : p ≤ n := by exact_mod_cast hpnR
  have hpD : p ≤ 7*n-2 := by omega
  have hpos := Nat.log_pos hpp.one_lt hpD
  omega

lemma smallFallback_first_sum_eq (n : ℕ) :
    (∑ p ∈ smallFallbackPrimes n, Real.log (p : ℝ)) =
      logSum 4 ((1/4 : ℝ)*(n : ℝ)) := by
  simp [smallFallbackPrimes, logSum, cPrime, Finset.sum_filter]

def smallFallbackLogSum (n : ℕ) : ℝ :=
  ∑ p ∈ smallFallbackPrimes n,
    ((Nat.log p (7*n-2) : ℝ)*Real.log (p : ℝ))

lemma smallFallbackLogSum_eq (n : ℕ) :
    smallFallbackLogSum n = logSum 4 ((1/4 : ℝ)*(n : ℝ)) +
      primePowerExcess (7*n-2) (smallFallbackPrimes n) := by
  rw [← smallFallback_first_sum_eq n]
  unfold smallFallbackLogSum primePowerExcess
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hL := smallFallback_natLog_one_le hp
  simp only [Nat.cast_sub hL, Nat.cast_one]
  ring

lemma smallFallback_first_tendsto :
    Tendsto (fun n : ℕ => logSum 4 ((1/4 : ℝ)*(n : ℝ))/(n : ℝ))
      atTop (𝓝 (1/4 : ℝ)) := by
  have htheta : Tendsto (fun n : ℕ =>
      Chebyshev.theta ((1/4 : ℝ)*(n : ℝ))/(n : ℝ))
      atTop (𝓝 (1/4 : ℝ)) :=
    (theta_scaled_tendsto (c := (1/4 : ℝ)) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have h : Tendsto (fun n : ℕ =>
      (Chebyshev.theta ((1/4 : ℝ)*(n : ℝ))-Chebyshev.theta 4)/(n : ℝ))
      atTop (𝓝 (1/4 : ℝ)) := by
    simpa only [sub_zero, ← sub_div] using htheta.sub
      (tendsto_const_div_atTop_nhds_zero_nat (Chebyshev.theta 4))
  apply (tendsto_congr' ?_).mp h
  filter_upwards [eventually_ge_atTop (16 : ℕ)] with n hn
  have hnR : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [logSum_eq_theta_sub (by linarith : (4 : ℝ) ≤ (1/4 : ℝ)*(n : ℝ))]

lemma smallFallbackLogSum_tendsto :
    Tendsto (fun n : ℕ => smallFallbackLogSum n/(n : ℝ))
      atTop (𝓝 (1/4 : ℝ)) := by
  have htail := primePowerExcess_seven_sub_two_tendsto_zero smallFallbackPrimes
    (fun n p hp => (mem_smallFallbackPrimes.mp hp).1)
  have h : Tendsto (fun n : ℕ =>
      logSum 4 ((1/4 : ℝ)*(n : ℝ))/(n : ℝ) +
        primePowerExcess (7*n-2) (smallFallbackPrimes n)/(n : ℝ))
      atTop (𝓝 (1/4 : ℝ)) := by
    simpa only [add_zero] using smallFallback_first_tendsto.add htail
  apply (tendsto_congr' ?_).mp h
  exact Filter.Eventually.of_forall (fun n => by
    dsimp only
    rw [smallFallbackLogSum_eq, add_div])

def smallFallbackWeightedBound (n : ℕ) : ℝ :=
  ∑ p ∈ smallFallbackPrimes n,
    (((-4*(n : ℚ)*(Nat.log p (7*n-2) : ℚ) : ℚ) : ℝ)*Real.log (p : ℝ))

lemma smallFallbackWeightedBound_eq (n : ℕ) :
    smallFallbackWeightedBound n = -4*(n : ℝ)*smallFallbackLogSum n := by
  unfold smallFallbackWeightedBound smallFallbackLogSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  push_cast
  ring

theorem smallFallbackWeightedBound_tendsto :
    Tendsto (fun n : ℕ => smallFallbackWeightedBound n/(n : ℝ)^2)
      atTop (𝓝 (-1 : ℝ)) := by
  have h : Tendsto (fun n : ℕ => -4*(smallFallbackLogSum n/(n : ℝ)))
      atTop (𝓝 (-1 : ℝ)) := by
    simpa using smallFallbackLogSum_tendsto.const_mul (-4 : ℝ)
  apply (tendsto_congr' ?_).mp h
  filter_upwards [eventually_ge_atTop (16 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [smallFallbackWeightedBound_eq]
  field_simp [hn0] <;> ring

end
end Li2.PrimeSums

end
