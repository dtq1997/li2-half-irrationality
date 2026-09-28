module
public import Li2Unified.Modular.Base.PrimeSmallTableSum

set_option backward.privateInPublic true

@[expose] public section

section
open Finset Filter Topology

namespace Li2Unified.Proofs.Arithmetic
noncomputable section

def smallTailPrimes (δ : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Ioc 4 ⌊δ*(n:ℝ)⌋₊).filter Nat.Prime

theorem mem_smallTailPrimes {δ : ℝ} {n p : ℕ} (hδ : 0 ≤ δ) :
    p ∈ smallTailPrimes δ n ↔
      p.Prime ∧ 4 < p ∧ (p:ℝ) ≤ δ*(n:ℝ) := by
  simp only [smallTailPrimes, Finset.mem_filter, Finset.mem_Ioc]
  rw [Nat.le_floor_iff (mul_nonneg hδ (Nat.cast_nonneg n))]
  constructor
  · rintro ⟨⟨hp4, hpn⟩, hpr⟩
    exact ⟨hpr, hp4, hpn⟩
  · rintro ⟨hpr, hp4, hpn⟩
    exact ⟨⟨hp4, hpn⟩, hpr⟩

theorem smallTail_natLog_one_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {n p : ℕ} (hp : p ∈ smallTailPrimes δ n) :
    1 ≤ Nat.log p (7*n-2) := by
  obtain ⟨hpr, hp4, hpR⟩ := (mem_smallTailPrimes hδ0).mp hp
  have hpnR : (p:ℝ) ≤ (n:ℝ) := by
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    nlinarith only [hpR, hn0, hδ1]
  have hpn : p ≤ n := by exact_mod_cast hpnR
  have hpD : p ≤ 7*n-2 := by omega
  exact Nat.log_pos hpr.one_lt hpD

def smallTailLogSum (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ smallTailPrimes δ n,
    (Nat.log p (7*n-2):ℝ) * Real.log (p:ℝ)

theorem smallTailLogSum_eq (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (n : ℕ) :
    smallTailLogSum δ n =
      Li2.PrimeSums.logSum 4 (δ*(n:ℝ)) +
        Li2.PrimeSums.primePowerExcess (7*n-2) (smallTailPrimes δ n) := by
  have hfirst : (∑ p ∈ smallTailPrimes δ n, Real.log (p:ℝ)) =
      Li2.PrimeSums.logSum 4 (δ*(n:ℝ)) := by
    simp [smallTailPrimes, Li2.PrimeSums.logSum, Li2.PrimeSums.cPrime,
      Finset.sum_filter]
  rw [← hfirst]
  unfold smallTailLogSum Li2.PrimeSums.primePowerExcess
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hL := smallTail_natLog_one_le hδ0 hδ1 hp
  simp only [Nat.cast_sub hL, Nat.cast_one]
  ring

theorem smallTail_first_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => Li2.PrimeSums.logSum 4 (δ*(n:ℝ))/(n:ℝ))
      atTop (𝓝 δ) := by
  have htheta : Tendsto (fun n : ℕ =>
      Chebyshev.theta (δ*(n:ℝ))/(n:ℝ)) atTop (𝓝 δ) :=
    (Li2.PrimeSums.theta_scaled_tendsto hδ).comp
      tendsto_natCast_atTop_atTop
  have h : Tendsto (fun n : ℕ =>
      (Chebyshev.theta (δ*(n:ℝ))-Chebyshev.theta 4)/(n:ℝ))
      atTop (𝓝 δ) := by
    simpa only [sub_zero, ← sub_div] using! htheta.sub
      (tendsto_const_div_atTop_nhds_zero_nat (Chebyshev.theta 4))
  apply (tendsto_congr' ?_).mp h
  obtain ⟨N, hN⟩ := exists_nat_gt (4/δ)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnR : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have h4 : (4:ℝ) ≤ δ*(n:ℝ) := by
    have hh : (4:ℝ) < δ*(N:ℝ) := by
      simpa only [mul_comm] using! (div_lt_iff₀ hδ).mp hN
    nlinarith only [hh, hnR, hδ]
  rw [Li2.PrimeSums.logSum_eq_theta_sub h4]

theorem smallTailLogSum_tendsto (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun n : ℕ => smallTailLogSum δ n/(n:ℝ)) atTop (𝓝 δ) := by
  have htail := Li2.PrimeSums.primePowerExcess_seven_sub_two_tendsto_zero
    (smallTailPrimes δ) (fun n p hp => ((mem_smallTailPrimes hδ0.le).mp hp).1)
  have h : Tendsto (fun n : ℕ =>
      Li2.PrimeSums.logSum 4 (δ*(n:ℝ))/(n:ℝ) +
      Li2.PrimeSums.primePowerExcess (7*n-2) (smallTailPrimes δ n)/(n:ℝ))
      atTop (𝓝 δ) := by
    simpa only [add_zero] using! (smallTail_first_tendsto δ hδ0).add htail
  apply (tendsto_congr' ?_).mp h
  exact Filter.Eventually.of_forall (fun n => by
    dsimp only
    rw [smallTailLogSum_eq δ hδ0.le hδ1, add_div])

def smallTailFallbackBound (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ smallTailPrimes δ n,
    (-4*(n:ℝ)*(Nat.log p (7*n-2):ℝ)) * Real.log (p:ℝ)

theorem smallTailFallbackBound_tendsto (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun n : ℕ => smallTailFallbackBound δ n/(n:ℝ)^2)
      atTop (𝓝 (-4*δ)) := by
  have heq (n : ℕ) : smallTailFallbackBound δ n =
      -4*(n:ℝ)*smallTailLogSum δ n := by
    unfold smallTailFallbackBound smallTailLogSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have h : Tendsto (fun n : ℕ => -4*(smallTailLogSum δ n/(n:ℝ)))
      atTop (𝓝 (-4*δ)) := by
    simpa using! (smallTailLogSum_tendsto δ hδ0 hδ1).const_mul (-4:ℝ)
  apply (tendsto_congr' ?_).mp h
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [heq]
  field_simp [hn0]

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.smallTailLogSum_tendsto
#print axioms Li2Unified.Proofs.Arithmetic.smallTailFallbackBound_tendsto

end


end
