module
public import Li2Unified.Modular.Base.Criterion
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Prime.Infinite

set_option backward.privateInPublic true

@[expose] public section

/-! A nonzero constant reduction excludes every rational root whose denominator
is prime to p. This is the generic last step, not the prime-edge calculation. -/
open Polynomial Filter Topology
namespace Li2

lemma pow_mul_aeval_div_eq_cast {K : Type*} [Field K]
    (P : ℤ[X]) {d : ℕ} (hd : P.natDegree ≤ d) (a b : ℤ)
    (hb : (b : K) ≠ 0) :
    (b : K)^d * aeval ((a : K) / b) P =
      ((∑ k ∈ Finset.range (d+1), P.coeff k * a^k * b^(d-k) : ℤ) : K) := by
  have hlt : (P.map (algebraMap ℤ K)).natDegree < d+1 :=
    lt_of_le_of_lt natDegree_map_le (by omega)
  rw [aeval_def, eval₂_eq_eval_map, eval_eq_sum_range' hlt, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hpow : (b : K)^d = (b : K)^(d-k) * (b : K)^k := by
    rw [← pow_add]; congr 1; omega
  rw [coeff_map, hpow, div_pow]
  simp only [algebraMap_int_eq, eq_intCast]
  field_simp

theorem rational_nonzero_of_constant_reduction (P : ℤ[X]) (p : ℕ) [Fact p.Prime]
    (c : ZMod p) (hc : c ≠ 0)
    (hred : P.map (Int.castRingHom (ZMod p)) = C c)
    (q : ℚ) (hb : (q.den : ZMod p) ≠ 0) :
    aeval (q : ℝ) P ≠ 0 := by
  intro hz
  let d := P.natDegree
  let m : ℤ := ∑ k ∈ Finset.range (d+1), P.coeff k * q.num^k * (q.den : ℤ)^(d-k)
  have hmR := pow_mul_aeval_div_eq_intCast P (d := d) le_rfl q.num (q.den : ℤ)
    (by exact_mod_cast q.den_pos.ne')
  have heval : aeval ((q.num : ℝ) / (q.den : ℤ)) P = 0 := by
    simpa [Rat.cast_def, Int.cast_natCast] using hz
  have hm0 : m = 0 := by
    rw [heval, mul_zero] at hmR
    have : (m : ℝ) = 0 := hmR.symm
    exact_mod_cast this
  have hmZ := pow_mul_aeval_div_eq_cast (K := ZMod p) P (d := d) le_rfl
    q.num (q.den : ℤ) (by simpa using hb)
  have hz_eval : aeval ((q.num : ZMod p)/((q.den : ℤ) : ZMod p)) P = c := by
    rw [aeval_def, eval₂_eq_eval_map]
    change (P.map (Int.castRingHom (ZMod p))).eval _ = c
    rw [hred, eval_C]
  have hprod : (q.den : ZMod p)^d * c = 0 := by
    change ((q.den : ℤ) : ZMod p)^d * aeval ((q.num : ZMod p)/((q.den : ℤ) : ZMod p)) P = (m : ZMod p) at hmZ
    rw [hz_eval, hm0, Int.cast_zero, Int.cast_natCast] at hmZ
    exact hmZ
  exact mul_ne_zero (pow_ne_zero _ hb) hc hprod

/-- A prime p greater than the denominator and all exceptional primes is enough. -/
theorem frequently_rational_nonzero_of_prime_reduction (P : ℕ → ℤ[X])
    (hred : ∀ p : ℕ, p.Prime → 73 < p →
      ∃ c : ZMod p, c ≠ 0 ∧ (P (p-1)).map (Int.castRingHom (ZMod p)) = C c)
    (q : ℚ) : ∃ᶠ n in atTop, aeval (q : ℝ) (P n) ≠ 0 := by
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨p, hpbig, hp⟩ := Nat.exists_infinite_primes (max (N+2) (max 74 (q.den+1)))
  have h73 : 73 < p := by omega
  have hden : q.den < p := by omega
  have hN : N ≤ p-1 := by omega
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc, hcp⟩ := hred p hp h73
  refine ⟨p-1, hN, rational_nonzero_of_constant_reduction (P (p-1)) p c hc hcp q ?_⟩
  intro hz
  have hdvd : p ∣ q.den := (ZMod.natCast_eq_zero_iff _ _).mp hz
  exact (not_le.mpr hden) (Nat.le_of_dvd q.den_pos hdvd)

end Li2

end
