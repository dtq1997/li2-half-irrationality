module
public import Mathlib.Data.Int.CardIntervalMod
public import Li2Unified.Modular.Positive.Packed.P002
public import Li2Unified.Modular.Base.Valuation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option backward.privateInPublic true

@[expose] public section

section
/-! Exact copy of the frozen residue-count core, isolated to avoid an import cycle.
The original Stage0 declarations remain in place; their definitions are definitionally equal. -/
open Polynomial MeasureTheory
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite.CountsCore
noncomputable section

def residueCount (p K : ℕ) (c : Fin p) : ℕ :=
  ((Finset.Icc 1 K).filter fun j => j % p = c.val).card

def multiplicity (n p : ℕ) (c : Fin p) : ℕ :=
  if c.val = 0 then (3*n)/p - n/p
  else residueCount p (4*n) c - 2*residueCount p n c

def delta (n p : ℕ) : ℕ := (4*n)/p - n/p - (3*n)/p

private theorem residueCount_zero_bridge (p n : ℕ) (hp : 0 < p) :
    residueCount p n ⟨0, hp⟩ = n / p := by
  rw [residueCount]
  convert Nat.Ioc_filter_dvd_card_eq_div n p using 1
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, hn⟩, hmod⟩
    exact ⟨⟨by omega, hn⟩, Nat.dvd_iff_mod_eq_zero.mpr hmod⟩
  · rintro ⟨⟨h0, hn⟩, hdiv⟩
    exact ⟨⟨by omega, hn⟩, Nat.dvd_iff_mod_eq_zero.mp hdiv⟩

private theorem residueCount_nonzero_bridge (p n : ℕ) (c : Fin p)
    (hc : c.val ≠ 0) (hp : 0 < p) :
    residueCount p n c =
      (n + 1) / p + if c.val < (n + 1) % p then 1 else 0 := by
  have hset : (Finset.Icc 1 n).filter (fun k => k % p = c.val) =
      (Finset.range (n + 1)).filter (fun k => k ≡ c.val [MOD p]) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, hn⟩, hmod⟩
      exact ⟨by omega, by simpa [Nat.ModEq, Nat.mod_eq_of_lt c.isLt] using hmod⟩
    · rintro ⟨hn, hmod⟩
      have hk0 : k ≠ 0 := by
        intro hk
        subst k
        simp [Nat.ModEq, Nat.mod_eq_of_lt c.isLt] at hmod
        exact hc hmod.symm
      exact ⟨⟨by omega, by omega⟩,
        by simpa [Nat.ModEq, Nat.mod_eq_of_lt c.isLt] using hmod⟩
  rw [residueCount, hset, ← Nat.count_eq_card_filter_range]
  simpa [Nat.mod_eq_of_lt c.isLt] using Nat.count_modEq_card (n + 1) (r := p) hp c.val

private theorem residueCount_nonzero_le_bridge (p n : ℕ) (c : Fin p)
    (hc : c.val ≠ 0) (hp : 0 < p) :
    residueCount p n c ≤ n / p + 1 := by
  rw [residueCount_nonzero_bridge p n c hc hp, Nat.succ_div]
  by_cases h : p ∣ n + 1
  · have hm : (n + 1) % p = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    simp [h, hm]
  · simp only [h, ↓reduceIte, Nat.add_zero]
    split_ifs <;> omega

private theorem residueCount_nonzero_ge_bridge (p n : ℕ) (c : Fin p)
    (hc : c.val ≠ 0) (hp : 0 < p) :
    n / p ≤ residueCount p n c := by
  rw [residueCount_nonzero_bridge p n c hc hp]
  have hdiv : n / p ≤ (n + 1) / p := Nat.div_le_div_right (by omega)
  split_ifs <;> omega

private theorem residueCount_twice_le_bridge (p n : ℕ) (c : Fin p)
    (hc : c.val ≠ 0) (hp : 0 < p) (hpn : p ≤ n) :
    2 * residueCount p n c ≤ residueCount p (4 * n) c := by
  have hq : 1 ≤ n / p := (Nat.one_le_div_iff hp).mpr hpn
  have h4q : 4 * (n / p) ≤ (4 * n) / p := by
    apply (Nat.le_div_iff_mul_le hp).2
    nlinarith [Nat.div_mul_le_self n p]
  have hu := residueCount_nonzero_le_bridge p n c hc hp
  have hl := residueCount_nonzero_ge_bridge p (4 * n) c hc hp
  omega

private theorem residueCount_sum_bridge (p n : ℕ) (hp : 0 < p) :
    (∑ c : Fin p, residueCount p n c) = n := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.Icc 1 n) (Finset.univ : Finset (Fin p))
    (fun k => (⟨k % p, Nat.mod_lt k hp⟩ : Fin p))
  simpa [residueCount, Fin.ext_iff] using h

theorem exact_counts (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    delta n p ≤ 1 ∧ (∑ c : Fin p, multiplicity n p c) + delta n p = 2*n := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  let z : Fin p := ⟨0, hp0⟩
  have hq3 : n / p ≤ (3 * n) / p :=
    Nat.div_le_div_right (by omega)
  have hq4 : n / p + (3 * n) / p ≤ (4 * n) / p := by
    simpa [show n + 3 * n = 4 * n by omega] using
      (Nat.div_add_div_le_add_div (x := n) (y := 3 * n) (z := p))
  have h4q : 4 * (n / p) ≤ (4 * n) / p := by
    apply (Nat.le_div_iff_mul_le hp0).2
    nlinarith [Nat.div_mul_le_self n p]
  have hnonneg (c : Fin p) :
      2 * residueCount p n c ≤ residueCount p (4 * n) c := by
    by_cases hc : c.val = 0
    · have hcz : c = z := Fin.ext hc
      subst c
      rw [residueCount_zero_bridge p n hp0, residueCount_zero_bridge p (4 * n) hp0]
      omega
    · exact residueCount_twice_le_bridge p n c hc hp0 hpn
  have hzero : multiplicity n p z + delta n p =
      residueCount p (4 * n) z - 2 * residueCount p n z := by
    rw [show multiplicity n p z = (3 * n) / p - n / p by
      simp [Li2Unified.Proofs.Hermite.CountsCore.multiplicity, z],
      residueCount_zero_bridge p (4 * n) hp0, residueCount_zero_bridge p n hp0]
    unfold delta
    omega
  have hsum : (∑ c : Fin p, multiplicity n p c) + delta n p =
      ∑ c : Fin p, (residueCount p (4 * n) c - 2 * residueCount p n c) := by
    calc
      _ = ∑ c : Fin p,
          (multiplicity n p c + if c = z then delta n p else 0) := by
            rw [Finset.sum_add_distrib]
            simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c _
        by_cases hcz : c = z
        · subst c
          simpa using hzero
        · have hc : c.val ≠ 0 := by
            intro hc
            exact hcz (Fin.ext hc)
          simp [hcz, Li2Unified.Proofs.Hermite.CountsCore.multiplicity, hc]
  have htsub : (∑ c : Fin p,
      (residueCount p (4 * n) c - 2 * residueCount p n c)) =
      (∑ c : Fin p, residueCount p (4 * n) c) -
        (∑ c : Fin p, 2 * residueCount p n c) := by
    exact Finset.sum_tsub_distrib Finset.univ (by intro c _; exact hnonneg c)
  constructor
  · unfold delta
    rw [show 4 * n = n + 3 * n by omega, Nat.add_div hp0]
    split_ifs <;> omega
  · rw [hsum, htsub]
    rw [residueCount_sum_bridge p (4 * n) hp0, ← Finset.mul_sum,
      residueCount_sum_bridge p n hp0]
    omega

end
end Li2Unified.Proofs.Hermite.CountsCore
#print axioms Li2Unified.Proofs.Hermite.CountsCore.exact_counts

end


end
