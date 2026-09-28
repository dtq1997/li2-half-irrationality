module
public import Li2Unified.Modular.Positive.Packed.P040
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public import Li2Unified.Modular.Positive.Packed.P039
public import Li2Unified.Modular.Positive.Packed.P042

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Finset
open scoped BigOperators

/-- Exact disjoint partition of all prime contributions up to `4n` into
the two exceptional primes and three intervals. -/
theorem prime_range_three_interval_partition (f : ℕ → ℝ)
    (n c : ℕ) (hc4 : 4 ≤ c) (hcn : c ≤ n) :
    (∑ p ∈ (Finset.range (4*n+1)).filter Nat.Prime, f p) =
      f 2 + f 3 +
      (∑ p ∈ Finset.Ioc 4 c, if p.Prime then f p else 0) +
      (∑ p ∈ Finset.Ioc c n, if p.Prime then f p else 0) +
      (∑ p ∈ Finset.Ioc n (4*n), if p.Prime then f p else 0) := by
  let g : ℕ → ℝ := fun p => if p.Prime then f p else 0
  have h0 : (∑ p ∈ Finset.range 5, g p) = f 2 + f 3 := by
    simp [g, Finset.sum_range_succ,
      show ¬ (0:ℕ).Prime by decide, show ¬ (1:ℕ).Prime by decide,
      show (2:ℕ).Prime by decide, show (3:ℕ).Prime by decide,
      show ¬ (4:ℕ).Prime by decide]
  have hIco (a b : ℕ) : Finset.Ico (a+1) (b+1) = Finset.Ioc a b := by
    ext p
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  have h5 : 5 ≤ 4*n+1 := by omega
  rw [Finset.sum_filter]
  change (∑ p ∈ Finset.range (4*n+1), g p) = _
  rw [← Finset.sum_range_add_sum_Ico g h5]
  have hsplit1 :
      (∑ p ∈ Finset.Ico 5 (4*n+1), g p) =
      (∑ p ∈ Finset.Ico 5 (c+1), g p) +
      (∑ p ∈ Finset.Ico (c+1) (4*n+1), g p) := by
    symm
    exact Finset.sum_Ico_consecutive (f := g) (by omega : 5 ≤ c+1)
      (by omega : c+1 ≤ 4*n+1)
  rw [hsplit1]
  have hsplit2 :
      (∑ p ∈ Finset.Ico (c+1) (4*n+1), g p) =
      (∑ p ∈ Finset.Ico (c+1) (n+1), g p) +
      (∑ p ∈ Finset.Ico (n+1) (4*n+1), g p) := by
    symm
    exact Finset.sum_Ico_consecutive (f := g) (by omega : c+1 ≤ n+1)
      (by omega : n+1 ≤ 4*n+1)
  rw [hsplit2, h0, hIco 4 c, hIco c n, hIco n (4*n)]
  simp only [g]
  ring

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.prime_range_three_interval_partition

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Finset
open scoped BigOperators

/-- Exact medium-prime partition at any finite cutoff. -/
theorem medium_prime_two_interval_partition (f : ℕ → ℝ)
    (n c : ℕ) (hc4 : 4 ≤ c) (hcn : c ≤ n) :
    (∑ p ∈ (Finset.range (n+1)).filter (fun p => p.Prime ∧ 5 ≤ p), f p) =
      (∑ p ∈ Finset.Ioc 4 c, if p.Prime then f p else 0) +
      (∑ p ∈ Finset.Ioc c n, if p.Prime then f p else 0) := by
  have hset :
      (Finset.range (n+1)).filter (fun p => p.Prime ∧ 5 ≤ p) =
        (Finset.Ioc 4 n).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨hpn, hpr, hp5⟩
      exact ⟨⟨by omega, by omega⟩, hpr⟩
    · rintro ⟨⟨hp4, hpn⟩, hpr⟩
      exact ⟨by omega, hpr, by omega⟩
  let g : ℕ → ℝ := fun p => if p.Prime then f p else 0
  have hIco (a b : ℕ) : Finset.Ico (a+1) (b+1) = Finset.Ioc a b := by
    ext p
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rw [hset, Finset.sum_filter]
  change (∑ p ∈ Finset.Ioc 4 n, g p) = _
  rw [← hIco 4 n]
  have hsplit :
      (∑ p ∈ Finset.Ico 5 (n+1), g p) =
      (∑ p ∈ Finset.Ico 5 (c+1), g p) +
      (∑ p ∈ Finset.Ico (c+1) (n+1), g p) := by
    symm
    exact Finset.sum_Ico_consecutive (f := g)
      (by omega : 5 ≤ c+1) (by omega : c+1 ≤ n+1)
  rw [hsplit, hIco 4 c, hIco c n]

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.medium_prime_two_interval_partition

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section

/-- The cutoff is chosen after `ε`; each proof uses only finitely many
reciprocal cells. -/
theorem exists_finite_cutoff (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧
      (0:ℝ) < 1/((N+1:ℕ):ℝ) ∧
      1/((N+1:ℕ):ℝ) ≤ 1 ∧
      4/((N+1:ℕ):ℝ) < ε/2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (8/ε+2)
  have hN2R : (2:ℝ) < (N:ℝ) := by
    have hnonneg : (0:ℝ) ≤ 8/ε := by positivity
    linarith
  have hN2 : 2 ≤ N := by exact_mod_cast hN2R.le
  have hden : (0:ℝ) < ((N+1:ℕ):ℝ) := by positivity
  have hN8 : 8/ε < (N:ℝ) := by linarith
  have h8 : 8 < ε*((N+1:ℕ):ℝ) := by
    have := (div_lt_iff₀ hε).mp hN8
    push_cast
    nlinarith
  refine ⟨N, hN2, by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ hden).mpr
    norm_num
  · apply (div_lt_iff₀ hden).mpr
    nlinarith

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.exists_finite_cutoff

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf
open Li2Unified.Stage0.HermitePreparation
open Filter Finset
open scoped BigOperators

/-- The full `ε` medium-prime rate follows by choosing one finite reciprocal
cutoff after `ε`. Only the actual Gram estimate remains a premise. -/
theorem posHalf_medium_eventually_of_gram (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (∀ p ∈ (Finset.range (n+1)).filter (fun p => p.Prime ∧ 5 ≤ p),
        ∀ hp : p.Prime,
          letI : Fact p.Prime := ⟨hp⟩
          Li2.GV p (binomGram lambda n).det (normalizedDetLower n p)) →
      Instances.PosHalf.Qtilde n ≠ 0 →
        ((-523/840:ℝ)-ε)*(n:ℝ)^2 ≤
          ∑ p ∈ (Finset.range (n+1)).filter (fun p => p.Prime ∧ 5 ≤ p),
            ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ)*Real.log (p:ℝ) := by
  obtain ⟨N, hN, hδ0raw, hδ1raw, hδbudgetRaw⟩ :=
    exists_finite_cutoff ε hε
  let δ : ℝ := 1/((N:ℝ)+1)
  have hδ0 : 0 < δ := by
    simpa only [δ, Nat.cast_add, Nat.cast_one] using hδ0raw
  have hδ1 : δ ≤ 1 := by
    simpa only [δ, Nat.cast_add, Nat.cast_one] using hδ1raw
  have hδbudget : 4*δ < ε/2 := by
    simpa only [δ, Nat.cast_add, Nat.cast_one, mul_one_div] using hδbudgetRaw
  have hε4 : 0 < ε/4 := by linarith
  have hsmall := posHalf_smallTail_eventually_delta δ (ε/4)
    hδ0 hδ1 hε4
  have hmedium := parameter_mediumN_eventually lambda N hN (ε/4) hε4
  filter_upwards [hsmall, hmedium,
    eventually_ge_atTop (4*(N+1))] with n hs hm hn
  intro hgram hne
  let c := ⌊δ*(n:ℝ)⌋₊
  have hc4 : 4 ≤ c := by
    apply (Nat.le_floor_iff (mul_nonneg hδ0.le (Nat.cast_nonneg n))).mpr
    have hnR : (4:ℝ)*((N:ℝ)+1) ≤ (n:ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hn
      push_cast at this
      nlinarith
    dsimp [δ]
    have hden : (0:ℝ) < (N:ℝ)+1 := by positivity
    calc
      (4:ℝ) = 4*((N:ℝ)+1)/((N:ℝ)+1) := by field_simp
      _ ≤ ((n:ℝ))/((N:ℝ)+1) :=
        div_le_div_of_nonneg_right hnR hden.le
      _ = (1/((N:ℝ)+1))*(n:ℝ) := by ring
  have hcn : c ≤ n := by
    have hle : δ*(n:ℝ) ≤ (n:ℝ) := by
      have hnR : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg _
      nlinarith [hδ1]
    have := Nat.floor_le_floor hle
    simpa only [Nat.floor_natCast] using this
  let f : ℕ → ℝ := fun p =>
    ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ)*Real.log (p:ℝ)
  have hpart := medium_prime_two_interval_partition f n c hc4 hcn
  have hsmallEq :
      (∑ p ∈ Finset.Ioc 4 c, if p.Prime then f p else 0) =
      ∑ p ∈ smallTailPrimes δ n,
        if p.Prime then f p else 0 := by
    change (∑ p ∈ Finset.Ioc 4 c, if p.Prime then f p else 0) =
      ∑ p ∈ (Finset.Ioc 4 c).filter Nat.Prime,
        if p.Prime then f p else 0
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.Prime <;> simp [hp]
  have hgramN : ∀ p ∈ Finset.Ioc c n, ∀ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      Li2.GV p (binomGram lambda n).det (normalizedDetLower n p) := by
    intro p hpI hp
    apply hgram p
    · simp only [Finset.mem_filter, Finset.mem_range]
      obtain ⟨hpc, hpn⟩ := Finset.mem_Ioc.mp hpI
      exact ⟨by omega, ⟨hp, by omega⟩⟩
    · exact hp
  have hs' := hs hne
  have hm' := hm (by omega : 0 < n)
    (by simpa only [Instances.PosHalf.Qtilde] using hne) hgramN
  have hbudget : (-523/840:ℝ)-ε ≤
      ((-523/840:ℝ)+(2/3:ℝ)/((N+1:ℕ):ℝ)^2-ε/4) +
      (-4*δ-ε/4) := by
    have hcorr : (0:ℝ) ≤ (2/3:ℝ)/((N+1:ℕ):ℝ)^2 := by positivity
    linarith
  have hbudgetN := mul_le_mul_of_nonneg_right hbudget (sq_nonneg (n:ℝ))
  rw [hpart, hsmallEq]
  dsimp only [f] at hs' hm' ⊢
  linarith

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.posHalf_medium_eventually_of_gram

end


end
