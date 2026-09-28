module
public import Li2Unified.Modular.Positive.Packed.P009
public import Li2Unified.Modular.Positive.Packed.P024
public import Mathlib.Data.Int.CardIntervalMod
public import Li2Unified.Modular.Positive.Packed.P002
public import Li2Unified.Modular.Base.Valuation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.Floor

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial MeasureTheory
open scoped BigOperators
namespace Li2Unified.Stage0.HermitePreparation
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
      simp [Li2Unified.Stage0.HermitePreparation.multiplicity, z],
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
          simp [hcz, Li2Unified.Stage0.HermitePreparation.multiplicity, hc]
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

def rawDetLower (n p : ℕ) : ℚ :=
  (∑ c : Fin p,
    ((residueCount p (4*n) c : ℚ)-2*(residueCount p n c : ℚ)) *
    ((residueCount p n c : ℚ)-2)) + ((4*n)/p : ℕ) - 2*(n/p : ℕ)

def normalizedDetLower (n p : ℕ) : ℚ :=
  let A : ℚ := (n/p : ℕ)
  let L : ℚ := ((4*n)/p : ℕ)
  let B : ℚ := ((2*n)/p : ℕ)
  (n : ℚ)*(3*L-6*A-4*B-6) +
    (p : ℚ)*(A*(2*A-L+2)+B*(B+1)) +
    min ((n : ℚ)-A*p) (4*(n : ℚ)-L*p) + L-2*A

/-- Must be proved from general-pole dissection, integral CRT jets and local
Gauss bounds. E is an independently constructed polynomial basis. -/
theorem actual_functional (lam : ℚ) (n p : ℕ) [Fact p.Prime]
    (hlam : |(lam : ℝ)| < 1)
    (hp5 : 5 ≤ p) (hpn : p ≤ n) (hsq : 4*n < p*p)
    (hunit : (lam ≠ 0 ∧ padicValRat p lam = 0) ∧
      (1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)) :
    ∃ E : Fin (2*n) → ℚ[X],
      (∀ i, (E i).natDegree < 2*n) ∧
      (Li2.coeffMat E).det ≠ 0 ∧ padicValRat p (Li2.coeffMat E).det = 0 ∧
      Li2.GV p ((Matrix.of fun i j : Fin (2*n) =>
        ParameterFamily.numeratorFunctional lam (4*n)
          ((Li2.D n)^3 * E i * E j)).det) (rawDetLower n p) := by
  simpa only [rawDetLower, residueCount,
    Li2Unified.Proofs.Hermite.CountsCore.residueCount, add_sub_assoc] using
    (Li2Unified.Proofs.Hermite.generalOriginalFunctionalBasis_of_entries lam n hpn
      (fun i j => Li2Unified.Proofs.Hermite.actual_general_original_entry_GV
        lam n hlam hsq hpn hunit i j))

/-- Original normalized matrix, connected to Qtilde by Qtilde_eq_binomGram_det. -/
theorem actual_binomGram (lam : ℚ) (n p : ℕ) [Fact p.Prime]
    (hlam : |(lam : ℝ)| < 1)
    (hp5 : 5 ≤ p) (hpn : p ≤ n) (hsq : 4*n < p*p)
    (hunit : (lam ≠ 0 ∧ padicValRat p lam = 0) ∧
      (1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)) :
    Li2.GV p (ParameterFamily.binomGram lam n).det (normalizedDetLower n p) := by
  obtain ⟨E,hE,he,hev,hraw⟩ := actual_functional lam n p hlam hp5 hpn hsq hunit
  have hnorm : rawDetLower n p + Li2.normVal p n = normalizedDetLower n p := by
    simpa only [rawDetLower, normalizedDetLower, residueCount,
      Li2Unified.Proofs.Hermite.matchingCount] using
      Li2Unified.Proofs.Hermite.matchingCount_normalized_sum (p := p) n
  have hK : 4*n < p^2 := by simpa only [pow_two] using hsq
  simpa only [hnorm] using
    Li2Unified.Proofs.Hermite.actual_binomGram_of_unit_basis lam n hK E hE he hev
      (rawDetLower n p) hraw

def profile (x : ℝ) : ℝ :=
  let A : ℝ := ⌊1/x⌋
  let L : ℝ := ⌊4/x⌋
  let B : ℝ := ⌊2/x⌋
  3*L-6*A-4*B-6+x*(A*(2*A-L+2)+B*(B+1))+min (1-A*x) (4-L*x)

def cellIntegral (A : ℝ) : ℝ :=
  -(384*A^4+768*A^3+563*A^2+179*A+21) /
    (A*(A+1)*(2*A+1)*(3*A+1)*(3*A+2)*(4*A+1)*(4*A+3))

namespace ProfileCellBridge

open MeasureTheory Set
open scoped Interval

open Li2Unified.Stage0.HermitePreparation

open Li2Unified.Stage0.HermitePreparation

/-- Algebraic value of the integral of `c + d*x` from `u` to `v`. -/
def affinePrimitiveDifference (c d u v : ℝ) : ℝ :=
  c * (v-u) + d * (v^2-u^2)/2

/-- The six rational affine pieces indexed by θ = 1/x - A. -/
def profileCellAlgebraicSum (A : ℝ) : ℝ :=
  affinePrimitiveDifference (-2*A-5) (2*A^2+3*A) (4/(4*A+1)) (1/A) +
  affinePrimitiveDifference (-2*A+1) (2*A^2-A-1) (3/(3*A+1)) (4/(4*A+1)) +
  affinePrimitiveDifference (-2*A-2) (2*A^2+2*A) (2/(2*A+1)) (3/(3*A+1)) +
  affinePrimitiveDifference (-2*A) (2*A^2+2*A) (3/(3*A+2)) (2/(2*A+1)) +
  affinePrimitiveDifference (-2*A-3) (2*A^2+5*A+2) (4/(4*A+3)) (3/(3*A+2)) +
  affinePrimitiveDifference (-2*A+3) (2*A^2+A-1) (1/(A+1)) (4/(4*A+3))

/-- Literal rational cancellation for the six-cell formula; floor and integral
bridges are separate. -/
theorem profileCellAlgebraicSum_eq_cellIntegral (A : ℝ) (hA : 1 ≤ A) :
    profileCellAlgebraicSum A = cellIntegral A := by
  have h0 : A ≠ 0 := by linarith
  have h1 : A+1 ≠ 0 := by linarith
  have h2 : 2*A+1 ≠ 0 := by linarith
  have h3 : 3*A+1 ≠ 0 := by linarith
  have h4 : 3*A+2 ≠ 0 := by linarith
  have h5 : 4*A+1 ≠ 0 := by linarith
  have h6 : 4*A+3 ≠ 0 := by linarith
  unfold profileCellAlgebraicSum affinePrimitiveDifference cellIntegral
  field_simp [h0, h1, h2, h3, h4, h5, h6]
  ring

open Li2Unified.Stage0.HermitePreparation
open MeasureTheory Set

end ProfileCellBridge

theorem cell_positive_remainder (A : ℝ) (hA : 2 ≤ A) :
    -(2/3:ℝ)*(A⁻¹^2-(A+1)⁻¹^2) < cellIntegral A := by
  have heq : cellIntegral A + (2 / 3 : ℝ) * (A⁻¹ ^ 2 - (A + 1)⁻¹ ^ 2) =
      (223 * A ^ 4 + 446 * A ^ 3 + 326 * A ^ 2 + 103 * A + 12) /
        (3 * A ^ 2 * (A + 1) ^ 2 * (2 * A + 1) * (3 * A + 1) *
          (3 * A + 2) * (4 * A + 1) * (4 * A + 3)) := by
    have h0 : A ≠ 0 := by linarith
    have h1 : A + 1 ≠ 0 := by linarith
    have h2 : 2 * A + 1 ≠ 0 := by linarith
    have h3 : 3 * A + 1 ≠ 0 := by linarith
    have h4 : 3 * A + 2 ≠ 0 := by linarith
    have h5 : 4 * A + 1 ≠ 0 := by linarith
    have h6 : 4 * A + 3 ≠ 0 := by linarith
    unfold cellIntegral
    field_simp [h0, h1, h2, h3, h4, h5, h6]
    ring
  have hApos : 0 < A := by linarith
  have hnum : 0 < 223 * A ^ 4 + 446 * A ^ 3 + 326 * A ^ 2 + 103 * A + 12 := by
    positivity
  have hden : 0 < 3 * A ^ 2 * (A + 1) ^ 2 * (2 * A + 1) * (3 * A + 1) *
      (3 * A + 2) * (4 * A + 1) * (4 * A + 3) := by
    positivity
  have hpos := div_pos hnum hden
  linarith

namespace ProfileIntegralLowerBridge
open Finset Set

end ProfileIntegralLowerBridge

end
end Li2Unified.Stage0.HermitePreparation

#print axioms Li2Unified.Stage0.HermitePreparation.actual_binomGram

#print axioms Li2Unified.Stage0.HermitePreparation.actual_functional
#print axioms Li2Unified.Stage0.HermitePreparation.actual_binomGram

end

end
