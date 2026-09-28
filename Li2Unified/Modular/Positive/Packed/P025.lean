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

/-- Endpoint values do not affect the integral of a function affine in the
interior. This also supplies the integrability needed to concatenate cells. -/
theorem integral_eq_affine_of_open (f : ℝ → ℝ) (u v c d : ℝ)
    (huv : u ≤ v) (h : ∀ x, u < x → x < v → f x = c + d*x) :
    IntervalIntegrable f volume u v ∧
      (∫ x in u..v, f x) = c*(v-u)+d*(v^2-u^2)/2 := by
  let g : ℝ → ℝ := fun x => c + d*x
  have hgcont : Continuous g := by fun_prop
  have hge : IntervalIntegrable g volume u v := hgcont.intervalIntegrable u v
  have hae : f =ᵐ[volume.restrict (Ι u v)] g := by
    rw [uIoc_of_le huv, Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Measure.ae_ne volume v] with x hx hxI
    exact h x hxI.1 (lt_of_le_of_ne hxI.2 hx)
  have hfe : IntervalIntegrable f volume u v := hge.congr_ae hae.symm
  refine ⟨hfe, ?_⟩
  have hc : IntervalIntegrable (fun _ : ℝ => c) volume u v :=
    continuous_const.intervalIntegrable u v
  have hd : IntervalIntegrable (fun x : ℝ => d*x) volume u v :=
    (continuous_const.mul continuous_id).intervalIntegrable u v
  calc
    (∫ x in u..v, f x) = ∫ x in u..v, g x :=
      intervalIntegral.integral_congr_ae_restrict hae
    _ = c*(v-u)+d*(v^2-u^2)/2 := by
      dsimp [g]
      rw [intervalIntegral.integral_add hc hd,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, integral_id]
      ring

/-- The reciprocal of an interior point lies in the reversed open interval. -/
theorem reciprocal_open_bounds (α β x : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hleft : β⁻¹ < x) (hright : x < α⁻¹) :
    0 < x ∧ α < x⁻¹ ∧ x⁻¹ < β := by
  have hx : 0 < x := (inv_pos.mpr hβ).trans hleft
  have hαx : α < x⁻¹ := by
    have := (inv_lt_inv₀ (inv_pos.mpr hα) hx).2 hright
    simpa using this
  have hxβ : x⁻¹ < β := by
    have := (inv_lt_inv₀ hx (inv_pos.mpr hβ)).2 hleft
    simpa using this
  exact ⟨hx, hαx, hxβ⟩

open Li2Unified.Stage0.HermitePreparation

/-- Interior of the first sixth of one reciprocal profile cell. -/
theorem profile_piece_zero (A : ℕ) (x : ℝ) (_hA : 1 ≤ A) (hx : 0 < x)
    (hlo : (A:ℝ) < x⁻¹) (hhi : x⁻¹ < (A:ℝ)+1/4) :
    profile x = (2*(A:ℝ)^2+3*(A:ℝ))*x-2*(A:ℝ)-5 := by
  have hfloor (m : ℕ) (y : ℝ) (hlo' : (m:ℝ) ≤ y)
      (hhi' : y < (m:ℝ)+1) :
      (⌊y⌋ : ℝ) = (m:ℝ) := by
    have h : ⌊y⌋ = (m:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast hlo'
      · simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hhi'
    exact_mod_cast h
  have h1lo : (A:ℝ) ≤ (1:ℝ)/x := by simpa only [one_div] using hlo.le
  have h1hi : (1:ℝ)/x < (A:ℝ)+1 := by
    rw [one_div]
    linarith only [hhi]
  have h2lo : ((2*A:ℕ):ℝ) ≤ (2:ℝ)/x := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hlo]
  have h2hi : (2:ℝ)/x < ((2*A:ℕ):ℝ)+1 := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hhi]
  have h4lo : ((4*A:ℕ):ℝ) ≤ (4:ℝ)/x := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hlo]
  have h4hi : (4:ℝ)/x < ((4*A:ℕ):ℝ)+1 := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hhi]
  have hf1 := hfloor A (1/x) h1lo h1hi
  have hf2 := hfloor (2*A) (2/x) h2lo h2hi
  have hf4 := hfloor (4*A) (4/x) h4lo h4hi
  have hAx : (A:ℝ)*x < 1 := by
    have h := mul_lt_mul_of_pos_right hlo hx
    simpa only [inv_mul_cancel₀ hx.ne'] using h
  have hmin : min (1-(A:ℝ)*x) (4-((4*A:ℕ):ℝ)*x) = 1-(A:ℝ)*x := by
    apply min_eq_left
    push_cast
    nlinarith only [hAx]
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

/-- The three floors on any subcell with `lo < 1/x - A < hi`. -/
private theorem profile_floors_on_theta (A j b : ℕ) (x lo hi : ℝ)
    (hθlo : (A:ℝ)+lo < x⁻¹) (hθhi : x⁻¹ < (A:ℝ)+hi)
    (hlo0 : 0 ≤ lo) (hhi1 : hi ≤ 1)
    (hbLo : (b:ℝ) ≤ 2*lo) (hbHi : 2*hi ≤ (b:ℝ)+1)
    (hjLo : (j:ℝ) ≤ 4*lo) (hjHi : 4*hi ≤ (j:ℝ)+1) :
    (⌊(1:ℝ)/x⌋ : ℝ) = (A:ℝ) ∧
      (⌊(2:ℝ)/x⌋ : ℝ) = ((2*A+b:ℕ):ℝ) ∧
      (⌊(4:ℝ)/x⌋ : ℝ) = ((4*A+j:ℕ):ℝ) := by
  have hfloor (m : ℕ) (y : ℝ) (hlo' : (m:ℝ) ≤ y)
      (hhi' : y < (m:ℝ)+1) : (⌊y⌋ : ℝ) = (m:ℝ) := by
    have h : ⌊y⌋ = (m:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast hlo'
      · simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hhi'
    exact_mod_cast h
  have h1lo : (A:ℝ) ≤ (1:ℝ)/x := by
    rw [one_div]
    linarith only [hθlo, hlo0]
  have h1hi : (1:ℝ)/x < (A:ℝ)+1 := by
    rw [one_div]
    linarith only [hθhi, hhi1]
  have h2lo : ((2*A+b:ℕ):ℝ) ≤ (2:ℝ)/x := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hθlo, hbLo]
  have h2hi : (2:ℝ)/x < ((2*A+b:ℕ):ℝ)+1 := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hθhi, hbHi]
  have h4lo : ((4*A+j:ℕ):ℝ) ≤ (4:ℝ)/x := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hθlo, hjLo]
  have h4hi : (4:ℝ)/x < ((4*A+j:ℕ):ℝ)+1 := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hθhi, hjHi]
  exact ⟨hfloor A (1/x) h1lo h1hi,
    hfloor (2*A+b) (2/x) h2lo h2hi,
    hfloor (4*A+j) (4/x) h4lo h4hi⟩

private theorem profile_min_first (A j : ℕ) (x : ℝ) (hx : 0 < x)
    (hθ : (A:ℝ)+(j:ℝ)/3 < x⁻¹) :
    min (1-(A:ℝ)*x) (4-((4*A+j:ℕ):ℝ)*x) = 1-(A:ℝ)*x := by
  have hm := mul_lt_mul_of_pos_right hθ hx
  have hb : ((A:ℝ)+(j:ℝ)/3)*x < 1 := by
    simpa only [inv_mul_cancel₀ hx.ne'] using hm
  apply min_eq_left
  push_cast
  nlinarith only [hb]

private theorem profile_min_second (A j : ℕ) (x : ℝ) (hx : 0 < x)
    (hθ : x⁻¹ < (A:ℝ)+(j:ℝ)/3) :
    min (1-(A:ℝ)*x) (4-((4*A+j:ℕ):ℝ)*x) =
      4-((4*A+j:ℕ):ℝ)*x := by
  have hm := mul_lt_mul_of_pos_right hθ hx
  have hb : 1 < ((A:ℝ)+(j:ℝ)/3)*x := by
    simpa only [inv_mul_cancel₀ hx.ne'] using hm
  apply min_eq_right
  push_cast
  nlinarith only [hb]

theorem profile_piece_one (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+1/4 < x⁻¹) (hhi : x⁻¹ < (A:ℝ)+1/3) :
    profile x = (2*(A:ℝ)^2-(A:ℝ)-1)*x-2*(A:ℝ)+1 := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_on_theta A 1 0 x (1/4) (1/3) hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_second A 1 x hx (by simpa only [Nat.cast_one] using hhi)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

theorem profile_piece_two (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+1/3 < x⁻¹) (hhi : x⁻¹ < (A:ℝ)+1/2) :
    profile x = (2*(A:ℝ)^2+2*(A:ℝ))*x-2*(A:ℝ)-2 := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_on_theta A 1 0 x (1/3) (1/2) hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_first A 1 x hx (by simpa only [Nat.cast_one] using hlo)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

theorem profile_piece_three (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+1/2 < x⁻¹) (hhi : x⁻¹ < (A:ℝ)+2/3) :
    profile x = (2*(A:ℝ)^2+2*(A:ℝ))*x-2*(A:ℝ) := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_on_theta A 2 1 x (1/2) (2/3) hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_second A 2 x hx (by norm_num at hhi ⊢; exact hhi)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

theorem profile_piece_four (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+2/3 < x⁻¹) (hhi : x⁻¹ < (A:ℝ)+3/4) :
    profile x = (2*(A:ℝ)^2+5*(A:ℝ)+2)*x-2*(A:ℝ)-3 := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_on_theta A 2 1 x (2/3) (3/4) hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_first A 2 x hx (by norm_num at hlo ⊢; exact hlo)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

theorem profile_piece_five (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+3/4 < x⁻¹) (hhi : x⁻¹ < (A:ℝ)+1) :
    profile x = (2*(A:ℝ)^2+(A:ℝ)-1)*x-2*(A:ℝ)+3 := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_on_theta A 3 1 x (3/4) 1 hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_second A 3 x hx (by norm_num at hhi ⊢; exact hhi)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

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

private theorem profile_subcell_integral (A : ℕ) (lo hi c d : ℝ)
    (hlo : 0 < (A:ℝ)+lo) (hgap : lo < hi)
    (hform : ∀ x, 0 < x → (A:ℝ)+lo < x⁻¹ → x⁻¹ < (A:ℝ)+hi →
      profile x = c+d*x) :
    IntervalIntegrable profile volume (((A:ℝ)+hi)⁻¹) (((A:ℝ)+lo)⁻¹) ∧
    (∫ x in (((A:ℝ)+hi)⁻¹)..(((A:ℝ)+lo)⁻¹), profile x) =
      c*(((A:ℝ)+lo)⁻¹-((A:ℝ)+hi)⁻¹) +
      d*((((A:ℝ)+lo)⁻¹)^2-(((A:ℝ)+hi)⁻¹)^2)/2 := by
  have hhi : 0 < (A:ℝ)+hi := by linarith
  have horder : (((A:ℝ)+hi)⁻¹) ≤ (((A:ℝ)+lo)⁻¹) := by
    have := one_div_lt_one_div_of_lt hlo (by linarith : (A:ℝ)+lo < (A:ℝ)+hi)
    simpa only [one_div] using this.le
  apply integral_eq_affine_of_open profile _ _ c d horder
  intro x hleft hright
  obtain ⟨hx, hθlo, hθhi⟩ :=
    reciprocal_open_bounds ((A:ℝ)+lo) ((A:ℝ)+hi) x hlo hhi hleft hright
  exact hform x hx hθlo hθhi

private theorem profile_piece_integrals (A : ℕ) (hA : 1 ≤ A) :
    (IntervalIntegrable profile volume (((A:ℝ)+1)⁻¹) (((A:ℝ)+3/4)⁻¹) ∧
      (∫ x in (((A:ℝ)+1)⁻¹)..(((A:ℝ)+3/4)⁻¹), profile x) =
        (-2*(A:ℝ)+3)*((((A:ℝ)+3/4)⁻¹)-(((A:ℝ)+1)⁻¹)) +
        (2*(A:ℝ)^2+(A:ℝ)-1)*(((((A:ℝ)+3/4)⁻¹)^2)-((((A:ℝ)+1)⁻¹)^2))/2) ∧
    (IntervalIntegrable profile volume (((A:ℝ)+3/4)⁻¹) (((A:ℝ)+2/3)⁻¹) ∧
      (∫ x in (((A:ℝ)+3/4)⁻¹)..(((A:ℝ)+2/3)⁻¹), profile x) =
        (-2*(A:ℝ)-3)*((((A:ℝ)+2/3)⁻¹)-(((A:ℝ)+3/4)⁻¹)) +
        (2*(A:ℝ)^2+5*(A:ℝ)+2)*(((((A:ℝ)+2/3)⁻¹)^2)-((((A:ℝ)+3/4)⁻¹)^2))/2) ∧
    (IntervalIntegrable profile volume (((A:ℝ)+2/3)⁻¹) (((A:ℝ)+1/2)⁻¹) ∧
      (∫ x in (((A:ℝ)+2/3)⁻¹)..(((A:ℝ)+1/2)⁻¹), profile x) =
        (-2*(A:ℝ))*((((A:ℝ)+1/2)⁻¹)-(((A:ℝ)+2/3)⁻¹)) +
        (2*(A:ℝ)^2+2*(A:ℝ))*(((((A:ℝ)+1/2)⁻¹)^2)-((((A:ℝ)+2/3)⁻¹)^2))/2) ∧
    (IntervalIntegrable profile volume (((A:ℝ)+1/2)⁻¹) (((A:ℝ)+1/3)⁻¹) ∧
      (∫ x in (((A:ℝ)+1/2)⁻¹)..(((A:ℝ)+1/3)⁻¹), profile x) =
        (-2*(A:ℝ)-2)*((((A:ℝ)+1/3)⁻¹)-(((A:ℝ)+1/2)⁻¹)) +
        (2*(A:ℝ)^2+2*(A:ℝ))*(((((A:ℝ)+1/3)⁻¹)^2)-((((A:ℝ)+1/2)⁻¹)^2))/2) ∧
    (IntervalIntegrable profile volume (((A:ℝ)+1/3)⁻¹) (((A:ℝ)+1/4)⁻¹) ∧
      (∫ x in (((A:ℝ)+1/3)⁻¹)..(((A:ℝ)+1/4)⁻¹), profile x) =
        (-2*(A:ℝ)+1)*((((A:ℝ)+1/4)⁻¹)-(((A:ℝ)+1/3)⁻¹)) +
        (2*(A:ℝ)^2-(A:ℝ)-1)*(((((A:ℝ)+1/4)⁻¹)^2)-((((A:ℝ)+1/3)⁻¹)^2))/2) ∧
    (IntervalIntegrable profile volume (((A:ℝ)+1/4)⁻¹) (((A:ℝ))⁻¹) ∧
      (∫ x in (((A:ℝ)+1/4)⁻¹)..(((A:ℝ))⁻¹), profile x) =
        (-2*(A:ℝ)-5)*((((A:ℝ))⁻¹)-(((A:ℝ)+1/4)⁻¹)) +
        (2*(A:ℝ)^2+3*(A:ℝ))*(((((A:ℝ))⁻¹)^2)-((((A:ℝ)+1/4)⁻¹)^2))/2) := by
  have hApos : (0:ℝ) < A := by exact_mod_cast (Nat.zero_lt_of_lt hA)
  constructor
  · exact profile_subcell_integral A (3/4) 1 (-2*(A:ℝ)+3)
      (2*(A:ℝ)^2+(A:ℝ)-1) (by linarith) (by norm_num) (by
        intro x hx hlo hhi
        rw [profile_piece_five A x hx (by simpa using hlo) (by simpa using hhi)]
        ring)
  constructor
  · exact profile_subcell_integral A (2/3) (3/4) (-2*(A:ℝ)-3)
      (2*(A:ℝ)^2+5*(A:ℝ)+2) (by linarith) (by norm_num) (by
        intro x hx hlo hhi
        rw [profile_piece_four A x hx (by simpa using hlo) (by simpa using hhi)]
        ring)
  constructor
  · exact profile_subcell_integral A (1/2) (2/3) (-2*(A:ℝ))
      (2*(A:ℝ)^2+2*(A:ℝ)) (by linarith) (by norm_num) (by
        intro x hx hlo hhi
        rw [profile_piece_three A x hx (by simpa using hlo) (by simpa using hhi)]
        ring)
  constructor
  · exact profile_subcell_integral A (1/3) (1/2) (-2*(A:ℝ)-2)
      (2*(A:ℝ)^2+2*(A:ℝ)) (by linarith) (by norm_num) (by
        intro x hx hlo hhi
        rw [profile_piece_two A x hx (by simpa using hlo) (by simpa using hhi)]
        ring)
  constructor
  · exact profile_subcell_integral A (1/4) (1/3) (-2*(A:ℝ)+1)
      (2*(A:ℝ)^2-(A:ℝ)-1) (by linarith) (by norm_num) (by
        intro x hx hlo hhi
        rw [profile_piece_one A x hx (by simpa using hlo) (by simpa using hhi)]
        ring)
  · simpa only [add_zero] using profile_subcell_integral A 0 (1/4) (-2*(A:ℝ)-5)
      (2*(A:ℝ)^2+3*(A:ℝ)) (by linarith) (by norm_num) (by
        intro x hx hlo hhi
        rw [profile_piece_zero A x hA hx (by simpa using hlo) (by simpa using hhi)]
        ring)

private theorem inv_add_fraction (a b k : ℝ) (hk : k ≠ 0) (hd : k*a+b ≠ 0) :
    (a+b/k)⁻¹ = k/(k*a+b) := by
  have h : a+b/k = (k*a+b)/k := by field_simp
  rw [h]
  field_simp

/-- The original profile cell integral, proved using all six floor branches. -/
theorem profile_cell_integral_actual (A : ℕ) (hA : 1 ≤ A) :
    (∫ x in (1/((A:ℝ)+1))..(1/(A:ℝ)), profile x) = cellIntegral A := by
  rcases profile_piece_integrals A hA with ⟨h5, h4, h3, h2, h1, h0⟩
  have h43210 := h4.1.trans (h3.1.trans (h2.1.trans (h1.1.trans h0.1)))
  have h3210 := h3.1.trans (h2.1.trans (h1.1.trans h0.1))
  have h210 := h2.1.trans (h1.1.trans h0.1)
  have h10 := h1.1.trans h0.1
  simp only [one_div]
  rw [← intervalIntegral.integral_add_adjacent_intervals h5.1 h43210,
    ← intervalIntegral.integral_add_adjacent_intervals h4.1 h3210,
    ← intervalIntegral.integral_add_adjacent_intervals h3.1 h210,
    ← intervalIntegral.integral_add_adjacent_intervals h2.1 h10,
    ← intervalIntegral.integral_add_adjacent_intervals h1.1 h0.1,
    h5.2, h4.2, h3.2, h2.2, h1.2, h0.2]
  have hAreal : 1 ≤ (A:ℝ) := by exact_mod_cast hA
  rw [← profileCellAlgebraicSum_eq_cellIntegral (A:ℝ) hAreal]
  dsimp [profileCellAlgebraicSum, affinePrimitiveDifference]
  have hA0 : (A:ℝ) ≠ 0 := by positivity
  have h41 : 4*(A:ℝ)+1 ≠ 0 := by positivity
  have h43 : 4*(A:ℝ)+3 ≠ 0 := by positivity
  have h31 : 3*(A:ℝ)+1 ≠ 0 := by positivity
  have h32 : 3*(A:ℝ)+2 ≠ 0 := by positivity
  have h21 : 2*(A:ℝ)+1 ≠ 0 := by positivity
  have hA1 : (A:ℝ)+1 ≠ 0 := by positivity
  rw [inv_add_fraction (A:ℝ) 1 4 (by norm_num) h41,
    inv_add_fraction (A:ℝ) 3 4 (by norm_num) h43,
    inv_add_fraction (A:ℝ) 1 3 (by norm_num) h31,
    inv_add_fraction (A:ℝ) 2 3 (by norm_num) h32,
    inv_add_fraction (A:ℝ) 1 2 (by norm_num) h21]
  simp only [one_div]
  ring
end ProfileCellBridge

theorem profile_cell_integral (A : ℕ) (hA : 1 ≤ A) :
    (∫ x in (1/((A:ℝ)+1))..(1/(A:ℝ)), profile x) = cellIntegral A := by
  exact ProfileCellBridge.profile_cell_integral_actual A hA

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

theorem profile_fract_identity (x : ℝ) (hx : 0 < x) :
    profile x =
      6 * Int.fract (1/x) - 2 * Int.fract (4/x) - 2 +
      x * (2 * Int.fract (1/x)^2 - Int.fract (1/x)*Int.fract (4/x) -
        2*Int.fract (1/x) + Int.fract (2/x)^2 - Int.fract (2/x) +
        min (Int.fract (1/x)) (Int.fract (4/x))) := by
  let u : ℝ := Int.fract (1/x)
  let v : ℝ := Int.fract (4/x)
  let w : ℝ := Int.fract (2/x)
  have hx0 : x ≠ 0 := ne_of_gt hx
  have h1 : (⌊1/x⌋ : ℝ) = 1/x-u := by
    change (⌊1/x⌋ : ℝ) = 1/x-(1/x-(⌊1/x⌋ : ℝ))
    ring
  have h4 : (⌊4/x⌋ : ℝ) = 4/x-v := by
    change (⌊4/x⌋ : ℝ) = 4/x-(4/x-(⌊4/x⌋ : ℝ))
    ring
  have h2 : (⌊2/x⌋ : ℝ) = 2/x-w := by
    change (⌊2/x⌋ : ℝ) = 2/x-(2/x-(⌊2/x⌋ : ℝ))
    ring
  have he1 : 1 - (⌊1/x⌋ : ℝ)*x = x*u := by
    rw [h1]
    field_simp
    ring
  have he4 : 4 - (⌊4/x⌋ : ℝ)*x = x*v := by
    rw [h4]
    field_simp
    ring
  have hmin : min (1 - (⌊1/x⌋ : ℝ)*x) (4 - (⌊4/x⌋ : ℝ)*x) =
      x*min u v := by
    rw [he1, he4]
    rcases le_total u v with huv | hvu
    · rw [min_eq_left huv, min_eq_left (mul_le_mul_of_nonneg_left huv hx.le)]
    · rw [min_eq_right hvu, min_eq_right (mul_le_mul_of_nonneg_left hvu hx.le)]
  unfold profile
  dsimp only
  rw [hmin, h1, h4, h2]
  change 3*(4/x-v)-6*(1/x-u)-4*(2/x-w)-6+
      x*((1/x-u)*(2*(1/x-u)-(4/x-v)+2)+(2/x-w)*((2/x-w)+1))+
      x*min u v =
    6*u-2*v-2+x*(2*u^2-u*v-2*u+w^2-w+min u v)
  field_simp
  ring

/-- A uniform bound through the accumulating floor discontinuities at zero. -/
theorem profile_bound_unit (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |profile x| ≤ 8 := by
  by_cases hx : x = 0
  · subst x
    norm_num [profile]
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  let u : ℝ := Int.fract (1/x)
  let v : ℝ := Int.fract (4/x)
  let w : ℝ := Int.fract (2/x)
  have hu0 : 0 ≤ u := Int.fract_nonneg _
  have hv0 : 0 ≤ v := Int.fract_nonneg _
  have hw0 : 0 ≤ w := Int.fract_nonneg _
  have hu1 : u ≤ 1 := (Int.fract_lt_one _).le
  have hv1 : v ≤ 1 := (Int.fract_lt_one _).le
  have hw1 : w ≤ 1 := (Int.fract_lt_one _).le
  have hm0 : 0 ≤ min u v := le_min hu0 hv0
  have hm1 : min u v ≤ 1 := (min_le_left u v).trans hu1
  have huv0 : 0 ≤ u*v := mul_nonneg hu0 hv0
  have huv1 : u*v ≤ 1 := by
    calc
      u*v ≤ u*1 := mul_le_mul_of_nonneg_left hv1 hu0
      _ = u := mul_one u
      _ ≤ 1 := hu1
  have huSq : u^2 ≤ 1 := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  have hwSq : w^2 ≤ 1 := by nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hw1)]
  let t := 2*u^2-u*v-2*u+w^2-w+min u v
  have ht : -4 ≤ t ∧ t ≤ 4 := by
    dsimp [t]
    constructor <;> nlinarith [sq_nonneg u, sq_nonneg w]
  have hxt : -4 ≤ x*t ∧ x*t ≤ 4 := by
    constructor
    · have := mul_le_mul_of_nonneg_left ht.1 hx0
      nlinarith
    · have := mul_le_mul_of_nonneg_left ht.2 hx0
      nlinarith
  rw [profile_fract_identity x hxpos]
  change |6*u-2*v-2+x*t| ≤ 8
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem profile_measurable : Measurable profile := by
  unfold profile
  measurability

/-- The uniform bound makes the infinitely many floor jumps harmless at zero. -/
theorem profile_intervalIntegrable_zero_to (y : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    IntervalIntegrable profile volume 0 y := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hy0).2
  have hfinite : volume (Ioc (0:ℝ) y) ≠ ⊤ := by simp
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioc (0:ℝ) y)),
      ‖profile x‖ ≤ 8 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    exact profile_bound_unit x hx.1.le (hx.2.trans hy1)
  exact Measure.integrableOn_of_bounded hfinite
    profile_measurable.aestronglyMeasurable hbound

theorem profile_intervalIntegrable_between (a b : ℝ)
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    IntervalIntegrable profile volume a b := by
  have hf := profile_intervalIntegrable_zero_to 1 (by norm_num) (by norm_num)
  apply hf.mono_set
  rw [uIcc_of_le hab, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  intro x hx
  exact ⟨ha0.trans hx.1, hx.2.trans hb1⟩

/-- The initial partial cell has integral at most eight times its length. -/
theorem profile_tail_integral_bound (y : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |∫ x in (0:ℝ)..y, profile x| ≤ 8*y := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := y) (C := 8) (f := profile) (by
      intro x hx
      have hx' : x ∈ Ioc (0:ℝ) y := by simpa only [uIoc_of_le hy0] using hx
      rw [Real.norm_eq_abs]
      exact profile_bound_unit x hx'.1.le (hx'.2.trans hy1))
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hy0] using h

private theorem reciprocal_square_telescope_from3 (N : ℕ) (hN : 2 ≤ N) :
    (∑ A ∈ Finset.Ico 3 (N+1),
      (((A:ℝ)⁻¹)^2 - ((((A:ℝ)+1)⁻¹)^2))) =
      ((3:ℝ)⁻¹)^2 - ((((N:ℝ)+1)⁻¹)^2) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hN2 : 2 ≤ N
    · rw [sum_Ico_succ_top (by omega : 3 ≤ N+1), ih hN2]
      push_cast
      ring
    · have hN1 : N = 1 := by omega
      subst N
      norm_num

/-- The cell `A=2` supplies a fixed positive surplus which survives the
limit of reciprocal cutoffs. -/
theorem profile_cell_sum_uniform_margin (N : ℕ) (hN : 2 ≤ N) :
    (-523/840:ℝ) + (2/3:ℝ)/((N+1:ℕ):ℝ)^2 + 481/166320 ≤
      ∑ A ∈ Finset.Ico (1:ℕ) (N+1), cellIntegral A := by
  have htail :
      (∑ A ∈ Finset.Ico (3:ℕ) (N+1),
        -(2/3:ℝ)*((((A:ℝ)⁻¹)^2)-(((((A:ℝ)+1)⁻¹)^2)))) ≤
      ∑ A ∈ Finset.Ico (3:ℕ) (N+1), cellIntegral A := by
    apply Finset.sum_le_sum
    intro A hA
    have hA2 : (2:ℝ) ≤ A := by
      have hAnat : 2 ≤ A := by have := (mem_Ico.mp hA).1; omega
      exact_mod_cast hAnat
    exact (cell_positive_remainder (A:ℝ) hA2).le
  have htel := reciprocal_square_telescope_from3 N hN
  rw [← sum_Ico_consecutive (f := fun A : ℕ => cellIntegral A)
    (by decide : 1 ≤ 3) (by omega : 3 ≤ N+1)]
  have hfirst :
      (∑ A ∈ Finset.Ico (1:ℕ) 3, cellIntegral A) = -30251/55440 := by
    have hIco : Finset.Ico (1:ℕ) 3 = {1, 2} := by decide
    rw [hIco]
    norm_num [cellIntegral]
  rw [hfirst]
  have hsum :
      (∑ A ∈ Finset.Ico (3:ℕ) (N+1),
        -(2/3:ℝ)*((((A:ℝ)⁻¹)^2)-(((((A:ℝ)+1)⁻¹)^2)))) =
      -(2/3:ℝ)*((((3:ℝ)⁻¹)^2)-((((N:ℝ)+1)⁻¹)^2)) := by
    rw [← Finset.mul_sum, htel]
  rw [hsum] at htail
  push_cast at htail ⊢
  simp only [div_eq_mul_inv, ← inv_pow] at htail ⊢
  norm_num at htail ⊢
  linarith

theorem profile_finite_cells_integral (N : ℕ) :
    (∫ x in (1/((N:ℝ)+1))..1, profile x) =
      ∑ A ∈ Finset.Ico (1:ℕ) (N+1), cellIntegral A := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    let a : ℝ := 1/((N:ℝ)+2)
    let b : ℝ := 1/((N:ℝ)+1)
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have hab : a ≤ b := by
      dsimp [a, b]
      exact one_div_le_one_div_of_le (by positivity : (0:ℝ) < (N:ℝ)+1)
        (by linarith)
    have hb1 : b ≤ 1 := by
      dsimp [b]
      have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
        (show (1:ℝ) ≤ (N:ℝ)+1 by
          have := Nat.cast_nonneg (α := ℝ) N
          linarith)
      simpa using h
    have hleft := profile_intervalIntegrable_between a b ha0 hab hb1
    have hright := profile_intervalIntegrable_between b 1
      (ha0.trans hab) hb1 (by norm_num)
    have hadd : (N:ℝ)+1+1 = (N:ℝ)+2 := by ring
    have hcell : (∫ x in a..b, profile x) = cellIntegral (N+1) := by
      simpa only [a, b, Nat.cast_add, Nat.cast_one, hadd] using
        profile_cell_integral (N+1) (by omega)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
    calc
      (∫ x in (1/(((N+1:ℕ):ℝ)+1))..1, profile x) =
          (∫ x in a..b, profile x) + ∫ x in b..1, profile x := by
        simpa only [a, b, Nat.cast_add, Nat.cast_one, hadd] using hsplit.symm
      _ = cellIntegral (N+1) +
          ∑ A ∈ Finset.Ico (1:ℕ) (N+1), cellIntegral A := by
        rw [hcell]
        simpa only [b] using congrArg (fun z : ℝ => cellIntegral (N+1) + z) ih
      _ = ∑ A ∈ Finset.Ico (1:ℕ) ((N+1)+1), cellIntegral A := by
        rw [sum_Ico_succ_top (by omega : 1 ≤ N+1)]
        simp only [Nat.cast_add, Nat.cast_one]
        ac_rfl

theorem profile_integral_lower_actual :
    (-523/840:ℝ) < ∫ x in (0:ℝ)..1, profile x := by
  let y : ℝ := 1/4096
  have hy0 : 0 ≤ y := by norm_num [y]
  have hy1 : y ≤ 1 := by norm_num [y]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (profile_intervalIntegrable_zero_to y hy0 hy1)
    (profile_intervalIntegrable_between y 1 hy0 hy1 (by norm_num))
  have hfinite : (∫ x in y..1, profile x) =
      ∑ A ∈ Finset.Ico (1:ℕ) 4096, cellIntegral A := by
    convert profile_finite_cells_integral 4095 using 1; norm_num [y]
  have hmargin :
      (-523/840:ℝ)+(2/3:ℝ)/((4096:ℕ):ℝ)^2+481/166320 ≤
        ∫ x in y..1, profile x := by
    rw [hfinite]
    simpa using profile_cell_sum_uniform_margin 4095 (by omega)
  have htail : -(8*y) ≤ ∫ x in (0:ℝ)..y, profile x :=
    (abs_le.mp (profile_tail_integral_bound y hy0 hy1)).1
  have hbudget : (-523/840:ℝ) <
      -(8*y)+((-523/840:ℝ)+(2/3:ℝ)/((4096:ℕ):ℝ)^2+481/166320) := by
    norm_num [y]
  calc
    (-523/840:ℝ) <
        (∫ x in (0:ℝ)..y, profile x) + ∫ x in y..1, profile x := by
      exact hbudget.trans_le (add_le_add htail hmargin)
    _ = ∫ x in (0:ℝ)..1, profile x := hsplit

end ProfileIntegralLowerBridge

theorem profile_integral_lower :
    (-523/840:ℝ) < ∫ x in (0:ℝ)..1, profile x := by
  exact ProfileIntegralLowerBridge.profile_integral_lower_actual

end
end Li2Unified.Stage0.HermitePreparation

#print axioms Li2Unified.Stage0.HermitePreparation.profile_integral_lower
#print axioms Li2Unified.Stage0.HermitePreparation.actual_binomGram

#print axioms Li2Unified.Stage0.HermitePreparation.actual_functional
#print axioms Li2Unified.Stage0.HermitePreparation.actual_binomGram

end


end
