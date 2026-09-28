module
public import Li2Unified.Modular.Base.Valuation
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Int

set_option backward.privateInPublic true

@[expose] public section

/-! Transfer a constant p-adic congruence to any primitive integer normalization. -/
open Polynomial
namespace Li2
variable {p : ℕ} [hp : Fact p.Prime]

lemma primitive_exists_coeff_not_dvd (P : ℤ[X]) (hP : P.IsPrimitive) :
    ∃ k, ¬(p:ℤ) ∣ P.coeff k := by
  by_contra h
  push_neg at h
  have hu := hP (p:ℤ) ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr h)
  exact (Nat.prime_iff_prime_int.mp hp.out).not_unit hu

theorem primitive_constant_reduction_of_dvd (P : ℤ[X]) (hP : P.IsPrimitive)
    (hdiv : ∀ k, k ≠ 0 → (p:ℤ) ∣ P.coeff k) :
    ∃ c : ZMod p, c ≠ 0 ∧ P.map (Int.castRingHom (ZMod p)) = C c := by
  have h0 : ¬(p:ℤ) ∣ P.coeff 0 := by
    intro h0
    obtain ⟨k, hk⟩ := primitive_exists_coeff_not_dvd (p := p) P hP
    by_cases he : k = 0
    · exact hk (by simpa only [he] using h0)
    · exact hk (hdiv k he)
  refine ⟨(P.coeff 0 : ZMod p), ?_, ?_⟩
  · exact fun h => h0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  · ext k
    rw [coeff_map, coeff_C]
    by_cases hk : k = 0
    · subst k
      simp
    · rw [if_neg hk]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hdiv k hk)

theorem primitive_constant_reduction_of_strict_min (P : ℤ[X]) (hP : P.IsPrimitive)
    (hmin : ∀ k, k ≠ 0 → P.coeff k ≠ 0 →
      padicValInt p (P.coeff 0) < padicValInt p (P.coeff k)) :
    ∃ c : ZMod p, c ≠ 0 ∧ P.map (Int.castRingHom (ZMod p)) = C c := by
  apply primitive_constant_reduction_of_dvd P hP
  intro k hk
  by_cases hz : P.coeff k = 0
  · rw [hz]
    exact dvd_zero _
  · have hv : 1 ≤ padicValInt p (P.coeff k) := by have := hmin k hk hz; omega
    simpa only [pow_one] using (padicValInt_dvd_iff (p := p) 1 (P.coeff k)).mpr (Or.inr hv)

lemma unit_of_VG_sub {q c : ℚ} (hc : c ≠ 0) (hcval : padicValRat p c = 0)
    (h : VG p (q-c) 1) : q ≠ 0 ∧ padicValRat p q = 0 := by
  have hq : q ≠ 0 := by
    intro hq
    rw [hq, zero_sub] at h
    rcases h with he | he
    · exact hc (neg_eq_zero.mp he)
    · rw [padicValRat.neg, hcval] at he
      norm_num at he
  refine ⟨hq, ?_⟩
  by_cases he : q-c = 0
  · rw [sub_eq_zero.mp he]
    exact hcval
  have hv := h.resolve_left he
  have hv' : padicValRat p c < padicValRat p (q-c) := by
    rw [hcval]
    have : (0:ℚ) < (padicValRat p (q-c):ℚ) := by linarith
    exact_mod_cast this
  have heq : c+(q-c) = q := by ring
  have hsum : c+(q-c) ≠ 0 := by rwa [heq]
  have ht := padicValRat.add_eq_of_lt (p := p) hsum hc he hv'
  rw [heq] at ht
  exact ht.trans hcval

theorem primitive_constant_reduction_of_scaled_congruence
    (P : ℤ[X]) (hP : P.IsPrimitive) (F : ℚ[X]) (d s c : ℚ)
    (hd : d ≠ 0) (hs : s ≠ 0)
    (hprop : P.map (Int.castRingHom ℚ) = C d * F)
    (hc : c ≠ 0) (hcval : padicValRat p c = 0)
    (hcong : GV p (C s * F - C c) 1) :
    ∃ cbar : ZMod p, cbar ≠ 0 ∧ P.map (Int.castRingHom (ZMod p)) = C cbar := by
  have hcoeff (k : ℕ) : (P.coeff k : ℚ) = d * F.coeff k := by
    have h := congrArg (fun f : ℚ[X] => f.coeff k) hprop
    simpa only [coeff_map, coeff_C_mul] using h
  have hzero : VG p (s * F.coeff 0 - c) 1 := by
    simpa only [coeff_sub, coeff_C_mul, coeff_C_zero] using hcong 0
  obtain ⟨hz, hvz⟩ := unit_of_VG_sub hc hcval hzero
  have hF0 : F.coeff 0 ≠ 0 := fun h => hz (by rw [h, mul_zero])
  have hv0 := padicValRat.mul (p := p) hs hF0
  have hvP0 := padicValRat.mul (p := p) hd hF0
  rw [← hcoeff 0, padicValRat.of_int] at hvP0
  apply primitive_constant_reduction_of_strict_min P hP
  intro k hk hPk
  have hFk : F.coeff k ≠ 0 := by
    intro he
    have hh := hcoeff k
    rw [he, mul_zero] at hh
    exact hPk (by exact_mod_cast hh)
  have hvk : VG p (s * F.coeff k) 1 := by
    simpa only [coeff_sub, coeff_C_mul, coeff_C_ne_zero hk, sub_zero] using hcong k
  have hb := hvk.resolve_left (mul_ne_zero hs hFk)
  have hvk' := padicValRat.mul (p := p) hs hFk
  have hvPk := padicValRat.mul (p := p) hd hFk
  rw [← hcoeff k, padicValRat.of_int] at hvPk
  have hstrict : (padicValRat p (s * F.coeff 0):ℚ) < padicValRat p (s * F.coeff k) := by
    rw [hvz]
    norm_num only [Int.cast_zero]
    linarith
  have hstrict' : padicValRat p (s * F.coeff 0) < padicValRat p (s * F.coeff k) := by
    exact_mod_cast hstrict
  rw [hv0, hvk'] at hstrict'
  omega

end Li2

end
