module
public import Li2Unified.Modular.Base.Family
public import Li2Unified.Modular.Base.Valuation

set_option backward.privateInPublic true

@[expose] public section

/-! Specific arithmetic of the negative-half moments. Every denominator is
supported at 3; a uniform elementary 3-adic bound is also proved. -/
open Polynomial
namespace Li2

lemma inv_three_VG (p : ℕ) [hp : Fact p.Prime] (hp3 : p ≠ 3) :
    VG p (3 : ℚ)⁻¹ 0 := by
  have hn : ¬p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp.out (by decide)).mp h)
  have hv : padicValRat p (3 : ℚ) = 0 := by
    change padicValRat p ((3 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hn]
    rfl
  right
  rw [padicValRat.inv, hv]
  norm_num

theorem moment_VG_of_ne_three (p : ℕ) [Fact p.Prime] (hp3 : p ≠ 3) (k : ℕ) :
    VG p (moment k) 0 := by
  have h3 := inv_three_VG p hp3
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simpa [moment, div_eq_mul_inv] using h3.neg
    | succ k =>
      rw [moment]
      have hs : VG p (∑ j : Fin (k+1), (Nat.choose (k+1) j.val : ℚ) * moment j.val) 0 := by
        apply VG.sum
        intro j _
        simpa using (VG.natCast (p := p) (Nat.choose (k+1) j.val)).mul (ih j.val j.isLt)
      simpa [div_eq_mul_inv] using ((VG.one (p := p)).add hs).neg.mul h3

theorem moment_VG_three (k : ℕ) : VG 3 (moment k) (-((k:ℚ)+1)) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h3 : VG 3 (3 : ℚ)⁻¹ (-1) := by
    right
    have hv : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (p := 3) (by decide)
    rw [padicValRat.inv, hv]
    norm_num
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simpa [moment, div_eq_mul_inv] using h3.neg
    | succ k =>
      rw [moment]
      have hs : VG 3 (∑ j : Fin (k+1), (Nat.choose (k+1) j.val : ℚ) * moment j.val)
          (-((k:ℚ)+1)) := by
        apply VG.sum
        intro j _
        have hj : (j.val : ℚ) ≤ k := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
        have ht := (VG.natCast (p := 3) (Nat.choose (k+1) j.val)).mul (ih j.val j.isLt)
        exact ht.mono (by linarith)
      have h1 : VG 3 1 (-((k:ℚ)+1)) :=
        (VG.one (p := 3)).mono (by have := (Nat.cast_nonneg k : (0:ℚ) ≤ k); linarith)
      have ht := (h1.add hs).neg.mul h3
      have hb : -((k:ℚ)+1) + (-1) = -(((k+1:ℕ):ℚ)+1) := by push_cast; ring
      rw [hb] at ht
      simpa only [div_eq_mul_inv] using ht

theorem polynomialMoment_VG_of_ne_three (p : ℕ) [Fact p.Prime] (hp3 : p ≠ 3)
    (f : ℚ[X]) (hf : GV p f 0) : VG p (polynomialMoment f) 0 := by
  unfold polynomialMoment Polynomial.sum
  apply VG.sum
  intro k _
  simpa using ((hf k).mul (VG.natCast (p := p) (k+1))).mul (moment_VG_of_ne_three p hp3 k)

end Li2

end
