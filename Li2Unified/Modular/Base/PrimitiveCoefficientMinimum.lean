module
public import Li2Unified.Modular.Base.PrimitiveBinomialNormalization

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section

theorem primitive_scale_coeff_valuation_minimum (p : ℕ) [Fact p.Prime]
    (T : ℤ[X]) (hT : T.IsPrimitive) (F : ℚ[X]) (s : ℚ) (hs : s ≠ 0)
    (hprop : T.map (algebraMap ℤ ℚ) = C s * F) :
    ∃ k, F.coeff k ≠ 0 ∧ padicValRat p (F.coeff k) = -padicValRat p s ∧
      ∀ j, F.coeff j ≠ 0 → padicValRat p (F.coeff k) ≤ padicValRat p (F.coeff j) := by
  have hcoeff (k : ℕ) : (T.coeff k : ℚ) = s * F.coeff k := by
    have h := congrArg (fun f : ℚ[X] => f.coeff k) hprop
    simpa only [coeff_map, coeff_C_mul] using! h
  obtain ⟨k, hk⟩ := primitive_exists_coeff_not_dvd (p := p) T hT
  have hkF : F.coeff k ≠ 0 := by
    intro hz
    have hTq : (T.coeff k : ℚ) = 0 := by rw [hcoeff k, hz, mul_zero]
    have hTz : T.coeff k = 0 := by exact_mod_cast hTq
    exact hk (by rw [hTz]; exact dvd_zero _)
  have hkT : padicValRat p (T.coeff k : ℚ) = 0 := by
    simp only [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hk, Nat.cast_zero]
  have hkval := padicValRat.mul (p := p) hs hkF
  rw [← hcoeff k, hkT] at hkval
  have hke : padicValRat p (F.coeff k) = -padicValRat p s := by omega
  refine ⟨k, hkF, hke, ?_⟩
  intro j hj
  have hjnonneg : 0 ≤ padicValRat p (T.coeff j : ℚ) := by
    rw [padicValRat.of_int]
    exact Int.natCast_nonneg _
  rw [hcoeff j, padicValRat.mul hs hj] at hjnonneg
  omega

theorem Qtilde_coeff_valuation_minimum (p : ℕ) [Fact p.Prime] {n : ℕ}
    (hn : Qtilde n ≠ 0) :
    ∃ k, (Qtilde n).coeff k ≠ 0 ∧
      padicValRat p ((Qtilde n).coeff k) = -padicValRat p (dtilde n) ∧
      ∀ j, (Qtilde n).coeff j ≠ 0 →
        padicValRat p ((Qtilde n).coeff k) ≤ padicValRat p ((Qtilde n).coeff j) :=
  primitive_scale_coeff_valuation_minimum p (P n) (P_isPrimitive_of_Qtilde_ne_zero n hn)
    (Qtilde n) (dtilde n) (dtilde_ne_zero n) (P_eq_dtilde_Qtilde n)

theorem dtilde_padicVal_le_neg_GV (p : ℕ) [Fact p.Prime] {n : ℕ}
    (hn : Qtilde n ≠ 0) {r : ℚ} (hbound : GV p (Qtilde n) r) :
    (padicValRat p (dtilde n) : ℚ) ≤ -r := by
  obtain ⟨k, hk, hval, _⟩ := Qtilde_coeff_valuation_minimum p hn
  have h := (hbound k).resolve_left hk
  rw [hval, Int.cast_neg] at h
  linarith

end
end Li2

end
