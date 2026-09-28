module
public import Li2Unified.Modular.Base.PadicValuationBridge

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem VG_of_padic_norm_pow_le (q : ℚ) (k : ℕ)
    (h : ‖(q : ℚ_[p])‖ ≤ ‖(p : ℚ_[p])‖ ^ k) :
    VG p q (k : ℚ) := by
  apply (VG_iff_padic_norm_le q (k : ℚ)).mpr
  simpa only [Rat.cast_natCast, Real.rpow_neg_eq_inv_rpow,
    Real.rpow_natCast, Padic.norm_p, inv_pow] using h

theorem VG_of_cube_padic_norm_bound (q : ℚ) (k : ℕ)
    (h : ‖(((p : ℚ)^3 * q : ℚ) : ℚ_[p])‖ ≤ ‖(p : ℚ_[p])‖^k) :
    VG p q ((k : ℚ)-3) := by
  by_cases hq : q = 0
  · exact Or.inl hq
  · right
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hs := (VG_of_padic_norm_pow_le ((p : ℚ)^3*q) k h).resolve_left
      (mul_ne_zero (pow_ne_zero 3 hpq) hq)
    have hpv : padicValRat p ((p : ℚ)^3) = (3 : ℤ) := by
      simp [padicValRat.pow, padicValRat.self hp.out.one_lt]
    rw [padicValRat.mul (pow_ne_zero 3 hpq) hq, hpv] at hs
    push_cast at hs
    linarith

theorem GV_of_cube_padic_norm_bound (F : ℚ[X]) (k : ℕ)
    (h : ∀ n, ‖(C ((p : ℚ_[p])^3) * F.map (Rat.castHom ℚ_[p])).coeff n‖ ≤
      ‖(p : ℚ_[p])‖^k) :
    GV p F ((k : ℚ)-3) := by
  intro n
  apply VG_of_cube_padic_norm_bound (F.coeff n) k
  simpa only [coeff_C_mul, coeff_map, Rat.coe_castHom, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_natCast] using h n

theorem GV.strict_coeff_of_margin {F : ℚ[X]} {w ε : ℚ}
    (h : GV p F (w+ε)) (hε : 0 < ε) (n : ℕ) :
    F.coeff n = 0 ∨ w < (padicValRat p (F.coeff n) : ℚ) := by
  rcases h n with hz | hv
  · exact Or.inl hz
  · exact Or.inr (lt_of_lt_of_le (by linarith : w < w+ε) hv)

end
end Li2

end
