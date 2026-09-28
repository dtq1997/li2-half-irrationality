module
public import Li2Unified.Modular.Base.PrimeLowRationalLeading
public import Li2Unified.Modular.Base.PrimeCrossValuation
public import Li2Unified.Modular.Base.PrimeBlockIndex

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem GV_of_square_padic_leading_bound (F : ℚ[X]) (r : ℚ) (k : ℕ)
    (h : ∀ n, ‖(C ((p:ℚ_[p])^2)*F.map (Rat.castHom ℚ_[p]) -
      C ((p:ℚ_[p])^k*(r:ℚ_[p]))).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(k+1)) :
    GV p (F-C ((p:ℚ)^((k:ℤ)-2)*r)) ((k:ℚ)-1) := by
  let E : ℚ[X] := C ((p:ℚ)^2)*F-C ((p:ℚ)^k*r)
  have hmap : E.map (Rat.castHom ℚ_[p]) =
      C ((p:ℚ_[p])^2)*F.map (Rat.castHom ℚ_[p]) -
        C ((p:ℚ_[p])^k*(r:ℚ_[p])) := by
    simp only [E,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
      Rat.coe_castHom,Rat.cast_pow,Rat.cast_natCast,Rat.cast_mul]
  have hE : GV p E ((k+1 : ℕ) : ℚ) := by
    intro n
    apply VG_of_padic_norm_pow_le _ (k+1)
    have hn := h n
    rw [← hmap] at hn
    simpa only [coeff_map,Rat.coe_castHom] using! hn
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp2 : (p:ℚ)^(-2:ℤ)*(p:ℚ)^2 = 1 := by
    simp only [zpow_neg,zpow_ofNat]
    exact inv_mul_cancel₀ (pow_ne_zero 2 hpq)
  have hpk : (p:ℚ)^(-2:ℤ)*(p:ℚ)^k = (p:ℚ)^((k:ℤ)-2) := by
    rw [zpow_sub₀ hpq]
    simp only [zpow_neg,zpow_ofNat,zpow_natCast,div_eq_mul_inv]
    ring
  have he : C ((p:ℚ)^(-2:ℤ))*E = F-C ((p:ℚ)^((k:ℤ)-2)*r) := by
    dsimp only [E]
    rw [mul_sub,← mul_assoc,← C_mul,hp2,C_1,one_mul,← C_mul]
    rw [← mul_assoc,hpk]
  have hh := GV.C_mul (VG.primePow (p := p) (-2)) hE
  rw [he] at hh
  exact hh.mono (by push_cast <;> linarith)

end
end Li2

end
