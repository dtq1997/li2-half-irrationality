module
public import Li2Unified.Modular.Base.RationalBaseEvaluation
public import Li2Unified.Modular.Base.PrimeFieldPoleExtension

set_option backward.privateInPublic true

@[expose] public section

/-! The rational four-pole evaluations use the same actual prime-parameter
functional as the original local dissection, for every rational presentation. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem fieldPrimePoleU_rational (hp4 : 3 < p) (f : ℚ[X])
    (r : Fin 4 → ℚ) (Y : ℚ_[p]) :
    (fieldPrimePoleU hp4 (f.map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p])
      (fun j => (r j : ℚ_[p]))).eval Y =
    (rationalPoleU (primeParameter p) f r).eval₂ (Rat.castHom ℚ_[p]) Y := by
  change (C (fieldRestrictedU _ _) + ∑ j : Fin 4,
    C (r j : ℚ_[p]) * (primeUPole (by omega) j.val (by omega)).map
      (algebraMap ℤ_[p] ℚ_[p])).eval Y = _
  rw [fieldParameterU_polynomial]
  simp only [rationalPoleU, eval_add, eval_C, eval_finset_sum, eval_mul,
    eval_map, primeUPole_eval₂, eval₂_add, eval₂_C, eval₂_finset_sum,
    eval₂_mul, eval₂_sub, eval₂_X, Rat.coe_castHom, Rat.cast_mul, Rat.cast_pow, Rat.cast_inv, Rat.cast_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fieldPrimePoleV_rational (hp4 : 3 < p) (f : ℚ[X])
    (r : Fin 4 → ℚ) (Y : ℚ_[p]) :
    (fieldPrimePoleV hp4 (f.map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p])
      (fun j => (r j : ℚ_[p]))).eval Y =
    (rationalPoleV (primeParameter p) f r).eval₂ (Rat.castHom ℚ_[p]) Y := by
  change (C (fieldRestrictedV _ _) + ∑ j : Fin 4,
    C (r j : ℚ_[p]) * (primeVPole (by omega) j.val (by omega)).map
      (algebraMap ℤ_[p] ℚ_[p])).eval Y = _
  rw [fieldParameterV_polynomial]
  simp only [rationalPoleV, eval_add, eval_C, eval_finset_sum, eval_mul,
    eval_map, primeVPole_eval₂, eval₂_add, eval₂_C, eval₂_finset_sum,
    eval₂_mul, eval₂_sub, eval₂_X, Rat.coe_castHom, Rat.cast_mul, Rat.cast_pow, Rat.cast_inv, Rat.cast_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end Li2

end
