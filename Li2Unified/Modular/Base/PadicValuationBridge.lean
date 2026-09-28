module
public import Li2Unified.Modular.Base.PadicParameterFunctional
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.privateInPublic true

@[expose] public section

/-! Convert a proved p-adic norm estimate back to the rational valuation
predicate used by the determinant congruence lemmas, including half weights. -/
namespace Li2
variable {p : ℕ} [hp : Fact p.Prime]

theorem VG_iff_padic_norm_le (q r : ℚ) :
    VG p q r ↔ ‖(q:ℚ_[p])‖ ≤ (p:ℝ)^(-(r:ℝ)) := by
  by_cases hq : q = 0
  · subst q
    constructor
    · intro _
      simp only [Rat.cast_zero, norm_zero]
      positivity
    · intro _
      exact VG.zero r
  · simp only [VG, hq, false_or]
    rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hq]
    simp only [Rat.cast_zpow, Rat.cast_natCast]
    rw [← Real.rpow_intCast, Int.cast_neg,
      Real.rpow_le_rpow_left_iff (by exact_mod_cast hp.out.one_lt), neg_le_neg_iff]
    norm_cast

end Li2

end
