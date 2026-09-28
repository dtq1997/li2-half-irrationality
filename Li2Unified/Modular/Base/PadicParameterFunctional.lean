module
public import Li2Unified.Modular.Base.ParameterMoments
public import Li2Unified.Modular.Base.RestrictedFunctional

set_option backward.privateInPublic true

@[expose] public section

/-! Connect the rational parameter moments to a convergent integral p-adic functional. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem padic_norm_le_one_of_VG {q : ℚ} (hq : VG p q 0) : ‖(q : ℚ_[p])‖ ≤ 1 := by
  by_cases hzero : q = 0
  · simp [hzero]
  have hv : (0:ℤ) ≤ padicValRat p q := by
    exact_mod_cast hq.resolve_left hzero
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hzero]
  exact_mod_cast (zpow_le_one_of_nonpos₀ (show (1:ℚ) ≤ p by exact_mod_cast hp.out.one_le)
    (neg_nonpos.mpr hv))

def integralRational (q : ℚ) (hq : VG p q 0) : ℤ_[p] :=
  ⟨(q:ℚ_[p]), padic_norm_le_one_of_VG hq⟩

def integralParameterMoment (z : ℚ) (hz : VG p (z/(1-z)) 0) (k : ℕ) : ℤ_[p] :=
  integralRational (parameterMoment z k) (parameterMoment_VG p z hz k)

def padicParameterG (z : ℚ) (hz : VG p (z/(1-z)) 0) (f : PowerSeries ℤ_[p]) : ℤ_[p] :=
  restrictedMoment (integralParameterMoment z hz) f

end
end Li2

end
