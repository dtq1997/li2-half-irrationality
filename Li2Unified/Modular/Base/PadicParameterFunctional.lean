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

theorem padicParameterG_summable (z : ℚ) (hz : VG p (z/(1-z)) 0)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f) :
    Summable (fun n => PowerSeries.coeff n f * integralParameterMoment z hz n) :=
  restrictedMoment_summable _ _ hf

theorem padicParameterG_polynomial (z : ℚ) (hz : VG p (z/(1-z)) 0) (P : ℤ[X]) :
    (padicParameterG z hz ((P.map (Int.castRingHom ℤ_[p])) : PowerSeries ℤ_[p]) : ℚ_[p]) =
      (parameterG z (P.map (Int.castRingHom ℚ)) : ℚ_[p]) := by
  unfold padicParameterG
  rw [restrictedMoment_polynomial]
  unfold parameterG Polynomial.sum
  rw [support_map_of_injective P (show Function.Injective (Int.castRingHom ℤ_[p]) from Int.cast_injective),
    support_map_of_injective P (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)]
  rw [PadicInt.coe_sum, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [coeff_map, Int.coe_castRingHom, PadicInt.coe_mul, PadicInt.coe_intCast,
    integralParameterMoment, integralRational, Rat.cast_mul, Rat.cast_intCast]

end
end Li2

end
