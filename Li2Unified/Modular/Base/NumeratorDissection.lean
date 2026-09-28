module
public import Li2Unified.Modular.Base.PrimePoleDissection
public import Li2Unified.Modular.Base.ParameterDifferentialDissection

set_option backward.privateInPublic true

@[expose] public section

/-! Connect the completed polynomial and simple-pole dissections to the
literal numeratorFunctional. Local values here use its actual partial fractions;
identification with bounded four-pole representations is a separate bridge. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def numeratorPulledValue (hp2 : p ≠ 2) (hp3 : p ≠ 3) (Y : ℚ_[p])
    (m : ℕ) (F : ℚ[X]) (a : Fin p) : ℚ_[p] :=
  (parameterU (primeParameter p) ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ))):ℚ_[p])-
    (a.val:ℚ_[p])/(p:ℚ_[p])*
      (parameterV (primeParameter p) ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ))):ℚ_[p])+
    ∑ j ∈ Finset.Icc 1 m,
      ((F.eval (-(j:ℚ)) / ∏ l ∈ (Finset.Icc 1 m).erase j, ((l:ℚ)-(j:ℚ))):ℚ_[p])*
        pulledSimplePoleContribution hp2 hp3 Y j a.val

theorem numeratorFunctional_dissection_eval (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (m : ℕ) (F : ℚ[X]) (x : ℚ_[p]) :
    (numeratorFunctional m F).eval₂ (Rat.castHom ℚ_[p]) x =
      ∑ a : Fin p, (-2:ℚ_[p])^a.val*
        numeratorPulledValue hp2 hp3 ((p:ℚ_[p])^2*(x-(primeEta hp2 hp3:ℚ_[p]))) m F a := by
  have hpoly := congrArg (fun q : ℚ => (q:ℚ_[p]))
    (original_polynomial_dissection p hp.out.pos (F /ₘ D m))
  push_cast at hpoly
  unfold numeratorFunctional
  simp only [eval₂_add, eval₂_C, eval₂_finset_sum, eval₂_mul, eval₂_sub, eval₂_X, Rat.coe_castHom,
    Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat]
  rw [hpoly]
  unfold numeratorPulledValue
  simp only [mul_add, Finset.sum_add_distrib, primeParameter]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hs := prime_simple_pole_dissection_uv hp2 hp3 x j
  rw [← Fin.sum_univ_eq_sum_range] at hs
  have hinv : (-1/2:ℚ_[p])⁻¹ = -2 := by norm_num
  rw [hinv, parameterTau_negHalf] at hs
  rw [← hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  push_cast
  ring

end
end Li2

end
