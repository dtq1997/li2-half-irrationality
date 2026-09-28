module
public import Li2Unified.Modular.Base.OriginalRealSeries
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.FieldSimp

set_option backward.privateInPublic true

@[expose] public section

open Polynomial Filter Topology Set
open scoped BigOperators
namespace Li2
noncomputable section

def originalRealQuotient (m : ℕ) (F : ℚ[X]) (x : ℝ) : ℝ :=
  F.eval₂ (Rat.castHom ℝ) x / (D m).eval₂ (Rat.castHom ℝ) x

lemma D_eval₂_pos (m : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (D m).eval₂ (Rat.castHom ℝ) x := by
  simp only [D, eval₂_finset_prod, eval₂_add, eval₂_X, eval₂_C,
    Rat.coe_castHom, Rat.cast_natCast]
  apply Finset.prod_pos
  intro j _
  exact add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg j)

theorem originalRealQuotient_partial_fractions (m : ℕ) (F : ℚ[X])
    {x : ℝ} (hx : 0 < x) :
    originalRealQuotient m F x = (F /ₘ D m).eval₂ (Rat.castHom ℝ) x +
      ∑ j ∈ Finset.Icc 1 m, (originalResidue m F j:ℝ)/(x+(j:ℝ)) := by
  have hd : (D m).eval₂ (Rat.castHom ℝ) x ≠ 0 := ne_of_gt (D_eval₂_pos m hx)
  have he := congrArg (fun P : ℚ[X] => P.eval₂ (Rat.castHom ℝ) x)
    (original_partial_fractions m F)
  simp only [eval₂_add, eval₂_mul, eval₂_finset_sum, eval₂_finset_prod,
    eval₂_X, eval₂_C, Rat.coe_castHom, Rat.cast_natCast] at he
  have hc (j : ℕ) (hj : j ∈ Finset.Icc 1 m) :
      (D m).eval₂ (Rat.castHom ℝ) x =
        (x+(j:ℝ))*∏ l ∈ (Finset.Icc 1 m).erase j, (x+(l:ℝ)) := by
    simp only [D, eval₂_finset_prod, eval₂_add, eval₂_X, eval₂_C,
      Rat.coe_castHom, Rat.cast_natCast]
    exact (Finset.mul_prod_erase _ _ hj).symm
  unfold originalRealQuotient
  apply (div_eq_iff hd).mpr
  rw [he, add_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjx : x+(j:ℝ) ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg j))
  rw [hc j hj]
  field_simp [hjx]

lemma hasDerivAt_real_pole_numerator (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y/(y+(j:ℝ))) ((j:ℝ)/(x+(j:ℝ))^2) x := by
  have hjx : x+(j:ℝ) ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg j))
  convert (hasDerivAt_id x).fun_div ((hasDerivAt_id x).add_const (j:ℝ)) hjx using 1 <;>
    dsimp <;> ring

theorem originalRealQuotient_hasDerivAt (m : ℕ) (F : ℚ[X])
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y*originalRealQuotient m F y)
      (originalRealDerivativeExpansion m F x) x := by
  let qR : ℝ[X] := ((F /ₘ D m).map (Rat.castHom ℝ))*X
  have hp : HasDerivAt (fun y : ℝ => qR.eval y)
      (polynomialIntegrand (F /ₘ D m) x) x := by
    simpa only [qR, polynomialIntegrand_derivative] using qR.hasDerivAt x
  have hs : HasDerivAt
      (fun y : ℝ => ∑ j ∈ Finset.Icc 1 m,
        (originalResidue m F j:ℝ)*(y/(y+(j:ℝ))))
      (∑ j ∈ Finset.Icc 1 m,
        (originalResidue m F j:ℝ)*(j:ℝ)/(x+(j:ℝ))^2) x := by
    apply HasDerivAt.fun_sum
    intro j _
    simpa only [mul_div_assoc] using
      (hasDerivAt_real_pole_numerator j hx).const_mul (originalResidue m F j:ℝ)
  change HasDerivAt _ (polynomialIntegrand (F /ₘ D m) x + _) x
  apply (hp.add hs).congr_of_eventuallyEq
  have hy : ∀ᶠ y : ℝ in 𝓝 x, 0 < y := isOpen_Ioi.mem_nhds hx
  filter_upwards [hy] with y hy
  have hq : qR.eval y = y*(F /ₘ D m).eval₂ (Rat.castHom ℝ) y := by
    dsimp only [qR]
    rw [eval_mul, eval_X, ← eval₂_eq_eval_map]
    ring
  dsimp only [Pi.add_apply]
  rw [hq, originalRealQuotient_partial_fractions m F hy, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem numeratorFunctional_real_derivative_series (m : ℕ) (F : ℚ[X]) :
    (numeratorFunctional m F).eval₂ (Rat.castHom ℝ) li2NegHalf =
      ∑' k : ℕ, (-1/2:ℝ)^(k+1) *
        deriv (fun x : ℝ => x*originalRealQuotient m F x) ((k:ℝ)+1) := by
  rw [numeratorFunctional_real_series]
  apply tsum_congr
  intro k
  rw [(originalRealQuotient_hasDerivAt m F (x := (k:ℝ)+1) (by positivity)).deriv]

theorem summable_originalRealQuotient_derivative (m : ℕ) (F : ℚ[X]) :
    Summable (fun k : ℕ => (-1/2:ℝ)^(k+1) *
      deriv (fun x : ℝ => x*originalRealQuotient m F x) ((k:ℝ)+1)) := by
  apply (summable_originalRealDerivativeExpansion m F).congr
  intro k
  rw [(originalRealQuotient_hasDerivAt m F (x := (k:ℝ)+1) (by positivity)).deriv]

end
end Li2

end
