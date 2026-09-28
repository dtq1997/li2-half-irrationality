module
public import Li2Unified.Modular.Base.ParameterPolynomialSeries
public import Mathlib.Data.Fin.Rev
public import Mathlib.Logic.Equiv.Fin.Basic

set_option backward.privateInPublic true

@[expose] public section

/-! All-polynomial residue-class dissection. The real geometric series is
absolutely convergent; the resulting identity is an equality of rationals. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def dissectionIndex (q : ℕ) (a : Fin q) (k : ℕ) : ℕ := k*q+(q-1-a.val)

def dissectionEquiv (q : ℕ) [NeZero q] : (Fin q × ℕ) ≃ ℕ :=
  (Equiv.prodComm (Fin q) ℕ).trans
    ((Equiv.prodCongr (Equiv.refl ℕ) Fin.revPerm).trans (Nat.divModEquiv q).symm)

lemma dissectionEquiv_apply (q : ℕ) [NeZero q] (a : Fin q) (k : ℕ) :
    dissectionEquiv q (a,k) = dissectionIndex q a k := by
  simp [dissectionEquiv, dissectionIndex, Fin.revPerm, Nat.sub_sub, Nat.add_comm]

theorem tsum_dissection (q : ℕ) [NeZero q] (f : ℕ → ℝ) (hf : Summable f) :
    ∑' n, f n = ∑ a : Fin q, ∑' k : ℕ, f (dissectionIndex q a k) := by
  have hs : Summable (fun ak : Fin q × ℕ => f (dissectionEquiv q ak)) :=
    (dissectionEquiv q).summable_iff.mpr hf
  rw [← (dissectionEquiv q).tsum_eq f, hs.tsum_prod, tsum_fintype]
  simp only [dissectionEquiv_apply]

lemma dissectionIndex_add (q : ℕ) (a : Fin q) (k : ℕ) :
    dissectionIndex q a k+1+a.val = q*(k+1) := by
  unfold dissectionIndex
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm q k]
  omega

lemma rational_polynomial_dissection_term (z : ℚ) (hz : z ≠ 0)
    (q : ℕ) (a : Fin q) (k : ℕ) (P : ℚ[X]) :
    z^(dissectionIndex q a k+1)*P.eval ((dissectionIndex q a k:ℚ)+1) =
      z⁻¹^a.val*((z^q)^(k+1)*(P.comp (C (q:ℚ)*X-C (a.val:ℚ))).eval ((k:ℚ)+1)) := by
  have he : (dissectionIndex q a k:ℚ)+1 = (q:ℚ)*((k:ℚ)+1)-(a.val:ℚ) := by
    have h := congrArg (fun n : ℕ => (n:ℚ)) (dissectionIndex_add q a k)
    push_cast at h
    linarith
  have hp : z^(dissectionIndex q a k+1)*z^a.val = (z^q)^(k+1) := by
    rw [← pow_add, dissectionIndex_add, pow_mul]
  rw [eval_comp, eval_sub, eval_mul, eval_C, eval_X, eval_C, he]
  have hpow : z^(dissectionIndex q a k+1) = z⁻¹^a.val*(z^q)^(k+1) := by
    rw [inv_pow, ← hp]
    field_simp
  rw [hpow]
  ring

theorem parameterG_dissection (z : ℚ) (hz : ‖(z:ℝ)‖ < 1) (hzne : z ≠ 0)
    (q : ℕ) (hq : 0 < q) (P : ℚ[X]) :
    parameterG z P = ∑ a : Fin q,
      z⁻¹^a.val*parameterG (z^q) (P.comp (C (q:ℚ)*X-C (a.val:ℚ))) := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hzq : ‖((z^q:ℚ):ℝ)‖ < 1 := by
    rw [Rat.cast_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hz (Nat.ne_of_gt hq)
  apply Rat.cast_injective (α := ℝ)
  rw [parameterG_cast_eq_series z hz P,
    tsum_dissection q _ (summable_parameterPolynomial z hz P)]
  push_cast
  apply Finset.sum_congr rfl
  intro a _
  rw [parameterG_cast_eq_series (z^q) hzq, ← tsum_mul_left]
  apply tsum_congr
  intro k
  exact_mod_cast rational_polynomial_dissection_term z hzne q a k P

end
end Li2

end
