module
public import Li2Unified.Modular.Base.Valuation
public import Mathlib.Algebra.Polynomial.Div

set_option backward.privateInPublic true

@[expose] public section

/- Adapted from Apery/Arith/IntPoly.lean in mo271/Zeta5 by Moritz Firsching (https://github.com/mo271/Zeta5, commit f19a1960609f7d38e7b63fd2acb05e6f60a7b741), Apache-2.0; see licenses/LICENSE-Zeta5.txt. -/

/-!
# `p`-integral polynomials

`GV p F 0` means that `F ∈ ℚ[X]` has `p`-integral coefficients. We show closure under powers,
composition and evaluation, and division by `X - a` (for `p`-integral roots `a`).
-/

open Finset Polynomial

namespace Li2

variable {p : ℕ} [hp : Fact p.Prime]

lemma GV.pow {F : ℚ[X]} {r : ℚ} (h : GV p F r) (n : ℕ) : GV p (F ^ n) (n * r) := by
  induction n with
  | zero => simpa using GV.C (p := p) (VG.one (p := p))
  | succ n ih => rw [pow_succ]; convert ih.mul h using 1; push_cast; ring

lemma GV.comp {F G : ℚ[X]} (hF : GV p F 0) (hG : GV p G 0) : GV p (F.comp G) 0 := by
  rw [comp_eq_sum_left, Polynomial.sum]
  refine GV.sum _ fun n _ => ?_
  have := GV.C_mul (hF n) (hG.pow n)
  simpa using this

lemma VG.eval {F : ℚ[X]} {z : ℚ} (hF : GV p F 0) (hz : VG p z 0) : VG p (F.eval z) 0 := by
  rw [eval_eq_sum, Polynomial.sum]
  refine VG.sum _ fun n _ => ?_
  have := (hF n).mul (hz.pow n)
  simpa using this

lemma GV.divByMonic_X_sub_C {F : ℚ[X]} {a : ℚ} (hF : GV p F 0) (ha : VG p a 0) :
    GV p (F /ₘ (Polynomial.X - Polynomial.C a)) 0 := fun n => by
  rw [coeff_divByMonic_X_sub_C]
  refine VG.sum _ fun i _ => ?_
  have := (ha.pow (i - (n + 1))).mul (hF i)
  simpa using this

end Li2

end
