module
public import Li2Unified.Modular.Base.PrimeFieldLeadingConstants

set_option backward.privateInPublic true

@[expose] public section

/-! The three high classes, with the original derivative polynomial
((t-1)(t-2)(t-3))' = 3t^2-12t+11 written explicitly. -/
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem primeFieldLeadingUnit_tail_formula (hp4 : 3 < p) (a : ℕ) (ha : a < p) :
    primeFieldLeadingUnit (p := p) a =
      -(primeFieldUnitProduct a (p-1))^2 * primeFieldUnitFactor a (p-3) *
        primeFieldUnitFactor a (p-2) * primeFieldUnitFactor a (p-1) := by
  unfold primeFieldLeadingUnit
  apply (div_eq_iff (primeFieldUnitProduct_ne_zero a _ ha)).mpr
  rw [primeFieldUnitProduct_denominator hp4 a ha,
    primeFieldUnitProduct_last_three hp4 a]
  ring

lemma primeFieldUnitFactor_tail_residue (hp4 : 3 < p) (ell s : ℕ)
    (hl : 1 ≤ ell) (hl3 : ell ≤ 3) (hs : 1 ≤ s) (hs3 : s ≤ 3) :
    primeFieldUnitFactor (p := p) (p-ell) (p-s) =
      if s ≠ ell then (ell:ZMod p)-(s:ZMod p) else 1 := by
  rw [primeFieldUnitFactor_tail hp4 (p-ell) s hs hs3,
    primeField_cast_sub (p := p) ell (by omega)]
  by_cases he : s = ell
  · subst s
    simp
  · rw [if_pos he, if_pos (by omega)]
    ring

theorem primeFieldLeadingUnit_high (hp4 : 3 < p) (ell : ℕ)
    (hl : 1 ≤ ell) (hl3 : ell ≤ 3) :
    primeFieldLeadingUnit (p := p) (p-ell) =
      -(3*(ell:ZMod p)^2-12*(ell:ZMod p)+11)/(ell:ZMod p)^2 := by
  rw [primeFieldLeadingUnit_tail_formula hp4 (p-ell) (by omega),
    primeFieldUnitProduct_numerator_nonzero (p-ell) (by omega) (by omega),
    primeFieldUnitFactor_tail_residue hp4 ell 3 hl hl3 (by omega) (by omega),
    primeFieldUnitFactor_tail_residue hp4 ell 2 hl hl3 (by omega) (by omega),
    primeFieldUnitFactor_tail_residue hp4 ell 1 hl hl3 (by omega) (by omega),
    primeField_cast_sub (p := p) ell (by omega)]
  rcases (show ell = 1 ∨ ell = 2 ∨ ell = 3 by omega) with rfl | rfl | rfl <;>
    norm_num [div_eq_mul_inv, ← inv_pow] <;> norm_num [inv_pow] <;> ring

end
end Li2

end
