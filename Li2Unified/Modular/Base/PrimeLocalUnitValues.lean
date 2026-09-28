module
public import Li2Unified.Modular.Base.PrimeLocalUnitField

set_option backward.privateInPublic true

@[expose] public section

/-! Four explicit reductions of the actual top-degree product's local units. -/
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeFieldUnitTail_zero (hp4 : 3 < p) :
    primeFieldUnitTail (p := p) ⟨0,by omega⟩ = -6 := by
  simp only [primeFieldUnitTail,Fin.val_mk]
  rw [primeFieldUnitFactor_tail hp4 0 3 (by omega) (by omega),
    primeFieldUnitFactor_tail hp4 0 2 (by omega) (by omega),
    primeFieldUnitFactor_tail hp4 0 1 (by omega) (by omega),
    if_pos (by omega),if_pos (by omega),if_pos (by omega)]
  norm_num

lemma primeFieldUnitTail_high (hp4 : 3 < p) (ell : ℕ) (hl : 1 ≤ ell) (hl3 : ell ≤ 3) :
    primeFieldUnitTail (p := p) ⟨p-ell,by omega⟩ = 3*(ell:ZMod p)^2-12*(ell:ZMod p)+11 := by
  simp only [primeFieldUnitTail,Fin.val_mk]
  rw [primeFieldUnitFactor_tail_residue hp4 ell 3 hl hl3 (by omega) (by omega),
    primeFieldUnitFactor_tail_residue hp4 ell 2 hl hl3 (by omega) (by omega),
    primeFieldUnitFactor_tail_residue hp4 ell 1 hl hl3 (by omega) (by omega)]
  rcases (show ell=1 ∨ ell=2 ∨ ell=3 by omega) with rfl | rfl | rfl <;> norm_num

theorem primeLocalUnit_zero_value (hp4 : 3 < p) :
    (primeLocalUnit p ⟨0,by omega⟩:ZMod p) = -1/6 := by
  have h := primeLocalUnit_mul_tail hp4 (⟨0,by omega⟩:Fin p)
  rw [primeFieldUnitTail_zero hp4] at h
  have h6 : (6:ZMod p) ≠ 0 := by
    convert mul_ne_zero (primeField_two_ne_zero hp4) (primeField_three_ne_zero hp4) using 1 <;> ring
  apply (eq_div_iff h6).mpr
  linear_combination -h

theorem primeLocalUnit_high_one_value (hp4 : 3 < p) :
    (primeLocalUnit p ⟨p-1,by omega⟩:ZMod p) = 1/2 := by
  have h := primeLocalUnit_mul_tail hp4 (⟨p-1,by omega⟩:Fin p)
  rw [primeFieldUnitTail_high hp4 1 (by omega) (by omega)] at h
  norm_num at h
  exact (eq_div_iff (primeField_two_ne_zero hp4)).mpr h

theorem primeLocalUnit_high_two_value (hp4 : 3 < p) :
    (primeLocalUnit p ⟨p-2,by omega⟩:ZMod p) = -1 := by
  have h := primeLocalUnit_mul_tail hp4 (⟨p-2,by omega⟩:Fin p)
  rw [primeFieldUnitTail_high hp4 2 (by omega) (by omega)] at h
  norm_num at h
  linear_combination -h

theorem primeLocalUnit_high_three_value (hp4 : 3 < p) :
    (primeLocalUnit p ⟨p-3,by omega⟩:ZMod p) = 1/2 := by
  have h := primeLocalUnit_mul_tail hp4 (⟨p-3,by omega⟩:Fin p)
  rw [primeFieldUnitTail_high hp4 3 (by omega) (by omega)] at h
  norm_num at h
  exact (eq_div_iff (primeField_two_ne_zero hp4)).mpr h

end
end Li2

end
