module
public import Li2Unified.Modular.Base.PrimeTopEntry
public import Li2Unified.Modular.Base.PrimeEdgeNormValues

set_option backward.privateInPublic true

@[expose] public section

/-! Exactly four discs support the top self-pairing at its leading order. -/
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem primeTopLeadingSum_four (hp4 : 3 < p) :
    primeTopLeadingSum (p := p) =
      primeTopDiscLeading (p := p) ⟨0,by omega⟩ +
      (-2:ℚ_[p])^(p-1)*primeTopDiscLeading (p := p) ⟨p-1,by omega⟩ +
      (-2:ℚ_[p])^(p-2)*primeTopDiscLeading (p := p) ⟨p-2,by omega⟩ +
      (-2:ℚ_[p])^(p-3)*primeTopDiscLeading (p := p) ⟨p-3,by omega⟩ := by
  classical
  let a0 : Fin p := ⟨0,by omega⟩
  let a1 : Fin p := ⟨p-1,by omega⟩
  let a2 : Fin p := ⟨p-2,by omega⟩
  let a3 : Fin p := ⟨p-3,by omega⟩
  let s : Finset (Fin p) := {a0,a1,a2,a3}
  let F : Fin p → ℚ_[p] := fun a => (-2:ℚ_[p])^a.val*primeTopDiscLeading a
  have he : (∑ a : Fin p,F a) = ∑ a ∈ s,F a := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro a _ ha
    have hn : ¬ (a.val=0 ∨ a.val=p-1 ∨ a.val=p-2 ∨ a.val=p-3) := by
      simpa only [s,a0,a1,a2,a3,Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff] using ha
    have hz : a.val ≠ 0 := by omega
    have hl : a.val ≤ p-4 := by have := a.isLt; omega
    simp only [F,primeTopDiscLeading,if_neg hz,if_pos hl,mul_zero]
  have h01 : a0 ≠ a1 := by apply Fin.ne_of_val_ne; dsimp [a0,a1]; omega
  have h02 : a0 ≠ a2 := by apply Fin.ne_of_val_ne; dsimp [a0,a2]; omega
  have h03 : a0 ≠ a3 := by apply Fin.ne_of_val_ne; dsimp [a0,a3]; omega
  have h12 : a1 ≠ a2 := by apply Fin.ne_of_val_ne; dsimp [a1,a2]; omega
  have h13 : a1 ≠ a3 := by apply Fin.ne_of_val_ne; dsimp [a1,a3]; omega
  have h23 : a2 ≠ a3 := by apply Fin.ne_of_val_ne; dsimp [a2,a3]; omega
  change (∑ a : Fin p,F a) = _
  rw [he]
  dsimp only [s]
  rw [Finset.sum_insert (by simp [h01,h02,h03]),
    Finset.sum_insert (by simp [h12,h13]),
    Finset.sum_insert (by simp [h23]),Finset.sum_singleton]
  simp only [F,a0,a1,a2,a3,Fin.val_mk,pow_zero,one_mul]
  ring

theorem primeTopLeadingSum_weighted (hp4 : 3 < p) :
    primeTopLeadingSum (p := p) =
      (primeLocalUnit p ⟨0,by omega⟩:ℚ_[p])^2*
        (primeDiscUnitConstant (p := p) 0 (by omega):ℚ_[p])*(-17773/36) +
      ((primeHighDiscWeight (p := p) ⟨p-1,by omega⟩:ℚ_[p])*(primeLocalUnit p ⟨p-1,by omega⟩:ℚ_[p])^2 +
       (primeHighDiscWeight (p := p) ⟨p-2,by omega⟩:ℚ_[p])*(primeLocalUnit p ⟨p-2,by omega⟩:ℚ_[p])^2 +
       (primeHighDiscWeight (p := p) ⟨p-3,by omega⟩:ℚ_[p])*(primeLocalUnit p ⟨p-3,by omega⟩:ℚ_[p])^2)*(266/9) := by
  rw [primeTopLeadingSum_four hp4]
  simp only [primeTopDiscLeading,Fin.val_mk,ite_true,
    if_neg (by omega : p-1 ≠ 0),if_neg (by omega : p-2 ≠ 0),if_neg (by omega : p-3 ≠ 0),
    if_neg (by omega : ¬ p-1 ≤ p-4),if_neg (by omega : ¬ p-2 ≤ p-4),if_neg (by omega : ¬ p-3 ≤ p-4),
    primeHighDiscWeight,PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast,
    Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat]
  have htwo : ((2:ℤ_[p]):ℚ_[p]) = 2 := rfl
  simp only [htwo]
  ring

end
end Li2

end
