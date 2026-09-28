module
public import Li2Unified.Modular.Base.DissectedSquare
public import Li2Unified.Modular.Base.PoleWindowReversal
public import Mathlib.Data.Fin.Rev

set_option backward.privateInPublic true

@[expose] public section

/-! The actual integral eta is defined by a finite sum of independently
constructed restricted reciprocals. The reversal theorem gives the literal
negative representatives -a used in the source. -/
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeEta_index_unit (b : Fin (p-1)) : ¬p ∣ b.val+1 :=
  Nat.not_dvd_of_pos_of_lt (by omega) (by have := b.isLt; omega)

lemma negative_nat_rational_unit (a : ℕ) (ha0 : 0 < a) (hap : a < p) :
    -(a:ℚ) ≠ 0 ∧ padicValRat p (-(a:ℚ)) = 0 := by
  constructor
  · exact neg_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt ha0))
  · rw [padicValRat.neg, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt ha0 hap)]
    rfl


def primeEta (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ℤ_[p] :=
  ∑ b : Fin (p-1), (-2:ℤ_[p])^(p-1-b.val)*
    padicParameterG (primeParameter p) (primeParameter_moment_integral hp2 hp3)
      (padicReciprocalSeries (((b.val+1:ℕ):ℚ)-(p:ℚ))
        (rational_nonmultiple_sub_prime (b.val+1) (primeEta_index_unit (p := p) b)).1
        (rational_nonmultiple_sub_prime (b.val+1) (primeEta_index_unit (p := p) b)).2 2)

theorem primeEta_negative_representatives (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    primeEta hp2 hp3 =
      ∑ a : Fin (p-1), (-2:ℤ_[p])^(a.val+1)*
        padicParameterG (primeParameter p) (primeParameter_moment_integral hp2 hp3)
          (padicReciprocalSeries (-((a.val+1:ℕ):ℚ))
            (negative_nat_rational_unit (p := p) (a.val+1) (by omega) (by have := a.isLt; omega)).1
            (negative_nat_rational_unit (p := p) (a.val+1) (by omega) (by have := a.isLt; omega)).2 2) := by
  unfold primeEta
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (p-1)))]
  apply Finset.sum_congr rfl
  intro a _
  have hi : p-1-(Fin.revPerm a).val = a.val+1 := by
    simp only [Fin.revPerm_apply, Fin.val_rev]
    have := a.isLt
    omega
  rw [hi]
  congr 2
  apply padicReciprocalSeries_congr
  simp only [Fin.revPerm_apply, Fin.val_rev]
  have ht : p-1-(a.val+1)+1+(a.val+1) = p := by have := a.isLt; omega
  have he := congrArg (fun n : ℕ => (n:ℚ)) ht
  push_cast at he ⊢
  linarith

theorem dissectedSquare_at_last (hp2 : p ≠ 2) (hp3 : p ≠ 3) (Y : ℚ_[p]) :
    dissectedSquare hp2 hp3 Y (p-1) = (p:ℚ_[p])⁻¹^2*Y := by
  have he : p-1+1 = p := by have := hp.out.pos; omega
  rw [dissectedSquare_matching hp2 hp3 Y (p-1) (by rw [he]), he]
  simp [parameterTau, Nat.div_self hp.out.pos]

theorem primeEta_window_base (hp2 : p ≠ 2) (hp3 : p ≠ 3) (Y : ℚ_[p]) :
    poleDissectionWindow (-1/2:ℚ_[p]) p (dissectedSquare hp2 hp3 Y) 0 =
      (primeEta hp2 hp3:ℚ_[p])+(p:ℚ_[p])⁻¹^2*Y := by
  rw [poleDissectionWindow_reverse _ (by norm_num)]
  have hp' : p = (p-1)+1 := by have := hp.out.pos; omega
  rw [show Finset.range p = Finset.range ((p-1)+1) from congrArg Finset.range hp',
    Finset.sum_range_succ']
  simp only [Nat.add_zero, Nat.add_sub_cancel, Nat.sub_zero, pow_zero, one_mul, zero_add]
  rw [dissectedSquare_at_last hp2 hp3 Y]
  congr 1
  rw [primeEta, PadicInt.coe_sum, ← Fin.sum_univ_eq_sum_range]
  conv_rhs => rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (p-1)))]
  apply Finset.sum_congr rfl
  intro a _
  simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_neg]
  have hi : p-1-(a.val+1) = (Fin.revPerm a).val := by
    simp only [Fin.revPerm_apply, Fin.val_rev]
  have hw : p-1-(Fin.revPerm a).val = a.val+1 := by
    simp only [Fin.revPerm_apply, Fin.val_rev]
    have := a.isLt
    omega
  rw [hi, hw, dissectedSquare_nonmatching hp2 hp3 Y _ (primeEta_index_unit (p := p) (Fin.revPerm a))]
  rw [show ((2:ℤ_[p]):ℚ_[p]) = (2:ℚ_[p]) from rfl]
  norm_num

end
end Li2

end
