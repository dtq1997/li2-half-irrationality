module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring

set_option backward.privateInPublic true

@[expose] public section
open scoped BigOperators
namespace Li2
theorem option_signed_weight_double_sum {h : ℕ} (c : ℝ)
    (E : Option (Fin h) → Option (Fin h) → ℝ) :
    let w : Option (Fin h) → ℝ := fun k => match k with | none => -1 | some _ => c
    (∑ k : Option (Fin h), ∑ l : Option (Fin h), w k * w l * E k l) =
      c ^ 2 * (∑ i : Fin h, ∑ j : Fin h, E (some i) (some j)) -
        c * (∑ i : Fin h, E (some i) none) -
        c * (∑ j : Fin h, E none (some j)) + E none none := by
  classical
  dsimp only
  simp only [Fintype.sum_option, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
theorem symmetric_double_sum_eq_diag_add_two_Ioi {h : ℕ} (F : Fin h → Fin h → ℝ)
    (hF : ∀ i j, F i j = F j i) :
    (∑ i : Fin h, ∑ j : Fin h, F i j) =
      (∑ i : Fin h, F i i) + 2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, F i j) := by
  classical
  have hoff : (∑ i : Fin h, ∑ j ∈ ({i} : Finset (Fin h))ᶜ, F j i) =
      2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, F i j) := by
    calc
      _ = ∑ i : Fin h, ∑ j ∈ Finset.Ioi i, (F j i + F i j) :=
        (Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag F).symm
      _ = ∑ i : Fin h, ∑ j ∈ Finset.Ioi i, (2 * F i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hF j i]
        ring
      _ = _ := by simp only [← Finset.mul_sum]
  calc
    (∑ i : Fin h, ∑ j : Fin h, F i j) = ∑ i : Fin h, ∑ j : Fin h, F j i := Finset.sum_comm
    _ = ∑ i : Fin h, (F i i + ∑ j ∈ ({i} : Finset (Fin h))ᶜ, F j i) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Finset.sum_singleton] using
        (Finset.sum_add_sum_compl ({i} : Finset (Fin h)) (fun j => F j i)).symm
    _ = (∑ i : Fin h, F i i) + (∑ i : Fin h, ∑ j ∈ ({i} : Finset (Fin h))ᶜ, F j i) :=
      Finset.sum_add_distrib
    _ = _ := by rw [hoff]
end Li2

end
