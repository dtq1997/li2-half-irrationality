module
public import Li2Unified.Modular.Base.ParameterPoleValues
public import Mathlib.Algebra.BigOperators.Intervals

set_option backward.privateInPublic true

@[expose] public section

/-! Finite sliding-window dissection. This lemma is algebraic; its recurrence
hypothesis is to be supplied by the independently constructed p-adic factors. -/
open scoped BigOperators
namespace Li2
noncomputable section

section Window
variable {K : Type*} [Field K]

def poleDissectionWindow (z : K) (p : ℕ) (F : ℕ → K) (j : ℕ) : K :=
  z⁻¹^(p-1)*∑ b ∈ Finset.range p, z^b*F (j+b)

theorem poleDissectionWindow_step (z : K) (hz : z ≠ 0) (p : ℕ) (hp : 0 < p)
    (F B : ℕ → K) (hF : ∀ j, z^p*F (j+p) = F j-z^p*B j) (j : ℕ) :
    z*poleDissectionWindow z p F (j+1) = poleDissectionWindow z p F j-z*B j := by
  have hs := Finset.sum_range_succ' (fun b => z^b*F (j+b)) p
  rw [Finset.sum_range_succ] at hs
  have ht : (∑ b ∈ Finset.range p, z^(b+1)*F (j+(b+1))) =
      z*∑ b ∈ Finset.range p, z^b*F (j+1+b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [pow_succ]
    simp only [Nat.add_assoc, Nat.add_comm 1 b]
    ring
  rw [ht] at hs
  simp only [pow_zero, one_mul, Nat.add_zero] at hs
  have hi : z⁻¹^(p-1)*z^p = z := by
    nth_rw 2 [show p = (p-1)+1 by omega]
    rw [pow_succ, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hz), one_mul]
  unfold poleDissectionWindow
  calc
    _ = z⁻¹^(p-1)*(z*∑ b ∈ Finset.range p, z^b*F (j+1+b)) := by ring
    _ = z⁻¹^(p-1)*((∑ b ∈ Finset.range p, z^b*F (j+b))+z^p*F (j+p)-F j) := by rw [hs]; ring
    _ = z⁻¹^(p-1)*(∑ b ∈ Finset.range p, z^b*F (j+b))-
        (z⁻¹^(p-1)*z^p)*B j := by rw [hF j]; ring
    _ = _ := by rw [hi]

theorem poleDissectionWindow_telescope (z : K) (hz : z ≠ 0) (p : ℕ) (hp : 0 < p)
    (F B : ℕ → K) (hF : ∀ j, z^p*F (j+p) = F j-z^p*B j) (j : ℕ) :
    z^j*poleDissectionWindow z p F j = poleDissectionWindow z p F 0-
      ∑ b ∈ Finset.range j, z^(b+1)*B b := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_assoc, poleDissectionWindow_step z hz p hp F B hF j,
      mul_sub, ← mul_assoc, ih, Finset.sum_range_succ, pow_succ]
    ring
end Window

lemma parameterTau_succ (z : ℚ) (j : ℕ) :
    parameterTau z (j+1) = parameterTau z j+z^(j+1)/(j+1:ℚ)^2 := by
  unfold parameterTau
  rw [Finset.sum_Icc_succ_top (by omega)]
  push_cast
  rfl

lemma parameterTau_eq_range (z : ℚ) (j : ℕ) :
    parameterTau z j = ∑ b ∈ Finset.range j, z^(b+1)/(b+1:ℚ)^2 := by
  induction j with
  | zero => simp [parameterTau]
  | succ j ih => rw [parameterTau_succ, Finset.sum_range_succ, ih]

end
end Li2

end
