module
public import Li2Unified.Modular.Base.DissectedSquareRecurrence
public import Li2Unified.Modular.Base.PrimeEta
public import Li2Unified.Modular.Base.PulledPoleValues

set_option backward.privateInPublic true

@[expose] public section

/-! Exact all-index simple-pole residue sum, with the actual eta and the
substitution Y=p^2(X-eta). The individual summands are independently defined
matching poles or nonmatching restricted inverse squares. -/
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem dissectedSquare_window_identity (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (Y : ℚ_[p]) (j : ℕ) :
    poleDissectionWindow (-1/2:ℚ_[p]) p (dissectedSquare hp2 hp3 Y) j =
      (-1/2:ℚ_[p])⁻¹^j*((primeEta hp2 hp3:ℚ_[p])+(p:ℚ_[p])⁻¹^2*Y-
        (parameterTau (-1/2) j:ℚ_[p])) := by
  have hs := poleDissectionWindow_telescope (-1/2:ℚ_[p]) (by norm_num) p hp.out.pos
    (dissectedSquare hp2 hp3 Y) (fun m => (((m:ℚ_[p])+1)^2)⁻¹)
    (fun m => by
      have h := dissectedSquare_step hp2 hp3 Y m
      have hzcast : (primeParameter p:ℚ_[p]) = (-1/2:ℚ_[p])^p := by
        rw [primeParameter, Rat.cast_pow]
        norm_num
      rw [hzcast] at h
      simpa only [div_eq_mul_inv] using h) j
  rw [primeEta_window_base hp2 hp3 Y] at hs
  have ht : (∑ b ∈ Finset.range j, (-1/2:ℚ_[p])^(b+1)*(((b:ℚ_[p])+1)^2)⁻¹) =
      (parameterTau (-1/2) j:ℚ_[p]) := by
    rw [parameterTau_eq_range, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro b _
    push_cast
    rfl
  rw [ht] at hs
  rw [← hs]
  have hn : (-1/2:ℚ_[p])^j ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [inv_pow, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem prime_simple_pole_dissection (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (X : ℚ_[p]) (j : ℕ) :
    ∑ a ∈ Finset.range p, (-1/2:ℚ_[p])⁻¹^a*(j:ℚ_[p])*
      dissectedSquare hp2 hp3 ((p:ℚ_[p])^2*(X-(primeEta hp2 hp3:ℚ_[p])))
        (j+(p-1-a)) =
    (j:ℚ_[p])*(-1/2:ℚ_[p])⁻¹^j*(X-(parameterTau (-1/2) j:ℚ_[p])) := by
  have he := dissectedSquare_window_identity hp2 hp3
    ((p:ℚ_[p])^2*(X-(primeEta hp2 hp3:ℚ_[p]))) j
  rw [poleDissectionWindow_reverse _ (by norm_num)] at he
  have hpne : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hc : (primeEta hp2 hp3:ℚ_[p])+(p:ℚ_[p])⁻¹^2*
      ((p:ℚ_[p])^2*(X-(primeEta hp2 hp3:ℚ_[p]))) = X := by
    field_simp
    <;> ring
  rw [hc] at he
  calc
    _ = (j:ℚ_[p])*(∑ a ∈ Finset.range p, (-1/2:ℚ_[p])⁻¹^a*
        dissectedSquare hp2 hp3 ((p:ℚ_[p])^2*(X-(primeEta hp2 hp3:ℚ_[p])))
          (j+(p-1-a))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [he]; ring


theorem prime_simple_pole_dissection_uv (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (X : ℚ_[p]) (j : ℕ) :
    ∑ a ∈ Finset.range p, (-1/2:ℚ_[p])⁻¹^a*
      pulledSimplePoleContribution hp2 hp3
        ((p:ℚ_[p])^2*(X-(primeEta hp2 hp3:ℚ_[p]))) j a =
    (j:ℚ_[p])*(-1/2:ℚ_[p])⁻¹^j*(X-(parameterTau (-1/2) j:ℚ_[p])) := by
  calc
    _ = ∑ a ∈ Finset.range p, (-1/2:ℚ_[p])⁻¹^a*(j:ℚ_[p])*
        dissectedSquare hp2 hp3 ((p:ℚ_[p])^2*(X-(primeEta hp2 hp3:ℚ_[p])))
          (j+(p-1-a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [pulledSimplePoleContribution_eq hp2 hp3 _ j a (Finset.mem_range.mp ha), mul_assoc]
    _ = _ := prime_simple_pole_dissection hp2 hp3 X j

end
end Li2

end
