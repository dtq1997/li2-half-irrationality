module
public import Li2Unified.Modular.Positive.Packed.P001
public import Li2Unified.Modular.Base.PrimePoleExtension
public import Li2Unified.Modular.Positive.Packed.P009

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- A uniform carrier for every matching pole when the largest pole is below
`p²`. Unused centers may carry zero residue. -/
def generalPoleCenters : Fin p → ℤ_[p] := fun k => -(k.val : ℤ_[p])

theorem generalPoleCenters_injective : Function.Injective (generalPoleCenters (p := p)) := by
  intro i j h
  apply Fin.ext
  have he : (i.val : ℤ_[p]) = (j.val : ℤ_[p]) := neg_injective h
  exact_mod_cast he

def generalPoleU (z : ℚ) (hzUnit : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : Li2.VG p (z / (1 - z)) 0)
    (f : PowerSeries ℤ_[p]) (r : Fin p → ℤ_[p]) : (ℤ_[p])[X] :=
  Li2.restrictedPoleFunctional
    (fun n => (n + 1 : ℕ) * Li2.integralParameterMoment z hz n)
    (fun k : Fin p => Li2.integralUPole z hzUnit.1 hzUnit.2 k.val k.isLt)
    f r

def generalPoleV (z : ℚ) (hzUnit : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : Li2.VG p (z / (1 - z)) 0)
    (f : PowerSeries ℤ_[p]) (r : Fin p → ℤ_[p]) : (ℤ_[p])[X] :=
  Li2.restrictedPoleFunctional
    (Li2.derivativeMoments (Li2.integralParameterMoment z hz))
    (fun k : Fin p => Li2.integralVPole z hzUnit.1 hzUnit.2 k.val k.isLt)
    f r

theorem generalPoleU_coeff_bound (z : ℚ)
    (hzUnit : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : Li2.VG p (z / (1 - z)) 0)
    (f : PowerSeries ℤ_[p]) (r : Fin p → ℤ_[p])
    (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B)
    (hr : ∀ k, ‖r k‖ ≤ B) (n : ℕ) :
    ‖(generalPoleU z hzUnit hz f r).coeff n‖ ≤ B := by
  exact Li2.restrictedPoleFunctional_coeff_bound _ _ f r B hB hf hr n

theorem generalPoleV_coeff_bound (z : ℚ)
    (hzUnit : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : Li2.VG p (z / (1 - z)) 0)
    (f : PowerSeries ℤ_[p]) (r : Fin p → ℤ_[p])
    (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B)
    (hr : ∀ k, ‖r k‖ ≤ B) (n : ℕ) :
    ‖(generalPoleV z hzUnit hz f r).coeff n‖ ≤ B := by
  exact Li2.restrictedPoleFunctional_coeff_bound _ _ f r B hB hf hr n

#print axioms generalPoleCenters_injective
#print axioms generalPoleU_coeff_bound
#print axioms generalPoleV_coeff_bound

end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section

def generalMatchingPoleIndex (p m j : ℕ) (a : Fin p)
    (hp : 0 < p) (hm : m < p * p) (hj : j ≤ m)
    (_hmod : j % p = a.val) : Fin p :=
  ⟨j / p, pole_index_window p m j hp hm hj⟩

theorem generalMatchingPole_denominator (p m j : ℕ) (a : Fin p)
    (hp : 0 < p) (hm : m < p * p) (hj : j ≤ m)
    (hmod : j % p = a.val) :
    (j : ℚ) - (a.val : ℚ) =
      (p : ℚ) * (generalMatchingPoleIndex p m j a hp hm hj hmod).val := by
  have hdec := pole_index_decompose p j
  rw [hmod] at hdec
  have hc := congrArg (fun v : ℕ => (v : ℚ)) hdec
  push_cast at hc
  dsimp [generalMatchingPoleIndex]
  linear_combination hc

#print axioms generalMatchingPole_denominator

end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section

def generalTailPoleSet (n p : ℕ) (a : Fin p) : Finset (Fin p) :=
  Finset.univ.filter (fun k =>
    n < a.val + p * k.val ∧ a.val + p * k.val ≤ 4 * n)

theorem generalTailPoleSet_mem_iff (n p : ℕ) (a k : Fin p)
    (hp : 0 < p) :
    k ∈ generalTailPoleSet n p a ↔
      ∃ j ∈ (Finset.Icc (n + 1) (4 * n)).filter
        (fun j => j % p = a.val), j / p = k.val := by
  constructor
  · intro hk
    have hb := (Finset.mem_filter.mp hk).2
    let j := a.val + p * k.val
    have hmod : j % p = a.val := by
      dsimp [j]
      simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
    have hdiv : j / p = k.val := by
      dsimp [j]
      rw [Nat.add_mul_div_left a.val k.val hp]
      simp [Nat.div_eq_of_lt a.isLt]
    refine ⟨j, ?_, hdiv⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hb.2⟩, hmod⟩
  · rintro ⟨j, hj, hdiv⟩
    have hb := (Finset.mem_filter.mp hj).1
    have hmod := (Finset.mem_filter.mp hj).2
    have hdec := pole_index_decompose p j
    rw [hmod, hdiv] at hdec
    simp only [generalTailPoleSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hb
    omega

#print axioms generalTailPoleSet_mem_iff

end
end Li2Unified.Proofs.Hermite

end

end
