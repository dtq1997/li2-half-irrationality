module
public import Li2Unified.Modular.Positive.Packed.P010
public import Li2Unified.Modular.Base.PrimeDiscUnits
public import Li2Unified.Modular.Base.RestrictedPoles
public import Mathlib.LinearAlgebra.Lagrange

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalPoleCenters_unit_difference (i j : Fin p) (hij : i ≠ j) :
    IsUnit ((i.val : ℤ_[p]) - (j.val : ℤ_[p])) := by
  have hmod : i.val % p ≠ j.val := by
    simpa [Nat.mod_eq_of_lt i.isLt] using Fin.val_ne_of_ne hij
  have h := Li2.nonmatching_rational_unit (p := p)
    j.val i.val j.isLt hmod
  have he : ((i.val : ℤ_[p]) - (j.val : ℤ_[p])) =
      (Li2.integralRationalUnit ((i.val : ℚ) - (j.val : ℚ)) h.1 h.2 : ℤ_[p]) := by
    apply PadicInt.ext
    simp
  rw [he]
  exact Units.isUnit _

#print axioms generalPoleCenters_unit_difference

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalPoleCofactor_eval_isUnit (i : Fin p) :
    IsUnit ((Li2.integralPoleCofactor (generalPoleCenters (p := p)) i).eval
      (generalPoleCenters i)) := by
  unfold Li2.integralPoleCofactor
  rw [eval_prod, IsUnit.prod_iff]
  intro j hj
  simp only [eval_sub, eval_X, eval_C]
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simpa [generalPoleCenters, sub_eq_add_neg, add_comm] using
    generalPoleCenters_unit_difference j i hji

#print axioms generalPoleCofactor_eval_isUnit

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- The full cofactor family is an integral interpolation basis because
all node differences are p-adic units. -/
theorem generalPoleCofactor_basis (R : (ℤ_[p])[X])
    (hR : R.degree < p) :
    ∃ r : Fin p → ℤ_[p],
      R = ∑ i : Fin p,
        C (r i) * Li2.integralPoleCofactor (generalPoleCenters (p := p)) i := by
  let u : Fin p → (ℤ_[p])ˣ := fun i =>
    Classical.choose (generalPoleCofactor_eval_isUnit i)
  have hu (i : Fin p) : (u i : ℤ_[p]) =
      (Li2.integralPoleCofactor (generalPoleCenters (p := p)) i).eval
        (generalPoleCenters i) :=
    Classical.choose_spec (generalPoleCofactor_eval_isUnit i)
  let r : Fin p → ℤ_[p] := fun i =>
    R.eval (generalPoleCenters i) * (((u i)⁻¹ : (ℤ_[p])ˣ) : ℤ_[p])
  refine ⟨r, ?_⟩
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (Finset.univ : Finset (Fin p))
    generalPoleCenters_injective.injOn (by simpa using hR)
  · have hcof (i : Fin p) :
        (Li2.integralPoleCofactor (generalPoleCenters (p := p)) i).natDegree ≤ p - 1 := by
      unfold Li2.integralPoleCofactor
      calc
        _ ≤ ∑ j ∈ Finset.univ.erase i,
          (X - C (generalPoleCenters j) : (ℤ_[p])[X]).natDegree :=
            natDegree_prod_le _ _
        _ = p - 1 := by simp
    have hsum :
        (∑ i : Fin p,
          C (r i) * Li2.integralPoleCofactor (generalPoleCenters (p := p)) i).natDegree ≤
          p - 1 := by
      apply natDegree_sum_le_of_forall_le
      intro i _
      exact (natDegree_C_mul_le _ _).trans (hcof i)
    have hp : 0 < p := (Fact.out : p.Prime).pos
    have hlt : p - 1 < (Finset.univ : Finset (Fin p)).card := by
      simp
      omega
    exact (degree_le_of_natDegree_le hsum).trans_lt
      (WithBot.coe_lt_coe.mpr hlt)
  · intro i _
    rw [eval_finset_sum, Finset.sum_eq_single i]
    · simp only [eval_mul, eval_C]
      rw [← hu i]
      simp [r, mul_assoc]
    · intro j _ hji
      simp [eval_mul,
        Li2.integralPoleCofactor_eval_other (generalPoleCenters (p := p)) i j hji.symm]
    · simp

/-- Every integral polynomial has a simple-pole numerator presentation over
the full carrier, with integral regular quotient and integral residues. -/
theorem generalPolePolynomial_decomposition (H : (ℤ_[p])[X]) :
    ∃ Q : (ℤ_[p])[X], ∃ r : Fin p → ℤ_[p],
      H = Li2.integralPoleDenominator (generalPoleCenters (p := p)) * Q +
        ∑ i : Fin p,
          C (r i) * Li2.integralPoleCofactor (generalPoleCenters (p := p)) i := by
  let D := Li2.integralPoleDenominator (generalPoleCenters (p := p))
  have hD : D.Monic := by
    unfold D Li2.integralPoleDenominator
    exact monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
  have hDdeg : D.degree = p := by
    rw [degree_eq_natDegree hD.ne_zero]
    unfold D Li2.integralPoleDenominator
    rw [natDegree_prod_of_monic]
    · simp
    · intro i _
      exact monic_X_sub_C _
  have hR : (H %ₘ D).degree < p := by
    simpa [hDdeg] using degree_modByMonic_lt H hD
  obtain ⟨r, hr⟩ := generalPoleCofactor_basis (H %ₘ D) hR
  refine ⟨H /ₘ D, r, ?_⟩
  calc
    H = H %ₘ D + D * (H /ₘ D) := (modByMonic_add_div H D).symm
    _ = D * (H /ₘ D) +
        ∑ i : Fin p,
          C (r i) * Li2.integralPoleCofactor (generalPoleCenters (p := p)) i := by
      rw [hr]
      ring

#print axioms generalPoleCofactor_basis
#print axioms generalPolePolynomial_decomposition

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def generalPoleSubsetDenominator (s : Finset (Fin p)) : (ℤ_[p])[X] :=
  ∏ i ∈ s, (X - C (generalPoleCenters i))

theorem generalPoleSubset_product (s : Finset (Fin p)) :
    generalPoleSubsetDenominator s * generalPoleSubsetDenominator sᶜ =
      Li2.integralPoleDenominator (generalPoleCenters (p := p)) := by
  classical
  unfold generalPoleSubsetDenominator Li2.integralPoleDenominator
  simpa [mul_comm] using
    (Finset.prod_compl_mul_prod s
      (fun i : Fin p => (X - C (generalPoleCenters i) : (ℤ_[p])[X])))

theorem generalPoleSubset_integral_cleared (s : Finset (Fin p))
    (P : (ℤ_[p])[X]) :
    ∃ g : (ℤ_[p])[X], ∃ r : Fin p → ℤ_[p],
      (generalPoleSubsetDenominator s : PowerSeries ℤ_[p]) *
        Li2.integralPoleNumerator (generalPoleCenters (p := p))
          (g : PowerSeries ℤ_[p]) r =
      (Li2.integralPoleDenominator
        (generalPoleCenters (p := p)) : PowerSeries ℤ_[p]) *
          (P : PowerSeries ℤ_[p]) := by
  classical
  let U := generalPoleSubsetDenominator sᶜ
  obtain ⟨g, r, hdecomp⟩ := generalPolePolynomial_decomposition (U * P)
  refine ⟨g, r, ?_⟩
  have hpoly : generalPoleSubsetDenominator s *
      (Li2.integralPoleDenominator (generalPoleCenters (p := p)) * g +
        ∑ i : Fin p,
          C (r i) * Li2.integralPoleCofactor (generalPoleCenters (p := p)) i) =
      Li2.integralPoleDenominator (generalPoleCenters (p := p)) * P := by
    rw [← hdecomp]
    change generalPoleSubsetDenominator s * (generalPoleSubsetDenominator sᶜ * P) = _
    rw [← mul_assoc, generalPoleSubset_product]
  have hseries := congrArg
    (fun Q : (ℤ_[p])[X] => (Q : PowerSeries ℤ_[p])) hpoly
  simpa only [Li2.integralPoleNumerator, Polynomial.coe_mul,
    Polynomial.coe_add, map_sum] using hseries

#print axioms generalPoleSubset_product
#print axioms generalPoleSubset_integral_cleared

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def generalMatchingTailPolynomial (n : ℕ) (a : Fin p) : (ℤ_[p])[X] :=
  ∏ j ∈ (Finset.Icc (n + 1) (4 * n)).filter
    (fun j => j % p = a.val), (X + C ((j / p : ℕ) : ℤ_[p]))

theorem generalMatchingTailPolynomial_subset (n : ℕ) (a : Fin p)
    (hp : 0 < p) (hsq : 4 * n < p * p) :
    generalMatchingTailPolynomial n a =
      generalPoleSubsetDenominator (generalTailPoleSet n p a) := by
  classical
  let S := (Finset.Icc (n + 1) (4 * n)).filter (fun j => j % p = a.val)
  let f : ∀ j ∈ S, Fin p := fun j hj =>
    ⟨j / p, pole_index_window p (4 * n) j hp hsq
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).2⟩
  change (∏ j ∈ S, (X + C ((j / p : ℕ) : ℤ_[p]))) =
    ∏ k ∈ generalTailPoleSet n p a,
      (X - C (generalPoleCenters k))
  refine Finset.prod_bij f ?_ ?_ ?_ ?_
  · intro j hj
    apply (generalTailPoleSet_mem_iff n p a (f j hj) hp).2
    exact ⟨j, hj, rfl⟩
  · intro j hj k hk h
    apply matching_pole_index_injective p j k a
      (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
    exact congrArg Fin.val h
  · intro k hk
    obtain ⟨j, hj, hdiv⟩ :=
      (generalTailPoleSet_mem_iff n p a k hp).1 hk
    refine ⟨j, hj, Fin.ext ?_⟩
    exact hdiv
  · intro j hj
    simp [generalPoleCenters, f, sub_eq_add_neg]

#print axioms generalMatchingTailPolynomial_subset

end
end Li2Unified.Proofs.Hermite

end


end
