module
public import Li2Unified.Modular.Positive.Packed.P008
public import Li2Unified.Modular.Positive.Packed.P001

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- Exact determinant assembly; the actual entry estimates remain an explicit input. -/
theorem generalOriginalGramGV_of_entries (n : ℕ) (hpn : p ≤ n)
    (M : Matrix (Fin (2*n)) (Fin (2*n)) ℚ[X])
    (hentry : ∀ i j, Li2.GV p (M i j)
      (((generalOriginalRowTwiceWeight n hpn i : ℚ) +
        (generalOriginalRowTwiceWeight n hpn j : ℚ))/2)) :
    Li2.GV p M.det
      ((∑ a : Fin p,
        (((CountsCore.residueCount p (4*n) a:ℚ)-2*(CountsCore.residueCount p n a:ℚ)) *
         ((CountsCore.residueCount p n a:ℚ)-2))) +
        ((((4*n)/p:ℕ):ℚ)-2*((n/p:ℕ):ℚ))) := by
  let w : Fin (2*n) → ℚ := fun i => (generalOriginalRowTwiceWeight n hpn i : ℚ)/2
  have hd := Li2.det_GV M w w (by
    intro i j
    convert hentry i j using 1 <;> dsimp [w] <;> ring)
  have he : (∑ i : Fin (2*n), w i)+(∑ i : Fin (2*n), w i) =
      ∑ i : Fin (2*n), (generalOriginalRowTwiceWeight n hpn i : ℚ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w]
    ring
  have hs : (∑ i : Fin (2*n), (generalOriginalRowTwiceWeight n hpn i : ℚ)) =
      (∑ a : Fin p,
        (((CountsCore.residueCount p (4*n) a:ℚ)-2*(CountsCore.residueCount p n a:ℚ)) *
         ((CountsCore.residueCount p n a:ℚ)-2))) +
        ((((4*n)/p:ℕ):ℚ)-2*((n/p:ℕ):ℚ)) := by
    exact_mod_cast generalOriginalRowTwiceWeight_sum n hpn
  rwa [he,hs] at hd

theorem generalOriginalFunctionalBasis_of_entries (lam : ℚ) (n : ℕ) (hpn : p ≤ n)
    (hentry : ∀ i j : Fin (2*n), Li2.GV p
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*n)
        ((Li2.D n)^3 * (generalOriginalBasis n hpn i).map (Int.castRingHom ℚ) *
          (generalOriginalBasis n hpn j).map (Int.castRingHom ℚ)))
      (((generalOriginalRowTwiceWeight n hpn i : ℚ) +
        (generalOriginalRowTwiceWeight n hpn j : ℚ))/2)) :
    ∃ E : Fin (2*n) → ℚ[X],
      (∀ i, (E i).natDegree < 2*n) ∧
      (Li2.coeffMat E).det ≠ 0 ∧ padicValRat p (Li2.coeffMat E).det = 0 ∧
      Li2.GV p ((Matrix.of fun i j : Fin (2*n) =>
        Li2Unified.ParameterFamily.numeratorFunctional lam (4*n)
          ((Li2.D n)^3 * E i * E j)).det)
      ((∑ a : Fin p,
        (((CountsCore.residueCount p (4*n) a:ℚ)-2*(CountsCore.residueCount p n a:ℚ)) *
         ((CountsCore.residueCount p n a:ℚ)-2))) +
        ((((4*n)/p:ℕ):ℚ)-2*((n/p:ℕ):ℚ))) := by
  let E : Fin (2*n) → ℚ[X] := fun i =>
    (generalOriginalBasis n hpn i).map (Int.castRingHom ℚ)
  refine ⟨E, ?_, (generalOriginalBasis_det_unit n hpn).1,
    (generalOriginalBasis_det_unit n hpn).2, ?_⟩
  · intro i
    exact lt_of_le_of_lt Polynomial.natDegree_map_le (generalOriginalBasis_natDegree_lt n hpn i)
  · apply generalOriginalGramGV_of_entries n hpn
    exact hentry

end
end Li2Unified.Proofs.Hermite
#print axioms Li2Unified.Proofs.Hermite.generalOriginalFunctionalBasis_of_entries

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section

theorem matching_pole_index_injective (p j k : ℕ) (a : Fin p)
    (hj : j % p = a.val) (hk : k % p = a.val)
    (hdiv : j / p = k / p) : j = k := by
  have h1 := pole_index_decompose p j
  have h2 := pole_index_decompose p k
  rw [hj, hdiv] at h1
  rw [hk] at h2
  omega

#print axioms matching_pole_index_injective

end
end Li2Unified.Proofs.Hermite

end

end
