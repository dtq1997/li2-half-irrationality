module
public import Li2Unified.Modular.Positive.Packed.P005
public import Li2Unified.Modular.Positive.Packed.P006
public import Li2Unified.Modular.Base.PrimeProductJets
public import Li2Unified.Modular.Positive.Packed.P002

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def generalAppendedBasisLocalOrder (n : ℕ) (a : Fin p) :
    Fin (generalJetSize n p + 1) → ℕ :=
  Fin.cases (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a)
    (fun i => generalIndexedJetLocalOrder n p i a)

noncomputable def generalOriginalBasisLocalOrder (n : ℕ) (hpn : p ≤ n)
    (i : Fin (2 * n)) (a : Fin p) : ℕ := by
  by_cases hd : Li2Unified.Proofs.Hermite.CountsCore.delta n p = 0
  · exact generalIndexedJetLocalOrder n p
      (Fin.cast (by have := generalJetSize_add_delta n hpn; omega) i) a
  · have hd1 : Li2Unified.Proofs.Hermite.CountsCore.delta n p = 1 := by
      have := general_delta_le_one n hpn
      omega
    exact generalAppendedBasisLocalOrder n a
      (Fin.cast (by have := generalJetSize_add_delta n hpn; omega) i)

theorem generalAppendedBasis_disc_factor (n : ℕ)
    (i : Fin (generalJetSize n p + 1)) (a : Fin p) :
    ∃ A : ℤ[X], (generalAppendedBasis n i).comp
      (Li2.primeDiscSubstitution p a) =
        C ((p : ℤ) ^ (generalAppendedBasisLocalOrder n a i)) *
          X ^ (generalAppendedBasisLocalOrder n a i) * A := by
  refine Fin.cases ?_ ?_ i
  · obtain ⟨A, hA⟩ := Li2.fullClassProduct_expansion
      (Li2.primeCenter p)
      (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p) a (p : ℤ)
    exact ⟨C ((Li2.classProduct (Li2.primeCenter p)
      (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p) a).eval
        (Li2.primeCenter p a)) + C (p : ℤ) * A,
      by simpa only [generalAppendedBasis, generalAppendedBasisLocalOrder,
        Fin.cases_zero, Li2.primeDiscSubstitution] using hA⟩
  · intro j
    simpa only [generalAppendedBasis, generalAppendedBasisLocalOrder,
      Fin.cases_succ] using generalIndexedJet_disc_factor n p j a

theorem generalOriginalBasis_disc_factor (n : ℕ) (hpn : p ≤ n)
    (i : Fin (2 * n)) (a : Fin p) :
    ∃ A : ℤ[X], (generalOriginalBasis n hpn i).comp
      (Li2.primeDiscSubstitution p a) =
        C ((p : ℤ) ^ (generalOriginalBasisLocalOrder n hpn i a)) *
          X ^ (generalOriginalBasisLocalOrder n hpn i a) * A := by
  by_cases hd : Li2Unified.Proofs.Hermite.CountsCore.delta n p = 0
  · simpa only [generalOriginalBasis, generalOriginalBasisLocalOrder,
      dif_pos hd] using generalIndexedJet_disc_factor n p
        (Fin.cast (by have := generalJetSize_add_delta n hpn; omega) i) a
  · have hd1 : Li2Unified.Proofs.Hermite.CountsCore.delta n p = 1 := by
      have := general_delta_le_one n hpn
      omega
    simpa only [generalOriginalBasis, generalOriginalBasisLocalOrder,
      dif_neg hd] using generalAppendedBasis_disc_factor n
        (Fin.cast (by have := generalJetSize_add_delta n hpn; omega) i) a

theorem generalOriginalBasisProduct_disc_factor (n : ℕ) (hpn : p ≤ n)
    (i j : Fin (2 * n)) (a : Fin p) :
    ∃ A : ℤ[X], (generalOriginalBasis n hpn i *
        generalOriginalBasis n hpn j).comp (Li2.primeDiscSubstitution p a) =
      C ((p : ℤ) ^ (generalOriginalBasisLocalOrder n hpn i a +
        generalOriginalBasisLocalOrder n hpn j a)) *
      X ^ (generalOriginalBasisLocalOrder n hpn i a +
        generalOriginalBasisLocalOrder n hpn j a) * A := by
  obtain ⟨A, hA⟩ := generalOriginalBasis_disc_factor n hpn i a
  obtain ⟨B, hB⟩ := generalOriginalBasis_disc_factor n hpn j a
  refine ⟨A * B, ?_⟩
  rw [mul_comp, hA, hB]
  simp only [pow_add, C_mul]
  ring

#print axioms generalAppendedBasis_disc_factor
#print axioms generalOriginalBasis_disc_factor
#print axioms generalOriginalBasisProduct_disc_factor
end
end Li2Unified.Proofs.Hermite


end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem matchingCount_two_le_four (n : ℕ) (hpn : p ≤ n) (a : Fin p) :
    2 * matchingCount n p a ≤ matchingCount (4 * n) p a := by
  have hN := matchingCount_le_triple_floor n hpn a
  have hT := (matchingCount_tail_floor_all n a).1
  omega

theorem generalDelta_floor_relation (n : ℕ) :
    (4 * n) / p = n / p + (3 * n) / p +
      Li2Unified.Proofs.Hermite.CountsCore.delta n p := by
  have hlo : n / p + (3 * n) / p ≤ (4 * n) / p := by
    simpa [show n + 3 * n = 4 * n by omega] using
      (Nat.div_add_div_le_add_div (x := n) (y := 3 * n) (z := p))
  unfold Li2Unified.Proofs.Hermite.CountsCore.delta
  omega

def generalDiscBase (n : ℕ) (a : Fin p) : ℤ :=
  3 * (matchingCount n p a : ℤ) - (matchingCount (4 * n) p a : ℤ) -
    (if a.val = 0 then 0 else 1)

theorem generalDiscTop_nonzero (n : ℕ) (hpn : p ≤ n)
    (a : Fin p) (ha : a.val ≠ 0) :
    (((3 * n) / p : ℕ) : ℤ) - 1 ≤ generalDiscBase n a +
      2 * (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a : ℤ) ∧
    generalDiscBase n a +
      2 * (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a : ℤ) ≤
      (((3 * n) / p : ℕ) : ℤ) := by
  have htwo := matchingCount_two_le_four n hpn a
  have ht := matchingCount_tail_floor_all n a
  have hm : Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a =
      matchingCount (4 * n) p a - 2 * matchingCount n p a := by
    simp only [Li2Unified.Proofs.Hermite.CountsCore.multiplicity, if_neg ha]
    rfl
  simp only [generalDiscBase, if_neg ha, hm]
  omega

theorem generalDiscTop_zero (n : ℕ) (hpn : p ≤ n)
    (a : Fin p) (ha : a.val = 0) :
    (((3 * n) / p : ℕ) : ℤ) - 1 ≤ generalDiscBase n a +
      2 * (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a : ℤ) ∧
    generalDiscBase n a +
      2 * (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a : ℤ) ≤
      (((3 * n) / p : ℕ) : ℤ) ∧
    (Li2Unified.Proofs.Hermite.CountsCore.delta n p = 1 →
      generalDiscBase n a +
        2 * (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a : ℤ) =
        (((3 * n) / p : ℕ) : ℤ) - 1) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  let z : Fin p := ⟨0, hp0⟩
  have haz : a = z := Fin.ext ha
  subst a
  have hN : matchingCount n p z = n / p := matchingCount_zero n
  have hC : matchingCount (4 * n) p z = (4 * n) / p := matchingCount_zero (4 * n)
  have hm : Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p z =
      (3 * n) / p - n / p := by simp [Li2Unified.Proofs.Hermite.CountsCore.multiplicity, z]
  have hA : n / p ≤ (3 * n) / p := Nat.div_le_div_right (by omega)
  have hdelta := generalDelta_floor_relation (p := p) n
  have hdelta1 := general_delta_le_one n hpn
  simp only [generalDiscBase, hN, hC, hm, z, if_true, Nat.cast_sub hA]
  omega

theorem generalDiscTop_bounds (n : ℕ) (hpn : p ≤ n) (a : Fin p) :
    (((3 * n) / p : ℕ) : ℤ) - 1 ≤ generalDiscBase n a +
      2 * (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a : ℤ) ∧
    generalDiscBase n a +
      2 * (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a : ℤ) ≤
      (((3 * n) / p : ℕ) : ℤ) := by
  by_cases ha : a.val = 0
  · exact ⟨(generalDiscTop_zero n hpn a ha).1,
      (generalDiscTop_zero n hpn a ha).2.1⟩
  · exact generalDiscTop_nonzero n hpn a ha

#print axioms matchingCount_two_le_four
#print axioms generalDelta_floor_relation
#print axioms generalDiscTop_nonzero
#print axioms generalDiscTop_zero
#print axioms generalDiscTop_bounds
end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def generalIndexedRowTwiceWeight (n p : ℕ)
    (i : Fin (generalJetSize n p)) : ℤ :=
  generalDiscBase n (generalJetEquiv n p i).1 +
    2 * ((generalJetEquiv n p i).2.val : ℤ)

theorem generalIndexedRow_disc_bound (n : ℕ) (hpn : p ≤ n)
    (i : Fin (generalJetSize n p)) (a : Fin p) :
    generalIndexedRowTwiceWeight n p i ≤ generalDiscBase n a +
      2 * (generalIndexedJetLocalOrder n p i a : ℤ) := by
  let d : Fin p := (generalJetEquiv n p i).1
  by_cases he : a = d
  · subst a
    simp [generalIndexedRowTwiceWeight, generalIndexedJetLocalOrder, d]
  · have hown : generalDiscBase n (generalJetEquiv n p i).1 +
        2 * (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p
          (generalJetEquiv n p i).1 : ℤ) ≤ (((3 * n) / p : ℕ) : ℤ) :=
      (generalDiscTop_bounds n hpn d).2
    have hother := (generalDiscTop_bounds n hpn a).1
    have hi : (generalJetEquiv n p i).2.val <
        Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p
          (generalJetEquiv n p i).1 :=
      (generalJetEquiv n p i).2.isLt
    change a ≠ (generalJetEquiv n p i).1 at he
    simp only [generalIndexedRowTwiceWeight, generalIndexedJetLocalOrder,
      if_neg he]
    omega

#print axioms generalIndexedRow_disc_bound
end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def generalAppendedRowTwiceWeight (n : ℕ) :
    Fin (generalJetSize n p + 1) → ℤ :=
  Fin.cases ((((3 * n) / p : ℕ) : ℤ) - 1)
    (generalIndexedRowTwiceWeight n p)

theorem generalAppendedRow_disc_bound (n : ℕ) (hpn : p ≤ n)
    (i : Fin (generalJetSize n p + 1)) (a : Fin p) :
    generalAppendedRowTwiceWeight n i ≤ generalDiscBase n a +
      2 * (generalAppendedBasisLocalOrder n a i : ℤ) := by
  refine Fin.cases ?_ ?_ i
  · simpa only [generalAppendedRowTwiceWeight,
      generalAppendedBasisLocalOrder, Fin.cases_zero] using
      (generalDiscTop_bounds n hpn a).1
  · intro j
    simpa only [generalAppendedRowTwiceWeight,
      generalAppendedBasisLocalOrder, Fin.cases_succ] using
      generalIndexedRow_disc_bound n hpn j a

noncomputable def generalOriginalRowTwiceWeight (n : ℕ) (hpn : p ≤ n)
    (i : Fin (2 * n)) : ℤ := by
  by_cases hd : Li2Unified.Proofs.Hermite.CountsCore.delta n p = 0
  · exact generalIndexedRowTwiceWeight n p
      (Fin.cast (by have := generalJetSize_add_delta (p := p) n hpn; omega) i)
  · exact generalAppendedRowTwiceWeight (p := p) n
      (Fin.cast (by have := generalJetSize_add_delta (p := p) n hpn
                    have := general_delta_le_one (p := p) n hpn
                    omega) i)

theorem generalOriginalRow_disc_bound (n : ℕ) (hpn : p ≤ n)
    (i : Fin (2 * n)) (a : Fin p) :
    generalOriginalRowTwiceWeight n hpn i ≤ generalDiscBase n a +
      2 * (generalOriginalBasisLocalOrder n hpn i a : ℤ) := by
  by_cases hd : Li2Unified.Proofs.Hermite.CountsCore.delta n p = 0
  · simpa only [generalOriginalRowTwiceWeight,
      generalOriginalBasisLocalOrder, dif_pos hd] using
      generalIndexedRow_disc_bound n hpn
        (Fin.cast (by have := generalJetSize_add_delta (p := p) n hpn; omega) i) a
  · simpa only [generalOriginalRowTwiceWeight,
      generalOriginalBasisLocalOrder, dif_neg hd] using
      generalAppendedRow_disc_bound n hpn
        (Fin.cast (by have := generalJetSize_add_delta (p := p) n hpn
                      have := general_delta_le_one (p := p) n hpn
                      omega) i) a

#print axioms generalAppendedRow_disc_bound
#print axioms generalOriginalRow_disc_bound
end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section

theorem nonzero_class_twice_sum_identity (N C : ℕ) (h : 2 * N ≤ C) :
    let m := C - 2 * N
    (m : ℤ) * (3 * (N : ℤ) - (C : ℤ) - 1) +
        (m : ℤ) * ((m : ℤ) - 1) =
      ((C : ℤ) - 2 * (N : ℤ)) * ((N : ℤ) - 2) := by
  dsimp only
  have hsub : ((C - 2 * N : ℕ) : ℤ) = (C : ℤ) - 2 * (N : ℤ) := by omega
  rw [hsub]
  ring

theorem zero_class_twice_sum_identity (A F L δ : ℕ)
    (hA : A ≤ F) (hL : L = A + F + δ) (hδ : δ ≤ 1) :
    let m := F - A
    let b : ℤ := 3 * (A : ℤ) - (L : ℤ)
    (m : ℤ) * b + (m : ℤ) * ((m : ℤ) - 1) +
        (δ : ℤ) * (b + 2 * (m : ℤ)) =
      ((L : ℤ) - 2 * (A : ℤ)) * ((A : ℤ) - 1) := by
  dsimp only
  have hsub : ((F - A : ℕ) : ℤ) = (F : ℤ) - (A : ℤ) := by omega
  have hLz : (L : ℤ) = (A : ℤ) + (F : ℤ) + (δ : ℤ) := by exact_mod_cast hL
  rcases (show δ = 0 ∨ δ = 1 by omega) with hd | hd
  · subst δ
    rw [hsub, hLz]
    ring
  · subst δ
    rw [hsub, hLz]
    ring

#print axioms nonzero_class_twice_sum_identity
#print axioms zero_class_twice_sum_identity
end
end Li2Unified.Proofs.Hermite

end


end
