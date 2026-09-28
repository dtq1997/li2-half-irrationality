module
public import Li2Unified.Modular.Positive.Packed.P007

set_option backward.privateInPublic true

@[expose] public section

section
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section

theorem sum_fin_twice_weight (m : ℕ) (b : ℤ) :
    (∑ i : Fin m, (b + 2 * (i.val : ℤ))) =
      (m : ℤ) * b + (m : ℤ) * ((m : ℤ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      push_cast
      ring

#print axioms sum_fin_twice_weight
end
end Li2Unified.Proofs.Hermite

end

section
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ}

theorem generalIndexedRowTwiceWeight_sum (n : ℕ) :
    (∑ i : Fin (generalJetSize n p), generalIndexedRowTwiceWeight n p i) =
      ∑ a : Fin p,
        ((Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a : ℤ) *
            generalDiscBase n a +
          (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a : ℤ) *
            ((Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a : ℤ) - 1)) := by
  classical
  let w : generalJet n p → ℤ := fun x => generalDiscBase n x.1 + 2 * (x.2.val : ℤ)
  change (∑ i : Fin (generalJetSize n p), w (generalJetEquiv n p i)) = _
  rw [Equiv.sum_comp (generalJetEquiv n p) w]
  change (∑ x : Σ a : Fin p,
      Fin (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a), w x) = _
  rw [Fintype.sum_sigma]
  change (∑ a : Fin p,
      (∑ j : Fin (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a),
        w ⟨a, j⟩)) = _
  have hinner (a : Fin p) :
      (∑ j : Fin (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a),
          w ⟨a, j⟩) =
        (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a : ℤ) *
            generalDiscBase n a +
          (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a : ℤ) *
            ((Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a : ℤ) - 1) := by
    simpa only [w] using sum_fin_twice_weight
      (Li2Unified.Proofs.Hermite.CountsCore.multiplicity n p a) (generalDiscBase n a)
  simp only [hinner]

#print axioms generalIndexedRowTwiceWeight_sum
end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
open scoped BigOperators
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma generalClassTwiceWeight_sum (n : ℕ) (hpn : p ≤ n) (a : Fin p) :
    (CountsCore.multiplicity n p a : ℤ) * generalDiscBase n a +
      (CountsCore.multiplicity n p a : ℤ) * ((CountsCore.multiplicity n p a : ℤ)-1) +
      (if a.val = 0 then (CountsCore.delta n p : ℤ) * ((((3*n)/p:ℕ):ℤ)-1) else 0) =
    ((CountsCore.residueCount p (4*n) a:ℤ)-2*(CountsCore.residueCount p n a:ℤ)) *
      ((CountsCore.residueCount p n a:ℤ)-2) +
      (if a.val = 0 then ((((4*n)/p:ℕ):ℤ)-2*((n/p:ℕ):ℤ)) else 0) := by
  by_cases ha : a.val = 0
  · let z : Fin p := ⟨0,(Fact.out : p.Prime).pos⟩
    have haz : a = z := Fin.ext ha
    subst a
    have hN : CountsCore.residueCount p n z = n/p := matchingCount_zero n
    have hC : CountsCore.residueCount p (4*n) z = (4*n)/p := matchingCount_zero (4*n)
    have hm : CountsCore.multiplicity n p z = (3*n)/p-n/p := by
      simp [CountsCore.multiplicity,z]
    have hb : generalDiscBase n z = 3*((n/p:ℕ):ℤ)-(((4*n)/p:ℕ):ℤ) := by
      simp only [generalDiscBase, matchingCount_zero, z, if_true, sub_zero]
    have hA : n/p ≤ (3*n)/p := Nat.div_le_div_right (by omega)
    have hδ := general_delta_le_one n hpn
    have hL := generalDelta_floor_relation (p:=p) n
    have hsum := zero_class_twice_sum_identity (n/p) ((3*n)/p) ((4*n)/p)
      (CountsCore.delta n p) hA hL hδ
    dsimp only at hsum
    have htop : (CountsCore.delta n p:ℤ) *
        (3*((n/p:ℕ):ℤ)-(((4*n)/p:ℕ):ℤ)+2*((((3*n)/p-n/p:ℕ):ℤ))) =
        (CountsCore.delta n p:ℤ) * ((((3*n)/p:ℕ):ℤ)-1) := by
      rcases (show CountsCore.delta n p = 0 ∨ CountsCore.delta n p = 1 by omega) with hd | hd
      · simp [hd]
      · have h := (generalDiscTop_zero n hpn z rfl).2.2 hd
        rw [hb,hm] at h
        rw [h]
    rw [htop] at hsum
    simp only [hm,hb,hN,hC,z,if_true]
    nlinarith only [hsum]
  · have htwo := matchingCount_two_le_four n hpn a
    have h := nonzero_class_twice_sum_identity (matchingCount n p a)
      (matchingCount (4*n) p a) htwo
    simpa only [CountsCore.multiplicity, if_neg ha, generalDiscBase,
      if_neg ha, add_zero] using! h


private lemma sum_zero_class_indicator (v : ℤ) :
    (∑ a : Fin p, if a.val = 0 then v else 0) = v := by
  classical
  let z : Fin p := ⟨0,(Fact.out : p.Prime).pos⟩
  have he (a : Fin p) : a.val = 0 ↔ a = z := by
    constructor
    · intro h
      exact Fin.ext h
    · intro h
      rw [h]
  simp_rw [he]
  simp

lemma generalClassesTwiceWeight_sum (n : ℕ) (hpn : p ≤ n) :
    (∑ a : Fin p,
      ((CountsCore.multiplicity n p a : ℤ) * generalDiscBase n a +
       (CountsCore.multiplicity n p a : ℤ) * ((CountsCore.multiplicity n p a : ℤ)-1))) +
      (CountsCore.delta n p : ℤ) * ((((3*n)/p:ℕ):ℤ)-1) =
    (∑ a : Fin p,
      (((CountsCore.residueCount p (4*n) a:ℤ)-2*(CountsCore.residueCount p n a:ℤ)) *
       ((CountsCore.residueCount p n a:ℤ)-2))) +
      ((((4*n)/p:ℕ):ℤ)-2*((n/p:ℕ):ℤ)) := by
  classical
  have h := congrArg (fun f : Fin p → ℤ => ∑ a, f a)
    (funext (generalClassTwiceWeight_sum n hpn))
  simpa only [Finset.sum_add_distrib, sum_zero_class_indicator] using h

theorem generalOriginalRowTwiceWeight_sum (n : ℕ) (hpn : p ≤ n) :
    (∑ i : Fin (2*n), generalOriginalRowTwiceWeight n hpn i) =
    (∑ a : Fin p,
      (((CountsCore.residueCount p (4*n) a:ℤ)-2*(CountsCore.residueCount p n a:ℤ)) *
       ((CountsCore.residueCount p n a:ℤ)-2))) +
      ((((4*n)/p:ℕ):ℤ)-2*((n/p:ℕ):ℤ)) := by
  have hc := generalClassesTwiceWeight_sum n hpn
  have hsize := generalJetSize_add_delta n hpn
  by_cases hd : CountsCore.delta n p = 0
  · have he : 2*n = generalJetSize n p := by omega
    have hs : (∑ i : Fin (2*n), generalOriginalRowTwiceWeight n hpn i) =
        ∑ i : Fin (generalJetSize n p), generalIndexedRowTwiceWeight n p i := by
      simp only [generalOriginalRowTwiceWeight, dif_pos hd]
      exact Equiv.sum_comp (finCongr he) (generalIndexedRowTwiceWeight n p)
    rw [hs, generalIndexedRowTwiceWeight_sum]
    simpa only [hd, Nat.cast_zero, zero_mul, add_zero] using hc
  · have hd1 : CountsCore.delta n p = 1 := by
      have := general_delta_le_one n hpn
      omega
    have he : 2*n = generalJetSize n p+1 := by omega
    have hs : (∑ i : Fin (2*n), generalOriginalRowTwiceWeight n hpn i) =
        ∑ i : Fin (generalJetSize n p+1), generalAppendedRowTwiceWeight n i := by
      simp only [generalOriginalRowTwiceWeight, dif_neg hd]
      exact Equiv.sum_comp (finCongr he) (generalAppendedRowTwiceWeight n)
    rw [hs, Fin.sum_univ_succ]
    simp only [generalAppendedRowTwiceWeight, Fin.cases_zero, Fin.cases_succ]
    rw [generalIndexedRowTwiceWeight_sum]
    have hc' := hc
    rw [hd1, Nat.cast_one, one_mul] at hc'
    linarith only [hc']

end
end Li2Unified.Proofs.Hermite
#print axioms Li2Unified.Proofs.Hermite.generalClassTwiceWeight_sum
#print axioms Li2Unified.Proofs.Hermite.generalOriginalRowTwiceWeight_sum

end


end
