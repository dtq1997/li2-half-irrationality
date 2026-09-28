module
public import Li2Unified.Modular.Base.PrimeCrossDiscBounds

set_option backward.privateInPublic true

@[expose] public section

/-! Zero/high and distinct-high pairs are zero entries inside the
six-dimensional augmented block. Low/zero and low/high cross distinct blocks. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma primeDistinctJet_cube_order (hp4 : 3 < p) (a b : PrimeJet p)
    (hab : a.1 ≠ b.1) (k : ℕ)
    (ha : k ≤ a.2.val+primeMultiplicity p a.1+primeDiscCubeGain a.1)
    (hb : k ≤ b.2.val+primeMultiplicity p b.1+primeDiscCubeGain b.1)
    (hk : k ≤ 4) (c : Fin p) :
    k ≤ primeJetLocalOrder p a c+primeJetLocalOrder p b c+primeDiscCubeGain c := by
  by_cases hca : c = a.1
  · subst c
    simpa only [primeJetLocalOrder,ite_true,if_pos rfl,if_neg hab] using! ha
  · by_cases hcb : c = b.1
    · subst c
      simpa only [primeJetLocalOrder,ite_true,if_neg (Ne.symm hab),if_pos rfl,
        Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using! hb
    · simp only [primeJetLocalOrder,ite_true,if_neg hca,if_neg hcb]
      apply hk.trans
      by_cases hz : c.val = 0
      · have hm : primeMultiplicity p c = 2 := primeMultiplicity_low hp4 c (by omega)
        simp only [hm,primeDiscCubeGain,if_pos hz] <;> omega
      · by_cases hl : c.val ≤ p-4
        · simp only [primeMultiplicity_low hp4 c hl,primeDiscCubeGain,if_neg hz,if_pos hl] <;> omega
        · have hm : primeMultiplicity p c = 1 := by
            unfold primeMultiplicity
            rw [if_neg (by omega)]
          simp only [hm,primeDiscCubeGain,if_neg hz,if_neg hl] <;> omega

theorem primeDistinctJet_original_cube_bound (hp4 : 3 < p) (a b : PrimeJet p)
    (hab : a.1 ≠ b.1) (k : ℕ)
    (ha : k ≤ a.2.val+primeMultiplicity p a.1+primeDiscCubeGain a.1)
    (hb : k ≤ b.2.val+primeMultiplicity p b.1+primeDiscCubeGain b.1)
    (hk : k ≤ 4) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*
        (primeJetPoly p a*primeJetPoly p b).map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^k := by
  apply primeNumerator_cube_bound_of_disc_bounds hp4 _ k
  intro c l
  have h := primeDiscContribution_cube_factor_bound hp4 _ c _
    (primeJet_pair_disc_factor a b c) l
  exact h.trans (pow_le_pow_of_le_one (norm_nonneg _)
    (PadicInt.norm_le_one (p:ℤ_[p])) (primeDistinctJet_cube_order hp4 a b hab k ha hb hk c))

theorem primeOriginalBasis_distinct_jet_cube_bound (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : PrimeJet p)
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm a).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm b).succ)
    (hab : a.1 ≠ b.1) (k : ℕ)
    (ha : k ≤ a.2.val+primeMultiplicity p a.1+primeDiscCubeGain a.1)
    (hb : k ≤ b.2.val+primeMultiplicity p b.1+primeDiscCubeGain b.1)
    (hk : k ≤ 4) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*
        (primeOriginalBasis p (by omega) I*primeOriginalBasis p (by omega) J).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^k := by
  rw [primeOriginalBasis_eq_jet_of_index (by omega) I a hI,
    primeOriginalBasis_eq_jet_of_index (by omega) J b hJ]
  exact primeDistinctJet_original_cube_bound hp4 a b hab k ha hb hk n

/-- Low_i versus zero_j: cube order j+2; strict raw margin 3/2-i. -/
theorem primeOriginalBasis_low_zero_entry_bound (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (hb0 : b.val = 0)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*
        (primeOriginalBasis p (by omega) I*primeOriginalBasis p (by omega) J).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p])).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(j.val+2) := by
  have hmA := primeMultiplicity_low hp4 a ha
  have hmB : primeMultiplicity p b = 2 := primeMultiplicity_low hp4 b (by omega)
  have hj : j.val ≤ 1 := by
    have h := j.isLt
    omega
  have hab : a ≠ b := by
    intro he
    have he' := congrArg Fin.val he
    omega
  refine primeOriginalBasis_distinct_jet_cube_bound hp4 I J ⟨a,i⟩ ⟨b,j⟩
    hI hJ hab (j.val+2) ?_ ?_ ?_ n
  · simp only [hmA,primeDiscCubeGain,if_neg ha0.ne',if_pos ha] <;> omega
  · simp only [hmB,primeDiscCubeGain,if_pos hb0] <;> omega
  · omega

/-- Low_i versus high: cube order 3; strict raw margin 3/2-i. -/
theorem primeOriginalBasis_low_high_entry_bound (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (hb : p-4 < b.val)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*
        (primeOriginalBasis p (by omega) I*primeOriginalBasis p (by omega) J).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p])).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^3 := by
  have hmA := primeMultiplicity_low hp4 a ha
  have hmB : primeMultiplicity p b = 1 := by
    unfold primeMultiplicity
    rw [if_neg (by omega)]
  have hj : j.val = 0 := by
    have h := j.isLt
    omega
  have hab : a ≠ b := by
    intro he
    have he' := congrArg Fin.val he
    omega
  refine primeOriginalBasis_distinct_jet_cube_bound hp4 I J ⟨a,i⟩ ⟨b,j⟩
    hI hJ hab 3 ?_ ?_ ?_ n
  · simp only [hmA,primeDiscCubeGain,if_neg ha0.ne',if_pos ha] <;> omega
  · simp only [hj,hmB,primeDiscCubeGain,if_neg (by omega : b.val ≠ 0),
      if_neg (by omega : ¬ b.val ≤ p-4)] <;> omega
  · omega

/-- Zero_i versus high: one full order above the row-weight sum. -/
theorem primeOriginalBasis_zero_high_entry_bound (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : a.val = 0) (hb : p-4 < b.val)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*
        (primeOriginalBasis p (by omega) I*primeOriginalBasis p (by omega) J).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p])).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+2) := by
  have hmA : primeMultiplicity p a = 2 := primeMultiplicity_low hp4 a (by omega)
  have hmB : primeMultiplicity p b = 1 := by
    unfold primeMultiplicity
    rw [if_neg (by omega)]
  have hi : i.val ≤ 1 := by
    have h := i.isLt
    omega
  have hj : j.val = 0 := by
    have h := j.isLt
    omega
  have hab : a ≠ b := by
    intro he
    have he' := congrArg Fin.val he
    omega
  refine primeOriginalBasis_distinct_jet_cube_bound hp4 I J ⟨a,i⟩ ⟨b,j⟩
    hI hJ hab (i.val+2) ?_ ?_ ?_ n
  · simp only [hmA,primeDiscCubeGain,if_pos ha0] <;> omega
  · simp only [hj,hmB,primeDiscCubeGain,if_neg (by omega : b.val ≠ 0),
      if_neg (by omega : ¬ b.val ≤ p-4)] <;> omega
  · omega

/-- Two distinct high jets: one full order above the weight sum. -/
theorem primeOriginalBasis_high_cross_entry_bound (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha : p-4 < a.val) (hb : p-4 < b.val) (hab : a ≠ b)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (numeratorFunctional (4*(p-1)) ((D (p-1))^3*
        (primeOriginalBasis p (by omega) I*primeOriginalBasis p (by omega) J).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p])).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^3 := by
  have hmA : primeMultiplicity p a = 1 := by
    unfold primeMultiplicity
    rw [if_neg (by omega)]
  have hmB : primeMultiplicity p b = 1 := by
    unfold primeMultiplicity
    rw [if_neg (by omega)]
  have hi : i.val = 0 := by
    have h := i.isLt
    omega
  have hj : j.val = 0 := by
    have h := j.isLt
    omega
  refine primeOriginalBasis_distinct_jet_cube_bound hp4 I J ⟨a,i⟩ ⟨b,j⟩
    hI hJ hab 3 ?_ ?_ ?_ n
  · simp only [hi,hmA,primeDiscCubeGain,if_neg (by omega : a.val ≠ 0),
      if_neg (by omega : ¬ a.val ≤ p-4)] <;> omega
  · simp only [hj,hmB,primeDiscCubeGain,if_neg (by omega : b.val ≠ 0),
      if_neg (by omega : ¬ b.val ≤ p-4)] <;> omega
  · omega

end
end Li2

end
