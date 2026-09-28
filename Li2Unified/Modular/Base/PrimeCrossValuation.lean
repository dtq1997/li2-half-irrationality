module
public import Li2Unified.Modular.Base.PrimeCubeValuationBridge
public import Li2Unified.Modular.Base.PrimeRemainingCrossBounds

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- The literal rational numerator entry in the original Fin ordering. -/
def primeOriginalNumeratorEntry (p : ℕ) (hp3 : 3 ≤ p)
    (I J : Fin (2*(p-1))) : ℚ[X] :=
  numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
    (primeOriginalBasis p hp3 I * primeOriginalBasis p hp3 J).map
      (Int.castRingHom ℚ))

lemma primeOriginalNumeratorEntry_symm (hp3 : 3 ≤ p)
    (I J : Fin (2*(p-1))) :
    primeOriginalNumeratorEntry p hp3 I J = primeOriginalNumeratorEntry p hp3 J I := by
  unfold primeOriginalNumeratorEntry
  rw [mul_comm (primeOriginalBasis p hp3 I) (primeOriginalBasis p hp3 J)]

lemma primeLow_index_margin (hp4 : 3 < p) (a : Fin p)
    (ha : a.val ≤ p-4) (i : Fin (primeMultiplicity p a)) :
    (1/2 : ℚ) ≤ 3/2-(i.val : ℚ) := by
  have hm := primeMultiplicity_low hp4 a ha
  have hi0 := i.isLt
  have hi : i.val ≤ 1 := by omega
  have hiq : (i.val : ℚ) ≤ 1 := by exact_mod_cast hi
  linarith

lemma GV.with_strict_margin {F : ℚ[X]} {w ε : ℚ}
    (h : GV p F (w+ε)) (hε : 0 < ε) :
    GV p F (w+ε) ∧
      ∀ n, F.coeff n = 0 ∨ w < (padicValRat p (F.coeff n) : ℚ) :=
  ⟨h, fun n => h.strict_coeff_of_margin hε n⟩

/-- Different low blocks; margin1. -/
theorem primeOriginalBasis_low_cross_GV_strict (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (hb0 : 0 < b.val) (hb : b.val ≤ p-4) (hab : a ≠ b)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) :
    GV p (primeOriginalNumeratorEntry p (by omega) I J) ((((i.val : ℚ)-1)+((j.val : ℚ)-1))+(1)) ∧
    ∀ n, (primeOriginalNumeratorEntry p (by omega) I J).coeff n = 0 ∨
      (((i.val : ℚ)-1)+((j.val : ℚ)-1)) < (padicValRat p ((primeOriginalNumeratorEntry p (by omega) I J).coeff n) : ℚ) := by
  refine GV.with_strict_margin ?_ (by norm_num)
  have h := GV_of_cube_padic_norm_bound (primeOriginalNumeratorEntry p (by omega) I J) (i.val+j.val+2)
    (primeOriginalBasis_low_cross_entry_bound hp4 I J a b ha0 ha hb0 hb hab i j hI hJ)
  exact h.mono (by push_cast <;> linarith)

/-- Low against zero; margin at least1/2. -/
theorem primeOriginalBasis_low_zero_GV_strict (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (hb0 : b.val = 0)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) :
    GV p (primeOriginalNumeratorEntry p (by omega) I J) ((((i.val : ℚ)-1)+((j.val : ℚ)-3/2))+(3/2-(i.val : ℚ))) ∧
    ∀ n, (primeOriginalNumeratorEntry p (by omega) I J).coeff n = 0 ∨
      (((i.val : ℚ)-1)+((j.val : ℚ)-3/2)) < (padicValRat p ((primeOriginalNumeratorEntry p (by omega) I J).coeff n) : ℚ) := by
  have hm := primeLow_index_margin hp4 a ha i
  refine GV.with_strict_margin ?_ (by linarith : (0 : ℚ) < 3/2-(i.val : ℚ))
  have h := GV_of_cube_padic_norm_bound (primeOriginalNumeratorEntry p (by omega) I J) (j.val+2)
    (primeOriginalBasis_low_zero_entry_bound hp4 I J a b ha0 ha hb0 i j hI hJ)
  exact h.mono (by push_cast <;> linarith)

/-- Low against high; margin at least1/2. -/
theorem primeOriginalBasis_low_high_GV_strict (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (hb : p-4 < b.val)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) :
    GV p (primeOriginalNumeratorEntry p (by omega) I J) ((((i.val : ℚ)-1)+(-1/2 : ℚ))+(3/2-(i.val : ℚ))) ∧
    ∀ n, (primeOriginalNumeratorEntry p (by omega) I J).coeff n = 0 ∨
      (((i.val : ℚ)-1)+(-1/2 : ℚ)) < (padicValRat p ((primeOriginalNumeratorEntry p (by omega) I J).coeff n) : ℚ) := by
  have hm := primeLow_index_margin hp4 a ha i
  refine GV.with_strict_margin ?_ (by linarith : (0 : ℚ) < 3/2-(i.val : ℚ))
  have h := GV_of_cube_padic_norm_bound (primeOriginalNumeratorEntry p (by omega) I J) (3)
    (primeOriginalBasis_low_high_entry_bound hp4 I J a b ha0 ha hb i j hI hJ)
  exact h.mono (by push_cast <;> linarith)

/-- Zero against high inside the six-dimensional block; margin1. -/
theorem primeOriginalBasis_zero_high_GV_strict (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : a.val = 0) (hb : p-4 < b.val)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) :
    GV p (primeOriginalNumeratorEntry p (by omega) I J) ((((i.val : ℚ)-3/2)+(-1/2 : ℚ))+(1)) ∧
    ∀ n, (primeOriginalNumeratorEntry p (by omega) I J).coeff n = 0 ∨
      (((i.val : ℚ)-3/2)+(-1/2 : ℚ)) < (padicValRat p ((primeOriginalNumeratorEntry p (by omega) I J).coeff n) : ℚ) := by
  refine GV.with_strict_margin ?_ (by norm_num)
  have h := GV_of_cube_padic_norm_bound (primeOriginalNumeratorEntry p (by omega) I J) (i.val+2)
    (primeOriginalBasis_zero_high_entry_bound hp4 I J a b ha0 hb i j hI hJ)
  exact h.mono (by push_cast <;> linarith)

/-- Distinct high jets inside the six-dimensional block; margin1. -/
theorem primeOriginalBasis_high_cross_GV_strict (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha : p-4 < a.val) (hb : p-4 < b.val) (hab : a ≠ b)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) :
    GV p (primeOriginalNumeratorEntry p (by omega) I J) (((-1/2 : ℚ)+(-1/2 : ℚ))+(1)) ∧
    ∀ n, (primeOriginalNumeratorEntry p (by omega) I J).coeff n = 0 ∨
      ((-1/2 : ℚ)+(-1/2 : ℚ)) < (padicValRat p ((primeOriginalNumeratorEntry p (by omega) I J).coeff n) : ℚ) := by
  refine GV.with_strict_margin ?_ (by norm_num)
  have h := GV_of_cube_padic_norm_bound (primeOriginalNumeratorEntry p (by omega) I J) (3)
    (primeOriginalBasis_high_cross_entry_bound hp4 I J a b ha hb hab i j hI hJ)
  exact h.mono (by push_cast <;> linarith)

/-- Top G against a low block, with weights1/2 and i-1; margin1/2. -/
theorem primeOriginalBasis_top_low_GV_strict (hp4 : 3 < p)
    (J : Fin (2*(p-1))) (a : Fin p) (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (i : Fin (primeMultiplicity p a))
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ) :
    GV p (primeOriginalNumeratorEntry p (by omega)
      (⟨0,by omega⟩ : Fin (2*(p-1))) J)
      ((1/2 : ℚ)+((i.val : ℚ)-1)+1/2) ∧
    ∀ n, (primeOriginalNumeratorEntry p (by omega)
      (⟨0,by omega⟩ : Fin (2*(p-1))) J).coeff n = 0 ∨
      (1/2 : ℚ)+((i.val : ℚ)-1) <
        (padicValRat p ((primeOriginalNumeratorEntry p (by omega)
          (⟨0,by omega⟩ : Fin (2*(p-1))) J).coeff n) : ℚ) := by
  refine GV.with_strict_margin ?_ (by norm_num)
  have h := GV_of_cube_padic_norm_bound
    (primeOriginalNumeratorEntry p (by omega)
      (⟨0,by omega⟩ : Fin (2*(p-1))) J) (i.val+3)
    (primeOriginalBasis_top_low_entry_bound hp4 J a ha0 ha i hJ)
  exact h.mono (by push_cast <;> linarith)

end
end Li2

end
