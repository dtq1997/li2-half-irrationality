module
public import Li2Unified.Modular.Positive.Packed.P064
public import Li2Unified.Modular.Positive.Packed.P057
public import Li2Unified.Modular.Base.PrimeZeroRationalLeading
public import Li2Unified.Modular.Positive.Packed.P053
public import Li2Unified.Modular.Positive.Packed.P062
public import Li2Unified.Modular.Positive.Packed.P063

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem parameterTop_fixed_entry_leading (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*
        (primeProduct p*primeProduct p).map (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p]) -
      C ((p:ℚ_[p])^4*((fixedCornerBlock lam 5 5:ℚ):ℚ_[p]))).coeff n‖ ≤ ‖(p:ℚ_[p])‖^5 := by
  let F := C ((p:ℚ_[p])^3)*
    (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*
      (primeProduct p*primeProduct p).map (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p])
  have hc : ∀ k, ‖(C (parameterTopLeadingSum (p := p) lam-((fixedCornerBlock lam 5 5:ℚ):ℚ_[p]))).coeff k‖ ≤ ‖(p:ℚ_[p])‖^1 := by
    intro k
    by_cases hk : k=0
    · subst k
      simpa using! parameterTopLeadingSum_norm (p := p) lam hu hone hferm hp4
    · simp [coeff_C,hk]
  have hnew := fieldPolynomial_prime_power_bound
    (C (parameterTopLeadingSum (p := p) lam-((fixedCornerBlock lam 5 5:ℚ):ℚ_[p]))) 4 1 hc n
  have he : F-C ((p:ℚ_[p])^4*((fixedCornerBlock lam 5 5:ℚ):ℚ_[p])) =
      (F-C ((p:ℚ_[p])^4*parameterTopLeadingSum (p := p) lam)) +
        C ((p:ℚ_[p])^4)*C (parameterTopLeadingSum (p := p) lam-((fixedCornerBlock lam 5 5:ℚ):ℚ_[p])) := by
    simp only [C_sub,C_mul]
    ring
  change ‖(F-C ((p:ℚ_[p])^4*((fixedCornerBlock lam 5 5:ℚ):ℚ_[p]))).coeff n‖ ≤ _
  rw [he,coeff_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (parameterTop_original_entry_leading lam hlam hu hone hferm hp4 n) hnew)

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterTop_fixed_entry_leading

end

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- The original highest-degree vector is unchanged by the unit normalization. -/
theorem parameterTop_block_scaled_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) :
    GV p (parameterNormalizedMatrix lam hp4 (Sum.inr 5) (Sum.inr 5) -
      C ((p:ℚ) * fixedCornerBlock lam 5 5))
      (primeBlockWeight (p := p) (Sum.inr 5) +
        primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  unfold parameterNormalizedMatrix
  rw [primeBlockUnitScale_top, one_mul, C_1, one_mul]
  unfold parameterOriginalNumeratorEntry
  rw [primeBlock_original_basis_top]
  have h := GV_of_cube_padic_leading_bound
    (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
      (primeProduct p*primeProduct p).map (Int.castRingHom ℚ)))
    (fixedCornerBlock lam 5 5) 4 (by
      intro n
      simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using!
        parameterTop_fixed_entry_leading lam hlam hu hone hferm hp4 n)
  rw [show primeBlockWeight (p := p) (Sum.inr 5) = (1/2:ℚ) from rfl]
  norm_num only [show (1/2:ℚ)+(1/2:ℚ)+1 = 2 by norm_num]
  simpa only [neg_div, show ((4:ℕ):ℤ)-3 = 1 by norm_num, zpow_one,
    show ((4:ℕ):ℚ)-2 = 2 by norm_num] using! h

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterTop_block_scaled_GV

end

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def parameterEntryReferenceMatrix (lam : ℚ) (p : ℕ) :
    Matrix (PrimeBlockIndex p) (PrimeBlockIndex p) ℚ[X] := fun x y =>
  match x,y with
  | Sum.inl (a,i), Sum.inl (b,j) =>
      if a = b then C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-2) *
        parameterLowRationalWeight lam (a.val+1) * Li2Unified.ParameterFamily.fixedLowBlock lam i j) else 0
  | Sum.inr k, Sum.inr l =>
      C ((p:ℚ)^(primeEdgeIntegerWeight k+primeEdgeIntegerWeight l+1)*fixedCornerBlock lam k l)
  | _,_ => 0

lemma parameterEntryReference_lowBlock_symm (lam : ℚ) (i j : Fin 2) : Li2Unified.ParameterFamily.fixedLowBlock lam i j = Li2Unified.ParameterFamily.fixedLowBlock lam j i := by
  fin_cases i <;> fin_cases j <;> rfl

lemma parameterEntryReference_edgeBlock_symm (lam : ℚ) (k l : Fin 6) : fixedCornerBlock lam k l = fixedCornerBlock lam l k :=
  Li2Unified.ParameterFamily.arrowSix_symm _ _ _ _ _ _ _ _ _ _ _ _ k l

lemma parameterEntryReferenceMatrix_symm (lam : ℚ) (x y : PrimeBlockIndex p) :
    parameterEntryReferenceMatrix lam p x y = parameterEntryReferenceMatrix lam p y x := by
  rcases x with ⟨a,i⟩ | k <;> rcases y with ⟨b,j⟩ | l
  · by_cases hab : a = b
    · subst b
      simp only [parameterEntryReferenceMatrix,if_pos rfl]
      rw [parameterEntryReference_lowBlock_symm lam i j,add_comm (i.val:ℤ) (j.val:ℤ)]
    · simp only [parameterEntryReferenceMatrix,if_neg hab,if_neg (Ne.symm hab)]
  · rfl
  · rfl
  · simp only [parameterEntryReferenceMatrix]
    rw [parameterEntryReference_edgeBlock_symm lam k l,
      add_comm (primeEdgeIntegerWeight k) (primeEdgeIntegerWeight l)]

lemma parameterEntryReference_GV_swap (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) {x y : PrimeBlockIndex p} {δ : ℚ}
    (h : GV p (parameterNormalizedMatrix lam hp4 x y-parameterEntryReferenceMatrix lam p x y)
      (primeBlockWeight x+primeBlockWeight y+δ)) :
    GV p (parameterNormalizedMatrix lam hp4 y x-parameterEntryReferenceMatrix lam p y x)
      (primeBlockWeight y+primeBlockWeight x+δ) := by
  rw [parameterNormalizedMatrix_symm lam hp4 y x,parameterEntryReferenceMatrix_symm lam y x]
  simpa only [add_comm] using! h

lemma parameterEntryReference_high_cross_zero (lam : ℚ) (ell m : Fin 3) (hem : ell ≠ m) :
    fixedCornerBlock lam (primeHighEdgeSlot ell) (primeHighEdgeSlot m) = 0 := by
  fin_cases ell <;> fin_cases m <;> norm_num [primeHighEdgeSlot,fixedCornerBlock,Li2Unified.ParameterFamily.arrowSix] at *

lemma parameterEntryReference_zero_high_zero (lam : ℚ) (i : Fin 2) (ell : Fin 3) :
    fixedCornerBlock lam (primeZeroEdgeSlot i) (primeHighEdgeSlot ell) = 0 := by
  fin_cases i <;> fin_cases ell <;> rfl

theorem parameterEntryReference_low_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p)
    (a b : Fin (p-4)) (i j : Fin 2) :
    GV p (parameterNormalizedMatrix lam hp4 (Sum.inl (a,i)) (Sum.inl (b,j)) -
      parameterEntryReferenceMatrix lam p (Sum.inl (a,i)) (Sum.inl (b,j)))
      (primeBlockWeight (p := p) (Sum.inl (a,i)) +
        primeBlockWeight (p := p) (Sum.inl (b,j)) + 1) := by
  by_cases hab : a = b
  · subst b
    simpa only [parameterNormalizedMatrix,parameterEntryReferenceMatrix,if_pos rfl] using!
      parameterLow_block_scaled_GV lam hlam hu hone hferm hp4 a i j
  · simpa only [parameterEntryReferenceMatrix,if_neg hab,sub_zero] using!
      parameterNormalizedMatrix_low_cross_GV lam hlam hu hone hferm hp4 a b i j hab

theorem parameterEntryReference_low_edge_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p)
    (a : Fin (p-4)) (i : Fin 2) (k : Fin 6) :
    GV p (parameterNormalizedMatrix lam hp4 (Sum.inl (a,i)) (Sum.inr k) -
      parameterEntryReferenceMatrix lam p (Sum.inl (a,i)) (Sum.inr k))
      (primeBlockWeight (p := p) (Sum.inl (a,i)) +
        primeBlockWeight (p := p) (Sum.inr k) + 1/2) := by
  simpa only [parameterEntryReferenceMatrix,sub_zero] using!
    parameterNormalizedMatrix_low_edge_GV lam hlam hu hone hferm hp4 a i k

theorem parameterEntryReference_high_high_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (ell m : Fin 3) :
    GV p (parameterNormalizedMatrix lam hp4
      (Sum.inr (primeHighEdgeSlot ell)) (Sum.inr (primeHighEdgeSlot m)) -
      parameterEntryReferenceMatrix lam p (Sum.inr (primeHighEdgeSlot ell)) (Sum.inr (primeHighEdgeSlot m)))
      (primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
        primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot m)) + 1) := by
  by_cases hem : ell = m
  · subst m
    have he : primeEdgeIntegerWeight (primeHighEdgeSlot ell) +
        primeEdgeIntegerWeight (primeHighEdgeSlot ell) + 1 = -1 := by
      norm_num [primeEdgeIntegerWeight_highSlot]
    simpa only [parameterNormalizedMatrix,parameterEntryReferenceMatrix,he] using! parameterHigh_pair_block_scaled_GV lam hlam hu hone hferm hp4 ell
  · simpa only [parameterEntryReferenceMatrix,parameterEntryReference_high_cross_zero lam ell m hem,
      mul_zero,C_0,sub_zero] using! parameterNormalizedMatrix_high_cross_GV lam hlam hu hone hferm hp4 ell m hem

theorem parameterEntryReference_zero_high_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (i : Fin 2) (ell : Fin 3) :
    GV p (parameterNormalizedMatrix lam hp4
      (Sum.inr (primeZeroEdgeSlot i)) (Sum.inr (primeHighEdgeSlot ell)) -
      parameterEntryReferenceMatrix lam p (Sum.inr (primeZeroEdgeSlot i)) (Sum.inr (primeHighEdgeSlot ell)))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) + 1) := by
  simpa only [parameterEntryReferenceMatrix,parameterEntryReference_zero_high_zero lam,
    mul_zero,C_0,sub_zero] using! parameterNormalizedMatrix_zero_high_GV lam hlam hu hone hferm hp4 i ell

theorem parameterEntryReference_zero_zero_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (i j : Fin 2) :
    GV p (parameterNormalizedMatrix lam hp4
      (Sum.inr (primeZeroEdgeSlot i)) (Sum.inr (primeZeroEdgeSlot j)) -
      parameterEntryReferenceMatrix lam p (Sum.inr (primeZeroEdgeSlot i)) (Sum.inr (primeZeroEdgeSlot j)))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot j)) + 1) := by
  have he : primeEdgeIntegerWeight (primeZeroEdgeSlot i) +
      primeEdgeIntegerWeight (primeZeroEdgeSlot j) + 1 = (i.val:ℤ)+(j.val:ℤ)-3 := by
    rw [primeEdgeIntegerWeight_zeroSlot,primeEdgeIntegerWeight_zeroSlot]
    ring
  simpa only [parameterNormalizedMatrix,parameterEntryReferenceMatrix,he] using!
    parameterZero_pair_block_scaled_GV lam hlam hu hone hferm hp4 i j

theorem parameterEntryReference_high_top_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (ell : Fin 3) :
    GV p (parameterNormalizedMatrix lam hp4 (Sum.inr (primeHighEdgeSlot ell)) (Sum.inr 5) -
      parameterEntryReferenceMatrix lam p (Sum.inr (primeHighEdgeSlot ell)) (Sum.inr 5))
      (primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
        primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  have he : primeEdgeIntegerWeight (primeHighEdgeSlot ell) +
      primeEdgeIntegerWeight 5 + 1 = 0 := by
    rw [primeEdgeIntegerWeight_highSlot, show primeEdgeIntegerWeight 5 = 0 from rfl]
    norm_num
  simpa only [parameterNormalizedMatrix,parameterEntryReferenceMatrix,he,zpow_zero,one_mul] using!
    parameterHigh_top_block_scaled_GV lam hlam hu hone hferm hp4 ell

theorem parameterEntryReference_zero_top_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (i : Fin 2) :
    GV p (parameterNormalizedMatrix lam hp4 (Sum.inr (primeZeroEdgeSlot i)) (Sum.inr 5) -
      parameterEntryReferenceMatrix lam p (Sum.inr (primeZeroEdgeSlot i)) (Sum.inr 5))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  have he : primeEdgeIntegerWeight (primeZeroEdgeSlot i) +
      primeEdgeIntegerWeight 5 + 1 = (i.val:ℤ)-1 := by
    rw [primeEdgeIntegerWeight_zeroSlot,show primeEdgeIntegerWeight 5 = 0 from rfl]
    ring
  simpa only [parameterNormalizedMatrix,parameterEntryReferenceMatrix,he] using!
    parameterZero_top_block_scaled_GV lam hlam hu hone hferm hp4 i

theorem parameterEntryReference_top_top_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) :
    GV p (parameterNormalizedMatrix lam hp4 (Sum.inr 5) (Sum.inr 5) -
      parameterEntryReferenceMatrix lam p (Sum.inr 5) (Sum.inr 5))
      (primeBlockWeight (p := p) (Sum.inr 5) + primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  have he : primeEdgeIntegerWeight 5+primeEdgeIntegerWeight 5+1 = 1 := by
    rw [show primeEdgeIntegerWeight 5 = 0 from rfl]
    norm_num
  simpa only [parameterEntryReferenceMatrix,he,zpow_one] using! parameterTop_block_scaled_GV lam hlam hu hone hferm hp4

theorem parameterEntryReference_edge_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (k l : Fin 6) :
    GV p (parameterNormalizedMatrix lam hp4 (Sum.inr k) (Sum.inr l) -
      parameterEntryReferenceMatrix lam p (Sum.inr k) (Sum.inr l))
      (primeBlockWeight (p := p) (Sum.inr k) + primeBlockWeight (p := p) (Sum.inr l) + 1) := by
  rcases primeEdgeSlot_cases k with ⟨ell,rfl⟩ | ⟨i,rfl⟩ | rfl
  · rcases primeEdgeSlot_cases l with ⟨m,rfl⟩ | ⟨j,rfl⟩ | rfl
    · exact parameterEntryReference_high_high_GV lam hlam hu hone hferm hp4 ell m
    · exact parameterEntryReference_GV_swap lam hlam hu hone hferm hp4 (parameterEntryReference_zero_high_GV lam hlam hu hone hferm hp4 j ell)
    · exact parameterEntryReference_high_top_GV lam hlam hu hone hferm hp4 ell
  · rcases primeEdgeSlot_cases l with ⟨m,rfl⟩ | ⟨j,rfl⟩ | rfl
    · exact parameterEntryReference_zero_high_GV lam hlam hu hone hferm hp4 i m
    · exact parameterEntryReference_zero_zero_GV lam hlam hu hone hferm hp4 i j
    · exact parameterEntryReference_zero_top_GV lam hlam hu hone hferm hp4 i
  · rcases primeEdgeSlot_cases l with ⟨m,rfl⟩ | ⟨j,rfl⟩ | rfl
    · exact parameterEntryReference_GV_swap lam hlam hu hone hferm hp4 (parameterEntryReference_high_top_GV lam hlam hu hone hferm hp4 m)
    · exact parameterEntryReference_GV_swap lam hlam hu hone hferm hp4 (parameterEntryReference_zero_top_GV lam hlam hu hone hferm hp4 j)
    · exact parameterEntryReference_top_top_GV lam hlam hu hone hferm hp4

theorem parameterEntryReference_entry_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (x y : PrimeBlockIndex p) :
    GV p (parameterNormalizedMatrix lam hp4 x y-parameterEntryReferenceMatrix lam p x y)
      (primeBlockWeight x+primeBlockWeight y+1/2) := by
  rcases x with ⟨a,i⟩ | k <;> rcases y with ⟨b,j⟩ | l
  · exact (parameterEntryReference_low_GV lam hlam hu hone hferm hp4 a b i j).mono (by linarith)
  · exact parameterEntryReference_low_edge_GV lam hlam hu hone hferm hp4 a i l
  · exact parameterEntryReference_GV_swap lam hlam hu hone hferm hp4 (parameterEntryReference_low_edge_GV lam hlam hu hone hferm hp4 b j k)
  · exact (parameterEntryReference_edge_GV lam hlam hu hone hferm hp4 k l).mono (by linarith)

theorem parameterEntryReference_literal (lam : ℚ) (p : ℕ)
    (x y : PrimeBlockIndex p) :
    parameterEntryReferenceMatrix lam p x y = C ((p:ℚ)^
      (primeReferenceRowExponent x + primeReferenceColExponent y) *
      (match x,y with
       | Sum.inl ai, Sum.inl bi => if ai.1=bi.1 then
           parameterLowRationalWeight lam (ai.1.val+1) *
             Li2Unified.ParameterFamily.fixedLowBlock lam ai.2 bi.2 else 0
       | Sum.inr i, Sum.inr j => fixedCornerBlock lam i j
       | _,_ => 0)) := by
  rcases x with ⟨a,i⟩ | k <;> rcases y with ⟨b,j⟩ | l
  · by_cases hab : a=b
    · subst b
      simp only [parameterEntryReferenceMatrix, ↓reduceIte,
        primeReferenceRowExponent,primeReferenceColExponent]
      rw [show (i.val:ℤ)-1+((j.val:ℤ)-1) = (i.val:ℤ)+(j.val:ℤ)-2 by ring]
      congr 1
      ring
    · simp [parameterEntryReferenceMatrix,hab]
  · simp [parameterEntryReferenceMatrix]
  · simp [parameterEntryReferenceMatrix]
  · simp only [parameterEntryReferenceMatrix,primeReferenceRowExponent,primeReferenceColExponent]
    rw [show primeEdgeIntegerWeight k+(primeEdgeIntegerWeight l+1) =
      primeEdgeIntegerWeight k+primeEdgeIntegerWeight l+1 by ring]

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterEntryReference_entry_GV

#print axioms Li2Unified.Proofs.PrimeEdge.parameterEntryReference_literal

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem parameterEntryReference_eq_reference (lam : ℚ) (x y : PrimeBlockIndex p) :
    parameterEntryReferenceMatrix lam p x y =
      parameterReferenceMatrix lam p (fixedCornerBlock lam) x y := by
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [parameterEntryReference_literal]
  unfold parameterReferenceMatrix
  rw [← mul_assoc, ← zpow_add₀ hpq]
  congr 2
  rcases x with ⟨a,i⟩ | k <;> rcases y with ⟨b,j⟩ | l <;>
    simp only [parameterReferenceCore, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, parameterLowCore_apply, parameterLowWeight,
      parameterLowRationalWeight]

theorem parameterNormalizedMatrix_reference_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (x y : PrimeBlockIndex p) :
    GV p (parameterNormalizedMatrix lam hp4 x y -
      parameterReferenceMatrix lam p (fixedCornerBlock lam) x y)
      (primeBlockWeight x + primeBlockWeight y + 1/2) := by
  rw [← parameterEntryReference_eq_reference]
  exact parameterEntryReference_entry_GV lam hlam hu hone hferm hp4 x y

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterEntryReference_eq_reference
#print axioms Li2Unified.Proofs.PrimeEdge.parameterNormalizedMatrix_reference_GV

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
open Li2Unified.ParameterFamily
variable {p : ℕ} [hp : Fact p.Prime]

theorem parameterReferenceMatrix_GV_of_block_bounds (lam : ℚ)
    (corner : Matrix (Fin 6) (Fin 6) ℚ) (hp4 : 3 < p)
    (hlam : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hlow : ∀ i j, VG p (fixedLowBlock lam i j) 0)
    (hcorner : ∀ i j, VG p (corner i j) 0)
    (x y : PrimeBlockIndex p) :
    GV p (parameterReferenceMatrix lam p corner x y)
      (primeBlockWeight x+primeBlockWeight y) := by
  rcases x with ⟨a,i⟩ | k <;> rcases y with ⟨b,j⟩ | l
  · by_cases hab : a = b
    · subst b
      simp only [parameterReferenceMatrix, parameterReferenceCore,
        Matrix.fromBlocks_apply₁₁, parameterLowCore_apply, if_pos rfl]
      have ha := a.isLt
      have hu := parameterLowWeight_unit lam hp4 hlam (a.val+1) (by omega) (by omega)
      have hw : VG p (parameterLowWeight lam (a.val+1)) 0 := by
        right
        rw [hu.2]
        norm_num
      have h := GV.C ((VG.primePow (p := p) (primeReferenceRowExponent (Sum.inl (a,i)))).mul
        ((VG.primePow (p := p) (primeReferenceColExponent (Sum.inl (a,j)))).mul (hw.mul (hlow i j))))
      convert h using 1 <;>
        simp only [primeBlockWeight_low, primeReferenceRowExponent, primeReferenceColExponent] <;>
        push_cast <;> ring
    · simp only [parameterReferenceMatrix, parameterReferenceCore,
        Matrix.fromBlocks_apply₁₁, parameterLowCore_apply, if_neg hab, mul_zero, C_0]
      exact GV.zero _
  · simp only [parameterReferenceMatrix, parameterReferenceCore,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, mul_zero, C_0]
    exact GV.zero _
  · simp only [parameterReferenceMatrix, parameterReferenceCore,
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, C_0]
    exact GV.zero _
  · simp only [parameterReferenceMatrix, parameterReferenceCore, Matrix.fromBlocks_apply₂₂]
    have h := GV.C ((VG.primePow (p := p) (primeReferenceRowExponent (p := p) (Sum.inr k))).mul
      ((VG.primePow (p := p) (primeReferenceColExponent (p := p) (Sum.inr l))).mul (hcorner k l)))
    convert h using 1 <;>
      simp only [primeBlockWeight_edge, primeReferenceRowExponent, primeReferenceColExponent] <;>
      push_cast <;> ring

end
end Li2Unified.Proofs.PrimeEdge

#print axioms Li2Unified.Proofs.PrimeEdge.parameterReferenceMatrix_GV_of_block_bounds

end

end
