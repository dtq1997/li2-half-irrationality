module
public import Li2Unified.Modular.Base.PrimeNormalizedCrossBlock
public import Li2Unified.Modular.Base.PrimeLowScaledBlock
public import Li2Unified.Modular.Base.PrimeTopScaledBlock

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def primeReferenceMatrix (p : ℕ) :
    Matrix (PrimeBlockIndex p) (PrimeBlockIndex p) ℚ[X] := fun x y =>
  match x,y with
  | Sum.inl (a,i), Sum.inl (b,j) =>
      if a = b then C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-2) *
        primeLowRationalWeight (a.val+1) * lowBlock i j) else 0
  | Sum.inr k, Sum.inr l =>
      C ((p:ℚ)^(primeEdgeIntegerWeight k+primeEdgeIntegerWeight l+1)*edgeBlock k l)
  | _,_ => 0

lemma primeReference_lowBlock_symm (i j : Fin 2) : lowBlock i j = lowBlock j i := by
  fin_cases i <;> fin_cases j <;> rfl

lemma primeReference_edgeBlock_symm (k l : Fin 6) : edgeBlock k l = edgeBlock l k := by
  fin_cases k <;> fin_cases l <;> rfl

lemma primeReferenceMatrix_symm (x y : PrimeBlockIndex p) :
    primeReferenceMatrix p x y = primeReferenceMatrix p y x := by
  rcases x with ⟨a,i⟩ | k <;> rcases y with ⟨b,j⟩ | l
  · by_cases hab : a = b
    · subst b
      simp only [primeReferenceMatrix,if_pos rfl]
      rw [primeReference_lowBlock_symm i j,add_comm (i.val:ℤ) (j.val:ℤ)]
    · simp only [primeReferenceMatrix,if_neg hab,if_neg (Ne.symm hab)]
  · rfl
  · rfl
  · simp only [primeReferenceMatrix]
    rw [primeReference_edgeBlock_symm k l,
      add_comm (primeEdgeIntegerWeight k) (primeEdgeIntegerWeight l)]

lemma primeReference_GV_swap (hp4 : 3 < p) {x y : PrimeBlockIndex p} {δ : ℚ}
    (h : GV p (primeNormalizedMatrix hp4 x y-primeReferenceMatrix p x y)
      (primeBlockWeight x+primeBlockWeight y+δ)) :
    GV p (primeNormalizedMatrix hp4 y x-primeReferenceMatrix p y x)
      (primeBlockWeight y+primeBlockWeight x+δ) := by
  rw [primeNormalizedMatrix_symm hp4 y x,primeReferenceMatrix_symm y x]
  simpa only [add_comm] using h

lemma primeReference_high_cross_zero (ell m : Fin 3) (hem : ell ≠ m) :
    edgeBlock (primeHighEdgeSlot ell) (primeHighEdgeSlot m) = 0 := by
  fin_cases ell <;> fin_cases m <;> norm_num [primeHighEdgeSlot,edgeBlock] at *

lemma primeReference_zero_high_zero (i : Fin 2) (ell : Fin 3) :
    edgeBlock (primeZeroEdgeSlot i) (primeHighEdgeSlot ell) = 0 := by
  fin_cases i <;> fin_cases ell <;> rfl

theorem primeReference_low_GV (hp4 : 3 < p)
    (a b : Fin (p-4)) (i j : Fin 2) :
    GV p (primeNormalizedMatrix hp4 (Sum.inl (a,i)) (Sum.inl (b,j)) -
      primeReferenceMatrix p (Sum.inl (a,i)) (Sum.inl (b,j)))
      (primeBlockWeight (p := p) (Sum.inl (a,i)) +
        primeBlockWeight (p := p) (Sum.inl (b,j)) + 1) := by
  by_cases hab : a = b
  · subst b
    simpa only [primeNormalizedMatrix,primeReferenceMatrix,if_pos rfl] using
      primeLow_block_scaled_GV hp4 a i j
  · simpa only [primeReferenceMatrix,if_neg hab,sub_zero] using
      primeNormalizedMatrix_low_cross_GV hp4 a b i j hab

theorem primeReference_low_edge_GV (hp4 : 3 < p)
    (a : Fin (p-4)) (i : Fin 2) (k : Fin 6) :
    GV p (primeNormalizedMatrix hp4 (Sum.inl (a,i)) (Sum.inr k) -
      primeReferenceMatrix p (Sum.inl (a,i)) (Sum.inr k))
      (primeBlockWeight (p := p) (Sum.inl (a,i)) +
        primeBlockWeight (p := p) (Sum.inr k) + 1/2) := by
  simpa only [primeReferenceMatrix,sub_zero] using
    primeNormalizedMatrix_low_edge_GV hp4 a i k

theorem primeReference_high_high_GV (hp4 : 3 < p) (ell m : Fin 3) :
    GV p (primeNormalizedMatrix hp4
      (Sum.inr (primeHighEdgeSlot ell)) (Sum.inr (primeHighEdgeSlot m)) -
      primeReferenceMatrix p (Sum.inr (primeHighEdgeSlot ell)) (Sum.inr (primeHighEdgeSlot m)))
      (primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
        primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot m)) + 1) := by
  by_cases hem : ell = m
  · subst m
    have he : primeEdgeIntegerWeight (primeHighEdgeSlot ell) +
        primeEdgeIntegerWeight (primeHighEdgeSlot ell) + 1 = -1 := by
      norm_num [primeEdgeIntegerWeight_highSlot]
    simpa only [primeReferenceMatrix,he] using primeNormalizedMatrix_high_diag_GV hp4 ell
  · simpa only [primeReferenceMatrix,primeReference_high_cross_zero ell m hem,
      mul_zero,C_0,sub_zero] using primeNormalizedMatrix_high_cross_GV hp4 ell m hem

theorem primeReference_zero_high_GV (hp4 : 3 < p) (i : Fin 2) (ell : Fin 3) :
    GV p (primeNormalizedMatrix hp4
      (Sum.inr (primeZeroEdgeSlot i)) (Sum.inr (primeHighEdgeSlot ell)) -
      primeReferenceMatrix p (Sum.inr (primeZeroEdgeSlot i)) (Sum.inr (primeHighEdgeSlot ell)))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) + 1) := by
  simpa only [primeReferenceMatrix,primeReference_zero_high_zero,
    mul_zero,C_0,sub_zero] using primeNormalizedMatrix_zero_high_GV hp4 i ell

theorem primeReference_zero_zero_GV (hp4 : 3 < p) (i j : Fin 2) :
    GV p (primeNormalizedMatrix hp4
      (Sum.inr (primeZeroEdgeSlot i)) (Sum.inr (primeZeroEdgeSlot j)) -
      primeReferenceMatrix p (Sum.inr (primeZeroEdgeSlot i)) (Sum.inr (primeZeroEdgeSlot j)))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot j)) + 1) := by
  have he : primeEdgeIntegerWeight (primeZeroEdgeSlot i) +
      primeEdgeIntegerWeight (primeZeroEdgeSlot j) + 1 = (i.val:ℤ)+(j.val:ℤ)-3 := by
    rw [primeEdgeIntegerWeight_zeroSlot,primeEdgeIntegerWeight_zeroSlot]
    ring
  simpa only [primeNormalizedMatrix,primeReferenceMatrix,he] using
    primeZero_pair_block_scaled_GV hp4 i j

theorem primeReference_high_top_GV (hp4 : 3 < p) (ell : Fin 3) :
    GV p (primeNormalizedMatrix hp4 (Sum.inr (primeHighEdgeSlot ell)) (Sum.inr 5) -
      primeReferenceMatrix p (Sum.inr (primeHighEdgeSlot ell)) (Sum.inr 5))
      (primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
        primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  have he : primeEdgeIntegerWeight (primeHighEdgeSlot ell) +
      primeEdgeIntegerWeight 5 + 1 = 0 := by
    rw [primeEdgeIntegerWeight_highSlot, show primeEdgeIntegerWeight 5 = 0 from rfl]
    norm_num
  simpa only [primeReferenceMatrix,he,zpow_zero,one_mul] using
    primeNormalizedMatrix_high_top_GV hp4 ell

theorem primeReference_zero_top_GV (hp4 : 3 < p) (i : Fin 2) :
    GV p (primeNormalizedMatrix hp4 (Sum.inr (primeZeroEdgeSlot i)) (Sum.inr 5) -
      primeReferenceMatrix p (Sum.inr (primeZeroEdgeSlot i)) (Sum.inr 5))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  have he : primeEdgeIntegerWeight (primeZeroEdgeSlot i) +
      primeEdgeIntegerWeight 5 + 1 = (i.val:ℤ)-1 := by
    rw [primeEdgeIntegerWeight_zeroSlot,show primeEdgeIntegerWeight 5 = 0 from rfl]
    ring
  simpa only [primeNormalizedMatrix,primeReferenceMatrix,he] using
    primeZero_top_block_scaled_GV hp4 i

theorem primeReference_top_top_GV (hp4 : 3 < p) :
    GV p (primeNormalizedMatrix hp4 (Sum.inr 5) (Sum.inr 5) -
      primeReferenceMatrix p (Sum.inr 5) (Sum.inr 5))
      (primeBlockWeight (p := p) (Sum.inr 5) + primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  have he : primeEdgeIntegerWeight 5+primeEdgeIntegerWeight 5+1 = 1 := by
    rw [show primeEdgeIntegerWeight 5 = 0 from rfl]
    norm_num
  simpa only [primeReferenceMatrix,he,zpow_one] using primeTop_block_scaled_GV hp4

theorem primeReference_edge_GV (hp4 : 3 < p) (k l : Fin 6) :
    GV p (primeNormalizedMatrix hp4 (Sum.inr k) (Sum.inr l) -
      primeReferenceMatrix p (Sum.inr k) (Sum.inr l))
      (primeBlockWeight (p := p) (Sum.inr k) + primeBlockWeight (p := p) (Sum.inr l) + 1) := by
  rcases primeEdgeSlot_cases k with ⟨ell,rfl⟩ | ⟨i,rfl⟩ | rfl
  · rcases primeEdgeSlot_cases l with ⟨m,rfl⟩ | ⟨j,rfl⟩ | rfl
    · exact primeReference_high_high_GV hp4 ell m
    · exact primeReference_GV_swap hp4 (primeReference_zero_high_GV hp4 j ell)
    · exact primeReference_high_top_GV hp4 ell
  · rcases primeEdgeSlot_cases l with ⟨m,rfl⟩ | ⟨j,rfl⟩ | rfl
    · exact primeReference_zero_high_GV hp4 i m
    · exact primeReference_zero_zero_GV hp4 i j
    · exact primeReference_zero_top_GV hp4 i
  · rcases primeEdgeSlot_cases l with ⟨m,rfl⟩ | ⟨j,rfl⟩ | rfl
    · exact primeReference_GV_swap hp4 (primeReference_high_top_GV hp4 m)
    · exact primeReference_GV_swap hp4 (primeReference_zero_top_GV hp4 j)
    · exact primeReference_top_top_GV hp4

theorem primeReference_entry_GV (hp4 : 3 < p) (x y : PrimeBlockIndex p) :
    GV p (primeNormalizedMatrix hp4 x y-primeReferenceMatrix p x y)
      (primeBlockWeight x+primeBlockWeight y+1/2) := by
  rcases x with ⟨a,i⟩ | k <;> rcases y with ⟨b,j⟩ | l
  · exact (primeReference_low_GV hp4 a b i j).mono (by linarith)
  · exact primeReference_low_edge_GV hp4 a i l
  · exact primeReference_GV_swap hp4 (primeReference_low_edge_GV hp4 b j k)
  · exact (primeReference_edge_GV hp4 k l).mono (by linarith)

theorem primeReference_entry_strict (hp4 : 3 < p)
    (x y : PrimeBlockIndex p) (n : ℕ) :
    (primeNormalizedMatrix hp4 x y-primeReferenceMatrix p x y).coeff n = 0 ∨
      primeBlockWeight x+primeBlockWeight y <
        (padicValRat p ((primeNormalizedMatrix hp4 x y-primeReferenceMatrix p x y).coeff n):ℚ) :=
  (primeReference_entry_GV hp4 x y).strict_coeff_of_margin (by norm_num) n

end
end Li2

end
