module
public import Li2Unified.Modular.Base.PrimeReferenceMatrix
public import Li2Unified.Modular.Base.PrimeLowWeightUnit
public import Mathlib.Tactic.NormNum.GCD

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeReference_not_dvd_72 (hp4 : 3 < p) : ¬ p ∣ 72 := by
  have h2 : ¬ p ∣ 2 := by
    intro h
    have hh := Nat.le_of_dvd (by decide : 0 < 2) h
    omega
  have h3 : ¬ p ∣ 3 := by
    intro h
    have hh := Nat.le_of_dvd (by decide : 0 < 3) h
    omega
  rw [show (72:ℕ) = 2^3*3^2 by norm_num]
  intro h
  rcases hp.out.dvd_mul.mp h with h | h
  · exact h2 (hp.out.dvd_of_dvd_pow h)
  · exact h3 (hp.out.dvd_of_dvd_pow h)

lemma primeReference_rational_VG (hp4 : 3 < p) (q : ℚ) (hden : q.den ∣ 72) :
    VG p q 0 := by
  have hn : ¬ p ∣ q.den := fun h => primeReference_not_dvd_72 hp4 (dvd_trans h hden)
  right
  rw [padicValRat_def,padicValNat.eq_zero_of_not_dvd hn,Nat.cast_zero,sub_zero]
  positivity

lemma primeReference_low_den (i j : Fin 2) : (lowBlock i j).den ∣ 72 := by
  fin_cases i <;> fin_cases j <;> norm_num [lowBlock]

lemma primeReference_edge_den (k l : Fin 6) : (edgeBlock k l).den ∣ 72 := by
  fin_cases k <;> fin_cases l <;> norm_num [edgeBlock]

theorem primeReferenceMatrix_GV (hp4 : 3 < p) (x y : PrimeBlockIndex p) :
    GV p (primeReferenceMatrix p x y) (primeBlockWeight x+primeBlockWeight y) := by
  rcases x with ⟨a,i⟩ | k <;> rcases y with ⟨b,j⟩ | l
  · by_cases hab : a = b
    · subst b
      simp only [primeReferenceMatrix,if_pos rfl]
      have ha := a.isLt
      have hu := primeLowRationalWeight_unit (p := p) hp4 (a.val+1) (by omega) (by omega)
      have hw : VG p (primeLowRationalWeight (a.val+1)) 0 := by
        right
        rw [hu.2]
        norm_num
      have hb : VG p (lowBlock i j) 0 :=
        primeReference_rational_VG hp4 _ (primeReference_low_den i j)
      have h := GV.C (((VG.primePow (p := p) ((i.val:ℤ)+(j.val:ℤ)-2)).mul hw).mul hb)
      convert h using 1 <;> simp only [primeBlockWeight_low] <;> push_cast <;> ring
    · simpa only [primeReferenceMatrix,if_neg hab] using
        GV.zero (p := p) (primeBlockWeight (p := p) (Sum.inl (a,i)) +
          primeBlockWeight (p := p) (Sum.inl (b,j)))
  · simpa only [primeReferenceMatrix] using
      GV.zero (p := p) (primeBlockWeight (p := p) (Sum.inl (a,i)) +
        primeBlockWeight (p := p) (Sum.inr l))
  · simpa only [primeReferenceMatrix] using
      GV.zero (p := p) (primeBlockWeight (p := p) (Sum.inr k) +
        primeBlockWeight (p := p) (Sum.inl (b,j)))
  · simp only [primeReferenceMatrix]
    have hb : VG p (edgeBlock k l) 0 :=
      primeReference_rational_VG hp4 _ (primeReference_edge_den k l)
    have h := GV.C ((VG.primePow (p := p)
      (primeEdgeIntegerWeight k+primeEdgeIntegerWeight l+1)).mul hb)
    convert h using 1 <;> simp only [primeBlockWeight_edge] <;> push_cast <;> ring

theorem primeNormalizedMatrix_GV (hp4 : 3 < p) (x y : PrimeBlockIndex p) :
    GV p (primeNormalizedMatrix hp4 x y) (primeBlockWeight x+primeBlockWeight y) := by
  have hd : GV p (primeNormalizedMatrix hp4 x y-primeReferenceMatrix p x y)
      (primeBlockWeight x+primeBlockWeight y) :=
    (primeReference_entry_GV hp4 x y).mono (by linarith)
  have h := hd.add (primeReferenceMatrix_GV hp4 x y)
  simpa only [sub_add_cancel] using h

end
end Li2

end
