module
public import Li2Unified.Modular.Base.PrimeTopLocal
public import Li2Unified.Modular.Base.PrimeIntegralJetBounds

set_option backward.privateInPublic true

@[expose] public section

/-! Cube-scaled bounds for the literal integer tests and original discs. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def primeDiscCubeGain (a : Fin p) : ℕ :=
  if a.val = 0 then 0 else if a.val ≤ p-4 then 1 else 2

lemma primeJet_pair_disc_factor (a b : PrimeJet p) (c : Fin p) :
    ∃ E : ℤ[X], (primeJetPoly p a*primeJetPoly p b).comp (primeDiscSubstitution p c) =
      C ((p:ℤ)^(primeJetLocalOrder p a c+primeJetLocalOrder p b c))*E := by
  obtain ⟨A,hA⟩ := primeJet_disc_factor p a c
  obtain ⟨B,hB⟩ := primeJet_disc_factor p b c
  refine ⟨X^(primeJetLocalOrder p a c+primeJetLocalOrder p b c)*(A*B),?_⟩
  rw [mul_comp,hA,hB]
  simp only [pow_add,C_mul]
  ring

lemma primeLow_cross_cube_order (hp4 : 3 < p) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (hb0 : 0 < b.val) (hb : b.val ≤ p-4) (hab : a ≠ b)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b)) (c : Fin p) :
    i.val+j.val+2 ≤ primeJetLocalOrder p ⟨a,i⟩ c+
      primeJetLocalOrder p ⟨b,j⟩ c+primeDiscCubeGain c := by
  have hi : i.val ≤ 1 := by
    have hi := i.isLt
    have hm := primeMultiplicity_low hp4 a ha
    omega
  have hj : j.val ≤ 1 := by
    have hj := j.isLt
    have hm := primeMultiplicity_low hp4 b hb
    omega
  by_cases hca : c = a
  · subst c
    simp only [primeJetLocalOrder,ite_true,if_pos rfl,if_neg hab,
      primeMultiplicity_low hp4 a ha,primeDiscCubeGain,if_neg ha0.ne',if_pos ha]
    omega
  · by_cases hcb : c = b
    · subst c
      simp only [primeJetLocalOrder,ite_true,if_neg (Ne.symm hab),if_pos rfl,
        primeMultiplicity_low hp4 b hb,primeDiscCubeGain,if_neg hb0.ne',if_pos hb]
      omega
    · simp only [primeJetLocalOrder,ite_true,if_neg hca,if_neg hcb]
      by_cases hz : c.val = 0
      · have hm : primeMultiplicity p c = 2 := primeMultiplicity_low hp4 c (by omega)
        simp only [hm,primeDiscCubeGain,if_pos hz]
        omega
      · by_cases hl : c.val ≤ p-4
        · simp only [primeMultiplicity_low hp4 c hl,primeDiscCubeGain,if_neg hz,if_pos hl]
          omega
        · have hm : primeMultiplicity p c = 1 := by
            unfold primeMultiplicity
            rw [if_neg (by omega)]
          simp only [hm,primeDiscCubeGain,if_neg hz,if_neg hl]
          omega

lemma primeProduct_jet_disc_factor (a : PrimeJet p) (c : Fin p) :
    ∃ E : ℤ[X], (primeProduct p*primeJetPoly p a).comp (primeDiscSubstitution p c) =
      C ((p:ℤ)^(primeMultiplicity p c+primeJetLocalOrder p a c))*E := by
  obtain ⟨A,hA⟩ := primeProduct_expansion p c
  obtain ⟨B,hB⟩ := primeJet_disc_factor p a c
  refine ⟨X^(primeMultiplicity p c+primeJetLocalOrder p a c)*
    ((C (primeLocalUnit p c)+C (p:ℤ)*A)*B),?_⟩
  rw [mul_comp,hA,hB]
  simp only [pow_add,C_mul]
  ring

lemma primeTop_low_cube_order (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (i : Fin (primeMultiplicity p a)) (c : Fin p) :
    i.val+3 ≤ primeMultiplicity p c+primeJetLocalOrder p ⟨a,i⟩ c+primeDiscCubeGain c := by
  have hi : i.val ≤ 1 := by
    have hi := i.isLt
    have hm := primeMultiplicity_low hp4 a ha
    omega
  by_cases hca : c = a
  · subst c
    simp only [primeJetLocalOrder,ite_true,if_pos rfl,primeMultiplicity_low hp4 a ha,
      primeDiscCubeGain,if_neg ha0.ne',if_pos ha]
    omega
  · simp only [primeJetLocalOrder,ite_true,if_neg hca]
    by_cases hz : c.val = 0
    · have hm : primeMultiplicity p c = 2 := primeMultiplicity_low hp4 c (by omega)
      simp only [hm,primeDiscCubeGain,if_pos hz]
      omega
    · by_cases hl : c.val ≤ p-4
      · simp only [primeMultiplicity_low hp4 c hl,primeDiscCubeGain,if_neg hz,if_pos hl]
        omega
      · have hm : primeMultiplicity p c = 1 := by
          unfold primeMultiplicity
          rw [if_neg (by omega)]
        simp only [hm,primeDiscCubeGain,if_neg hz,if_neg hl]
        omega

lemma primeOriginalBasis_eq_jet_of_index (hp3 : 3 ≤ p)
    (I : Fin (2*(p-1))) (a : PrimeJet p)
    (hI : finCongr (primeBasisSize p hp3) I = ((primeJetEquiv p hp3).symm a).succ) :
    primeOriginalBasis p hp3 I = primeJetPoly p a := by
  unfold primeOriginalBasis
  rw [hI]
  simp only [primeFullBasis,Fin.cases_succ,primeIndexedPoly,Equiv.apply_symm_apply]

lemma primeOriginalBasis_zero_eq_product (hp3 : 3 ≤ p) :
    primeOriginalBasis p hp3 (⟨0,by omega⟩ : Fin (2*(p-1))) = primeProduct p := by
  have hI : finCongr (primeBasisSize p hp3) (⟨0,by omega⟩ : Fin (2*(p-1))) = 0 :=
    Fin.ext rfl
  unfold primeOriginalBasis
  rw [hI]
  simp only [primeFullBasis,Fin.cases_zero]

end
end Li2

end
