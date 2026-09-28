module
public import Li2Unified.Modular.Base.PrimeZeroRationalLeading
public import Li2Unified.Modular.Base.PrimeCrossValuation

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def primeZeroEdgeSlot (i : Fin 2) : Fin 6 := ⟨3+i.val,by have h := i.isLt; omega⟩

lemma primeZeroEdgeSlot_encode (hp4 : 3 < p) (i : Fin 2) :
    primeBlockToJet hp4 (Sum.inr (primeZeroEdgeSlot i)) =
      some (primeZeroBlockJet hp4 i) := by
  fin_cases i <;> rfl

lemma primeBlockWeight_zeroSlot (i : Fin 2) :
    primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) = (i.val:ℚ)-3/2 := by
  fin_cases i <;> norm_num [primeBlockWeight,primeZeroEdgeSlot]

lemma primeEdgeIntegerWeight_zeroSlot (i : Fin 2) :
    primeEdgeIntegerWeight (primeZeroEdgeSlot i) = (i.val:ℤ)-2 := by
  fin_cases i <;> norm_num [primeEdgeIntegerWeight,primeZeroEdgeSlot]

lemma primeZeroMoment_pair_eq_edge (i j : Fin 2) (h : i.val+j.val < 5) :
    6*(![-113/12,95/4,-253/4,2093/12,-17773/36]
      (⟨i.val+j.val,h⟩ : Fin 5) : ℚ) =
      edgeBlock (primeZeroEdgeSlot i) (primeZeroEdgeSlot j) := by
  fin_cases i <;> fin_cases j <;> norm_num [primeZeroEdgeSlot,edgeBlock]

lemma primeZeroMoment_top_eq_edge (i : Fin 2) (h : i.val+2 < 5) :
    -(![-113/12,95/4,-253/4,2093/12,-17773/36]
      (⟨i.val+2,h⟩ : Fin 5) : ℚ) = edgeBlock (primeZeroEdgeSlot i) 5 := by
  fin_cases i <;> norm_num [primeZeroEdgeSlot,edgeBlock]

lemma primeZero_top_edge_symm (i : Fin 2) :
    edgeBlock 5 (primeZeroEdgeSlot i) = edgeBlock (primeZeroEdgeSlot i) 5 := by
  fin_cases i <;> rfl

lemma primeZeroSlot_basis (hp4 : 3 < p) (i : Fin 2) :
    primeOriginalBasis p (by omega)
      ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeZeroEdgeSlot i))) =
      primeZeroBlockPoly hp4 i.castSucc := by
  rw [primeZeroBlockPoly_jet]
  exact primeBlock_original_basis_jet hp4 _ (primeZeroBlockJet hp4 i)
    (primeZeroEdgeSlot_encode hp4 i)

lemma primeZeroSlot_unit (hp4 : 3 < p) (i : Fin 2) :
    primeBlockUnitScale hp4 (Sum.inr (primeZeroEdgeSlot i)) =
      (primeLocalUnit p ⟨0,by omega⟩:ℚ)⁻¹ :=
  primeBlockUnitScale_jet hp4 _ (primeZeroBlockJet hp4 i) (primeZeroEdgeSlot_encode hp4 i)

theorem primeZero_pair_scaled_GV (hp4 : 3 < p) (i j : Fin 2) :
    let c : ℚ := primeLocalUnit p ⟨0,by omega⟩
    GV p
      (C (c⁻¹*c⁻¹)*numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
        (primeZeroBlockPoly hp4 i.castSucc*primeZeroBlockPoly hp4 j.castSucc).map
          (Int.castRingHom ℚ)) -
        C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-3) *
          edgeBlock (primeZeroEdgeSlot i) (primeZeroEdgeSlot j)))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot j)) + 1) := by
  dsimp only
  let c : ℚ := primeLocalUnit p ⟨0,by omega⟩
  let q : ℚ := ![-113/12,95/4,-253/4,2093/12,-17773/36]
    (⟨i.val+j.val,by have hi := i.isLt; have hj := j.isLt; omega⟩ : Fin 5)
  let F := numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
    (primeZeroBlockPoly hp4 i.castSucc*primeZeroBlockPoly hp4 j.castSucc).map (Int.castRingHom ℚ))
  have hu : c ≠ 0 ∧ padicValRat p c = 0 := primeLocalUnit_unit p _
  have hi : VG p c⁻¹ 0 := rational_unit_inverse_VG c hu.1 hu.2
  have hraw := primeZero_rational_entry_GV hp4 i.castSucc j.castSucc
    (by have hi := i.isLt; have hj := j.isLt; change i.val+j.val < 4; omega)
  change GV p (F-C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-3)*(c^2*6*q)))
    ((i.val:ℚ)+(j.val:ℚ)-2) at hraw
  have hs := GV.C_mul (hi.mul hi) hraw
  have he : C (c⁻¹*c⁻¹) *
      (F-C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-3)*(c^2*6*q))) =
      C (c⁻¹*c⁻¹)*F-C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-3)*(6*q)) := by
    rw [mul_sub,← C_mul]
    congr 1
    congr 1
    field_simp [hu.1] <;> ring
  rw [he] at hs
  have hq : 6*q = edgeBlock (primeZeroEdgeSlot i) (primeZeroEdgeSlot j) :=
    primeZeroMoment_pair_eq_edge i j _
  rw [hq] at hs
  convert hs using 1 <;> try simp only [primeBlockWeight_zeroSlot] <;> ring

/-- G remains unscaled; replace the remaining 6*c0 by -1 with proved error. -/
theorem primeZero_top_scaled_GV (hp4 : 3 < p) (i : Fin 2) :
    let c : ℚ := primeLocalUnit p ⟨0,by omega⟩
    GV p
      (C c⁻¹*numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
        (primeZeroBlockPoly hp4 i.castSucc*primeZeroBlockPoly hp4 2).map (Int.castRingHom ℚ)) -
        C ((p:ℚ)^((i.val:ℤ)-1)*edgeBlock (primeZeroEdgeSlot i) 5))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  dsimp only
  let c : ℚ := primeLocalUnit p ⟨0,by omega⟩
  let q : ℚ := ![-113/12,95/4,-253/4,2093/12,-17773/36]
    (⟨i.val+2,by have hi := i.isLt; omega⟩ : Fin 5)
  let F := numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
    (primeZeroBlockPoly hp4 i.castSucc*primeZeroBlockPoly hp4 2).map (Int.castRingHom ℚ))
  have hu : c ≠ 0 ∧ padicValRat p c = 0 := primeLocalUnit_unit p _
  have hi : VG p c⁻¹ 0 := rational_unit_inverse_VG c hu.1 hu.2
  have hraw := primeZero_rational_entry_GV hp4 i.castSucc (2:Fin 3)
    (by have hi := i.isLt; change i.val+2 < 4; omega)
  change GV p (F-C ((p:ℚ)^((i.val:ℤ)+2-3)*(c^2*6*q)))
    ((i.val:ℚ)+2-2) at hraw
  simp only [show (i.val:ℤ)+2-3 = (i.val:ℤ)-1 by ring,add_sub_cancel_right] at hraw
  have hs := GV.C_mul hi hraw
  have he : C c⁻¹*(F-C ((p:ℚ)^((i.val:ℤ)-1)*(c^2*6*q))) =
      C c⁻¹*F-C ((p:ℚ)^((i.val:ℤ)-1)*(6*c*q)) := by
    rw [mul_sub,← C_mul]
    congr 1
    congr 1
    field_simp [hu.1] <;> ring
  rw [he] at hs
  have hleft : GV p (C c⁻¹*F-C ((p:ℚ)^((i.val:ℤ)-1)*(6*c*q))) (i.val:ℚ) := by
    simpa only [zero_add] using! hs
  have hc : VG p (c-(-1/6:ℚ)) 1 := by
    apply VG_of_padic_norm_pow_le _ 1
    simpa only [c,Rat.cast_sub,Rat.cast_intCast,Rat.cast_div,Rat.cast_neg,
      Rat.cast_one,Rat.cast_ofNat,pow_one] using! primeLocalUnit_zero_norm (p := p) hp4
  have h6 : VG p (6*c+1) 1 := by
    convert (VG.natCast (p := p) 6).mul hc using 1 <;> ring
  have hq : VG p q 0 := primeZeroMoment_VG hp4 _
  have hcorr : GV p (C ((p:ℚ)^((i.val:ℤ)-1)*((6*c+1)*q))) (i.val:ℚ) := by
    have h := GV.C ((VG.primePow (p := p) ((i.val:ℤ)-1)).mul (h6.mul hq))
    convert h using 1 <;> push_cast <;> ring
  have he' : C c⁻¹*F-C ((p:ℚ)^((i.val:ℤ)-1)*(-q)) =
      (C c⁻¹*F-C ((p:ℚ)^((i.val:ℤ)-1)*(6*c*q))) +
        C ((p:ℚ)^((i.val:ℤ)-1)*((6*c+1)*q)) := by
    simp only [C_mul,C_add,C_neg,C_1]
    ring
  have hfinal : GV p (C c⁻¹*F-C ((p:ℚ)^((i.val:ℤ)-1)*(-q))) (i.val:ℚ) := by
    rw [he']
    exact hleft.add hcorr
  have hqedge : -q = edgeBlock (primeZeroEdgeSlot i) 5 := primeZeroMoment_top_eq_edge i _
  rw [hqedge] at hfinal
  have hw : primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
      primeBlockWeight (p := p) (Sum.inr 5) + 1 = (i.val:ℚ) := by
    rw [primeBlockWeight_zeroSlot, show primeBlockWeight (p := p) (Sum.inr 5) = 1/2 from rfl]
    ring
  rw [hw]
  exact hfinal

theorem primeZero_pair_block_scaled_GV (hp4 : 3 < p) (i j : Fin 2) :
    GV p
      (C (primeBlockUnitScale hp4 (Sum.inr (primeZeroEdgeSlot i)) *
          primeBlockUnitScale hp4 (Sum.inr (primeZeroEdgeSlot j))) *
        primeOriginalNumeratorEntry p (by omega)
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeZeroEdgeSlot i)))
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeZeroEdgeSlot j))) -
        C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-3) *
          edgeBlock (primeZeroEdgeSlot i) (primeZeroEdgeSlot j)))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot j)) + 1) := by
  rw [primeZeroSlot_unit,primeZeroSlot_unit]
  unfold primeOriginalNumeratorEntry
  rw [primeZeroSlot_basis,primeZeroSlot_basis]
  exact primeZero_pair_scaled_GV hp4 i j

theorem primeZero_top_block_scaled_GV (hp4 : 3 < p) (i : Fin 2) :
    GV p
      (C (primeBlockUnitScale hp4 (Sum.inr (primeZeroEdgeSlot i)) *
          primeBlockUnitScale hp4 (Sum.inr 5)) *
        primeOriginalNumeratorEntry p (by omega)
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeZeroEdgeSlot i)))
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr 5)) -
        C ((p:ℚ)^((i.val:ℤ)-1)*edgeBlock (primeZeroEdgeSlot i) 5))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  rw [primeZeroSlot_unit,primeBlockUnitScale_top,mul_one]
  unfold primeOriginalNumeratorEntry
  rw [primeZeroSlot_basis,primeBlock_original_basis_top,← primeZeroBlockPoly_top hp4]
  exact primeZero_top_scaled_GV hp4 i

end
end Li2

end
