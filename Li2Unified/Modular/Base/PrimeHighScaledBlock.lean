module
public import Li2Unified.Modular.Base.PrimeHighRationalLeading
public import Li2Unified.Modular.Base.PrimeNormalizedMatrix

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def primeHighEdgeSlot (ell : Fin 3) : Fin 6 :=
  ⟨ell.val,by have h := ell.isLt; omega⟩

lemma primeHighEdgeSlot_encode (hp4 : 3 < p) (ell : Fin 3) :
    primeBlockToJet hp4 (Sum.inr (primeHighEdgeSlot ell)) =
      some (primeHighBlockJet hp4 ell) := by
  fin_cases ell <;> rfl

lemma primeBlockWeight_highSlot (ell : Fin 3) :
    primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) = -1/2 := by
  fin_cases ell <;> norm_num [primeBlockWeight,primeHighEdgeSlot]

lemma primeEdgeIntegerWeight_highSlot (ell : Fin 3) :
    primeEdgeIntegerWeight (primeHighEdgeSlot ell) = -1 := by
  fin_cases ell <;> norm_num [primeEdgeIntegerWeight,primeHighEdgeSlot]

lemma primeHighMoment_pair_eq_edge (ell : Fin 3) :
    primeHighRationalWeight ell*8 = edgeBlock (primeHighEdgeSlot ell) (primeHighEdgeSlot ell) := by
  fin_cases ell <;> norm_num [primeHighRationalWeight,primeHighEdgeSlot,edgeBlock]

lemma primeHighMoment_top_eq_edge (ell : Fin 3) :
    primeHighRationalLocalUnit ell*primeHighRationalWeight ell*(-46/3:ℚ) =
      edgeBlock (primeHighEdgeSlot ell) 5 := by
  fin_cases ell <;>
    norm_num [primeHighRationalLocalUnit,primeHighRationalWeight,primeHighEdgeSlot,edgeBlock]

lemma primeHigh_top_edge_symm (ell : Fin 3) :
    edgeBlock 5 (primeHighEdgeSlot ell) = edgeBlock (primeHighEdgeSlot ell) 5 := by
  fin_cases ell <;> rfl

lemma primeHighSlot_basis (hp4 : 3 < p) (ell : Fin 3) :
    primeOriginalBasis p (by omega)
      ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot ell))) =
      primeHighBlockPoly hp4 ell 0 := by
  rw [primeHighBlockPoly_jet]
  exact primeBlock_original_basis_jet hp4 _ (primeHighBlockJet hp4 ell)
    (primeHighEdgeSlot_encode hp4 ell)

lemma primeHighSlot_unit (hp4 : 3 < p) (ell : Fin 3) :
    primeBlockUnitScale hp4 (Sum.inr (primeHighEdgeSlot ell)) =
      (primeLocalUnit p (primeHighBlockJet hp4 ell).1:ℚ)⁻¹ :=
  primeBlockUnitScale_jet hp4 _ (primeHighBlockJet hp4 ell)
    (primeHighEdgeSlot_encode hp4 ell)

theorem primeHigh_pair_scaled_GV (hp4 : 3 < p) (ell : Fin 3) :
    let c : ℚ := primeLocalUnit p (primeHighBlockJet hp4 ell).1
    GV p
      (C (c⁻¹*c⁻¹)*numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
        (primeHighBlockPoly hp4 ell 0*primeHighBlockPoly hp4 ell 0).map
          (Int.castRingHom ℚ)) -
        C ((p:ℚ)^(-1:ℤ)*edgeBlock (primeHighEdgeSlot ell) (primeHighEdgeSlot ell))) 0 := by
  dsimp only
  let c : ℚ := primeLocalUnit p (primeHighBlockJet hp4 ell).1
  let w : ℚ := primeHighRationalWeight ell
  let F : ℚ[X] := numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
    (primeHighBlockPoly hp4 ell 0*primeHighBlockPoly hp4 ell 0).map (Int.castRingHom ℚ))
  have hu : c ≠ 0 ∧ padicValRat p c = 0 := primeLocalUnit_unit p _
  have hi : VG p c⁻¹ 0 := rational_unit_inverse_VG c hu.1 hu.2
  have hraw : GV p (F-C ((p:ℚ)^(-1:ℤ)*(c^2*w*8))) 0 := by
    simpa [F,c,w] using! primeHigh_rational_entry_GV hp4 ell (0:Fin 2) (0:Fin 2) (by decide)
  have hs : GV p (C (c⁻¹*c⁻¹)*(F-C ((p:ℚ)^(-1:ℤ)*(c^2*w*8)))) 0 := by
    simpa only [zero_add] using! GV.C_mul (hi.mul hi) hraw
  have he : C (c⁻¹*c⁻¹)*(F-C ((p:ℚ)^(-1:ℤ)*(c^2*w*8))) =
      C (c⁻¹*c⁻¹)*F-C ((p:ℚ)^(-1:ℤ)*(w*8)) := by
    rw [mul_sub,← C_mul]
    congr 1
    congr 1
    field_simp [hu.1] <;> ring
  rw [he] at hs
  have heq : w*8 = edgeBlock (primeHighEdgeSlot ell) (primeHighEdgeSlot ell) :=
    primeHighMoment_pair_eq_edge ell
  rw [heq] at hs
  exact hs

/-- G stays unchanged; the remaining actual local unit has a separately paid error. -/
theorem primeHigh_top_scaled_GV (hp4 : 3 < p) (ell : Fin 3) :
    let c : ℚ := primeLocalUnit p (primeHighBlockJet hp4 ell).1
    GV p
      (C c⁻¹*numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
        (primeHighBlockPoly hp4 ell 0*primeHighBlockPoly hp4 ell 1).map
          (Int.castRingHom ℚ)) -
        C (edgeBlock (primeHighEdgeSlot ell) 5)) 1 := by
  dsimp only
  let c : ℚ := primeLocalUnit p (primeHighBlockJet hp4 ell).1
  let v : ℚ := primeHighRationalLocalUnit ell
  let w : ℚ := primeHighRationalWeight ell
  let q : ℚ := -46/3
  let F : ℚ[X] := numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
    (primeHighBlockPoly hp4 ell 0*primeHighBlockPoly hp4 ell 1).map (Int.castRingHom ℚ))
  have hu : c ≠ 0 ∧ padicValRat p c = 0 := primeLocalUnit_unit p _
  have hi : VG p c⁻¹ 0 := rational_unit_inverse_VG c hu.1 hu.2
  have hraw : GV p (F-C (c^2*w*q)) 1 := by
    simpa [F,c,w,q] using! primeHigh_rational_entry_GV hp4 ell (0:Fin 2) (1:Fin 2) (by decide)
  have hs : GV p (C c⁻¹*(F-C (c^2*w*q))) 1 := by
    simpa only [zero_add] using! GV.C_mul hi hraw
  have he : C c⁻¹*(F-C (c^2*w*q)) = C c⁻¹*F-C (c*w*q) := by
    rw [mul_sub,← C_mul]
    congr 1
    congr 1
    field_simp [hu.1] <;> ring
  rw [he] at hs
  have hc : VG p (c-v) 1 := by
    apply VG_of_padic_norm_pow_le _ 1
    simpa only [c,v,Rat.cast_sub,Rat.cast_intCast,pow_one] using!
      primeHighRationalLocalUnit_norm hp4 ell
  have hq : VG p q 0 := by
    simpa [q] using! primeHighMoment_VG hp4 (1:Fin 3)
  have hcoeff : VG p (w*q) 0 := by
    simpa only [zero_add] using! (primeHighRationalWeight_VG hp4 ell).mul hq
  have hcorr : GV p (C ((c-v)*(w*q))) 1 := by
    simpa only [add_zero] using! GV.C (hc.mul hcoeff)
  have he' : C c⁻¹*F-C (v*w*q) =
      (C c⁻¹*F-C (c*w*q))+C ((c-v)*(w*q)) := by
    simp only [C_mul,C_sub]
    ring
  have hfinal : GV p (C c⁻¹*F-C (v*w*q)) 1 := by
    rw [he']
    exact hs.add hcorr
  have heq : v*w*q = edgeBlock (primeHighEdgeSlot ell) 5 :=
    primeHighMoment_top_eq_edge ell
  rw [heq] at hfinal
  exact hfinal

theorem primeHigh_pair_block_scaled_GV (hp4 : 3 < p) (ell : Fin 3) :
    GV p
      (C (primeBlockUnitScale hp4 (Sum.inr (primeHighEdgeSlot ell)) *
          primeBlockUnitScale hp4 (Sum.inr (primeHighEdgeSlot ell))) *
        primeOriginalNumeratorEntry p (by omega)
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot ell)))
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot ell))) -
        C ((p:ℚ)^(-1:ℤ)*edgeBlock (primeHighEdgeSlot ell) (primeHighEdgeSlot ell)))
      (primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
        primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) + 1) := by
  have hw : primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
      primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) + 1 = 0 := by
    norm_num [primeBlockWeight_highSlot]
  rw [hw]
  simp only [primeHighSlot_unit,primeOriginalNumeratorEntry,primeHighSlot_basis]
  exact primeHigh_pair_scaled_GV hp4 ell

theorem primeHigh_top_block_scaled_GV (hp4 : 3 < p) (ell : Fin 3) :
    GV p
      (C (primeBlockUnitScale hp4 (Sum.inr (primeHighEdgeSlot ell)) *
          primeBlockUnitScale hp4 (Sum.inr 5)) *
        primeOriginalNumeratorEntry p (by omega)
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot ell)))
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr 5)) -
        C (edgeBlock (primeHighEdgeSlot ell) 5))
      (primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
        primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  have hw : primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
      primeBlockWeight (p := p) (Sum.inr 5) + 1 = 1 := by
    rw [primeBlockWeight_highSlot,
      show primeBlockWeight (p := p) (Sum.inr 5) = (1/2:ℚ) from rfl]
    norm_num
  rw [hw]
  simp only [primeHighSlot_unit,primeBlockUnitScale_top,mul_one,
    primeOriginalNumeratorEntry,primeHighSlot_basis,primeBlock_original_basis_top]
  rw [← primeHighBlockPoly_top hp4 ell]
  exact primeHigh_top_scaled_GV hp4 ell

theorem primeNormalizedMatrix_high_diag_GV (hp4 : 3 < p) (ell : Fin 3) :
    GV p
      (primeNormalizedMatrix hp4 (Sum.inr (primeHighEdgeSlot ell))
        (Sum.inr (primeHighEdgeSlot ell)) -
        C ((p:ℚ)^(-1:ℤ)*edgeBlock (primeHighEdgeSlot ell) (primeHighEdgeSlot ell)))
      (primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
        primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) + 1) := by
  simpa only [primeNormalizedMatrix] using! primeHigh_pair_block_scaled_GV hp4 ell

theorem primeNormalizedMatrix_high_top_GV (hp4 : 3 < p) (ell : Fin 3) :
    GV p
      (primeNormalizedMatrix hp4 (Sum.inr (primeHighEdgeSlot ell)) (Sum.inr 5) -
        C (edgeBlock (primeHighEdgeSlot ell) 5))
      (primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
        primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  simpa only [primeNormalizedMatrix] using! primeHigh_top_block_scaled_GV hp4 ell

theorem primeNormalizedMatrix_top_high_GV (hp4 : 3 < p) (ell : Fin 3) :
    GV p
      (primeNormalizedMatrix hp4 (Sum.inr 5) (Sum.inr (primeHighEdgeSlot ell)) -
        C (edgeBlock 5 (primeHighEdgeSlot ell)))
      (primeBlockWeight (p := p) (Sum.inr 5) +
        primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) + 1) := by
  rw [primeNormalizedMatrix_symm hp4 (Sum.inr 5) (Sum.inr (primeHighEdgeSlot ell)),
    primeHigh_top_edge_symm]
  simpa only [add_comm] using! primeNormalizedMatrix_high_top_GV hp4 ell

end
end Li2

end
