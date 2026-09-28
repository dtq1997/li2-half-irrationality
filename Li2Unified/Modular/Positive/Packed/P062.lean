module
public import Li2Unified.Modular.Positive.Packed.P059
public import Li2Unified.Modular.Positive.Packed.P057
public import Li2Unified.Modular.Positive.Packed.P061
public import Li2Unified.Modular.Base.PrimeHighScaledBlock
public import Li2Unified.Modular.Positive.Packed.P056
public import Li2Unified.Modular.Base.PrimeZeroRationalLeading
public import Li2Unified.Modular.Base.PrimeZeroScaledBlock
public import Li2Unified.Modular.Base.PrimeNormalizedCrossBlock
public import Li2Unified.Modular.Positive.Packed.P055
public import Li2Unified.Modular.Base.PrimeLowEntry

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma parameterHighMoment_pair_eq_edge (lam : ℚ) (ell : Fin 3) :
    parameterHighRationalWeight lam ell*highShapeVValue lam 0 =
      fixedCornerBlock lam (primeHighEdgeSlot ell) (primeHighEdgeSlot ell) := by
  fin_cases ell <;> rfl

lemma parameterHighMoment_top_eq_edge (lam : ℚ) (ell : Fin 3) :
    primeHighRationalLocalUnit ell*parameterHighRationalWeight lam ell*highShapeVValue lam 1 =
      fixedCornerBlock lam (primeHighEdgeSlot ell) 5 := by
  fin_cases ell
  · change (1/2:ℚ)*(-2)*fixedHighMoment lam 1 = -fixedHighMoment lam 1
    ring
  · change (-1:ℚ)*(lam/2)*fixedHighMoment lam 1 = -lam/2*fixedHighMoment lam 1
    ring
  · change (1/2:ℚ)*(-2*lam^2/3)*fixedHighMoment lam 1 = -lam^2/3*fixedHighMoment lam 1
    ring

lemma parameterHigh_top_edge_symm (lam : ℚ) (ell : Fin 3) :
    fixedCornerBlock lam 5 (primeHighEdgeSlot ell) =
      fixedCornerBlock lam (primeHighEdgeSlot ell) 5 := by
  fin_cases ell <;> rfl

lemma parameterHighRationalWeight_VG (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (ell : Fin 3) :
    VG p (parameterHighRationalWeight lam ell) 0 := by
  apply VG_of_padic_norm_pow_le _ 0
  rw [pow_zero]
  let x : ℤ_[p] := parameterHighDiscWeight lam hu (primeHighBlockJet hp4 ell).1
  let q : ℚ_[p] := (parameterHighRationalWeight lam ell:ℚ_[p])
  change ‖q‖ ≤ 1
  have h : ‖(x:ℚ_[p])-q‖ ≤ ‖(p:ℚ_[p])‖ :=
    parameterHighRationalWeight_norm lam hu hferm hp4 ell
  rw [show q = (x:ℚ_[p])-((x:ℚ_[p])-q) by ring,sub_eq_add_neg]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  rw [norm_neg]
  exact max_le (PadicInt.norm_le_one x) (h.trans (PadicInt.norm_le_one (p:ℤ_[p])))

theorem parameterHigh_pair_scaled_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hunit : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (ell : Fin 3) :
    let c : ℚ := primeLocalUnit p (primeHighBlockJet hp4 ell).1
    GV p
      (C (c⁻¹*c⁻¹)*Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
        (primeHighBlockPoly hp4 ell 0*primeHighBlockPoly hp4 ell 0).map
          (Int.castRingHom ℚ)) -
        C ((p:ℚ)^(-1:ℤ)*fixedCornerBlock lam (primeHighEdgeSlot ell) (primeHighEdgeSlot ell))) 0 := by
  dsimp only
  let c : ℚ := primeLocalUnit p (primeHighBlockJet hp4 ell).1
  let w : ℚ := parameterHighRationalWeight lam ell
  let F : ℚ[X] := Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
    (primeHighBlockPoly hp4 ell 0*primeHighBlockPoly hp4 ell 0).map (Int.castRingHom ℚ))
  have hu : c ≠ 0 ∧ padicValRat p c = 0 := primeLocalUnit_unit p _
  have hi : VG p c⁻¹ 0 := rational_unit_inverse_VG c hu.1 hu.2
  have hraw : GV p (F-C ((p:ℚ)^(-1:ℤ)*(c^2*w*highShapeVValue lam 0))) 0 := by
    simpa [F,c,w] using parameterHigh_rational_entry_GV lam hlam hunit hone hferm hp4 ell (0:Fin 2) (0:Fin 2) (by decide)
  have hs : GV p (C (c⁻¹*c⁻¹)*(F-C ((p:ℚ)^(-1:ℤ)*(c^2*w*highShapeVValue lam 0)))) 0 := by
    simpa only [zero_add] using GV.C_mul (hi.mul hi) hraw
  have he : C (c⁻¹*c⁻¹)*(F-C ((p:ℚ)^(-1:ℤ)*(c^2*w*highShapeVValue lam 0))) =
      C (c⁻¹*c⁻¹)*F-C ((p:ℚ)^(-1:ℤ)*(w*highShapeVValue lam 0)) := by
    rw [mul_sub,← C_mul]
    congr 1
    congr 1
    field_simp [hu.1] <;> ring
  rw [he] at hs
  have heq : w*highShapeVValue lam 0 = fixedCornerBlock lam (primeHighEdgeSlot ell) (primeHighEdgeSlot ell) :=
    parameterHighMoment_pair_eq_edge lam ell
  rw [heq] at hs
  exact hs

/-- G stays unchanged; the remaining actual local unit has a separately paid error. -/
theorem parameterHigh_top_scaled_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hunit : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (ell : Fin 3) :
    let c : ℚ := primeLocalUnit p (primeHighBlockJet hp4 ell).1
    GV p
      (C c⁻¹*Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
        (primeHighBlockPoly hp4 ell 0*primeHighBlockPoly hp4 ell 1).map
          (Int.castRingHom ℚ)) -
        C (fixedCornerBlock lam (primeHighEdgeSlot ell) 5)) 1 := by
  dsimp only
  let c : ℚ := primeLocalUnit p (primeHighBlockJet hp4 ell).1
  let v : ℚ := primeHighRationalLocalUnit ell
  let w : ℚ := parameterHighRationalWeight lam ell
  let q : ℚ := highShapeVValue lam 1
  let F : ℚ[X] := Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
    (primeHighBlockPoly hp4 ell 0*primeHighBlockPoly hp4 ell 1).map (Int.castRingHom ℚ))
  have hu : c ≠ 0 ∧ padicValRat p c = 0 := primeLocalUnit_unit p _
  have hi : VG p c⁻¹ 0 := rational_unit_inverse_VG c hu.1 hu.2
  have hraw : GV p (F-C (c^2*w*q)) 1 := by
    simpa [F,c,w,q] using parameterHigh_rational_entry_GV lam hlam hunit hone hferm hp4 ell (0:Fin 2) (1:Fin 2) (by decide)
  have hs : GV p (C c⁻¹*(F-C (c^2*w*q))) 1 := by
    simpa only [zero_add] using GV.C_mul hi hraw
  have he : C c⁻¹*(F-C (c^2*w*q)) = C c⁻¹*F-C (c*w*q) := by
    rw [mul_sub,← C_mul]
    congr 1
    congr 1
    field_simp [hu.1] <;> ring
  rw [he] at hs
  have hc : VG p (c-v) 1 := by
    apply VG_of_padic_norm_pow_le _ 1
    simpa only [c,v,Rat.cast_sub,Rat.cast_intCast,pow_one] using
      primeHighRationalLocalUnit_norm hp4 ell
  have hq : VG p q 0 := by
    apply VG_of_padic_norm_pow_le _ 0
    simpa only [q,pow_zero] using highShapeVValue_norm_le_one lam hunit hone hferm hp4 (1:Fin 3)
  have hcoeff : VG p (w*q) 0 := by
    simpa only [zero_add] using (parameterHighRationalWeight_VG lam hunit hferm hp4 ell).mul hq
  have hcorr : GV p (C ((c-v)*(w*q))) 1 := by
    simpa only [add_zero] using GV.C (hc.mul hcoeff)
  have he' : C c⁻¹*F-C (v*w*q) =
      (C c⁻¹*F-C (c*w*q))+C ((c-v)*(w*q)) := by
    simp only [C_mul,C_sub]
    ring
  have hfinal : GV p (C c⁻¹*F-C (v*w*q)) 1 := by
    rw [he']
    exact hs.add hcorr
  have heq : v*w*q = fixedCornerBlock lam (primeHighEdgeSlot ell) 5 :=
    parameterHighMoment_top_eq_edge lam ell
  rw [heq] at hfinal
  exact hfinal

theorem parameterHigh_pair_block_scaled_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hunit : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (ell : Fin 3) :
    GV p
      (C (primeBlockUnitScale hp4 (Sum.inr (primeHighEdgeSlot ell)) *
          primeBlockUnitScale hp4 (Sum.inr (primeHighEdgeSlot ell))) *
        parameterOriginalNumeratorEntry lam p (by omega)
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot ell)))
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot ell))) -
        C ((p:ℚ)^(-1:ℤ)*fixedCornerBlock lam (primeHighEdgeSlot ell) (primeHighEdgeSlot ell)))
      (primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
        primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) + 1) := by
  have hw : primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
      primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) + 1 = 0 := by
    norm_num [primeBlockWeight_highSlot]
  rw [hw]
  simp only [primeHighSlot_unit,parameterOriginalNumeratorEntry,primeHighSlot_basis]
  exact parameterHigh_pair_scaled_GV lam hlam hunit hone hferm hp4 ell

theorem parameterHigh_top_block_scaled_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hunit : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (ell : Fin 3) :
    GV p
      (C (primeBlockUnitScale hp4 (Sum.inr (primeHighEdgeSlot ell)) *
          primeBlockUnitScale hp4 (Sum.inr 5)) *
        parameterOriginalNumeratorEntry lam p (by omega)
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot ell)))
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr 5)) -
        C (fixedCornerBlock lam (primeHighEdgeSlot ell) 5))
      (primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
        primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  have hw : primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
      primeBlockWeight (p := p) (Sum.inr 5) + 1 = 1 := by
    rw [primeBlockWeight_highSlot,
      show primeBlockWeight (p := p) (Sum.inr 5) = (1/2:ℚ) from rfl]
    norm_num
  rw [hw]
  simp only [primeHighSlot_unit,primeBlockUnitScale_top,mul_one,
    parameterOriginalNumeratorEntry,primeHighSlot_basis,primeBlock_original_basis_top]
  rw [← primeHighBlockPoly_top hp4 ell]
  exact parameterHigh_top_scaled_GV lam hlam hunit hone hferm hp4 ell


end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterHigh_top_block_scaled_GV

end

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

/-- Full zero/zero or zero/G entries; i=j=2 is excluded and requires the full top sum. -/
theorem parameterZero_rational_entry_leading (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (i j : Fin 3)
    (hij : i.val+j.val < 4) (n : ℕ) :
    let k : Fin 5 := ⟨i.val+j.val,by omega⟩
    let c : ℚ := primeLocalUnit p ⟨0,by omega⟩
    ‖(C ((p:ℚ_[p])^3) *
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
        (primeZeroBlockPoly hp4 i*primeZeroBlockPoly hp4 j).map (Int.castRingHom ℚ))).map
          (Rat.castHom ℚ_[p]) -
      C ((p:ℚ_[p])^(i.val+j.val) *
        ((c^2*6*(zeroShapeUValue lam k : ℚ) : ℚ) : ℚ_[p]))).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  let k : ℕ := i.val+j.val
  let q : ℚ := zeroShapeUValue lam
    (⟨i.val+j.val,by omega⟩ : Fin 5)
  let c : ℤ := primeLocalUnit p ⟨0,by omega⟩
  let u : ℤ_[p] := primeDiscUnitConstant 0 (by omega)
  let d : ℤ_[p] := (c:ℤ_[p])^2
  let e : ℤ_[p] := (p:ℤ_[p])^k * ((c*c:ℤ):ℤ_[p])
  let s : ℚ_[p] := (e:ℚ_[p]) * ((u:ℚ_[p])*(q:ℚ_[p]))
  let t : ℚ_[p] := (p:ℚ_[p])^k * (((c:ℚ)^2*6*q : ℚ) : ℚ_[p])
  have hq : ‖(q:ℚ_[p])‖ ≤ 1 := zeroShapeUValue_norm_le_one lam hu hone hferm hp4 _
  have hfac : ‖(d:ℚ_[p])*(q:ℚ_[p])‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1*1 := mul_le_mul (PadicInt.norm_le_one d) hq (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hunit : ‖(u:ℚ_[p])-6‖ ≤ ‖(p:ℚ_[p])‖ := primeDiscUnitConstant_zero_norm hp4
  have hdelta : ‖(d:ℚ_[p])*(q:ℚ_[p])*((u:ℚ_[p])-6)‖ ≤ ‖(p:ℚ_[p])‖ := by
    rw [norm_mul]
    calc
      _ ≤ 1*‖(p:ℚ_[p])‖ := mul_le_mul hfac hunit (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have he : s-t = (p:ℚ_[p])^k*((d:ℚ_[p])*(q:ℚ_[p])*((u:ℚ_[p])-6)) := by
    dsimp only [s,t,d,e]
    simp only [PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_natCast,
      PadicInt.coe_intCast,Int.cast_mul,Rat.cast_mul,Rat.cast_pow,
      Rat.cast_intCast,Rat.cast_ofNat]
    ring
  have hst : ‖s-t‖ ≤ ‖(p:ℚ_[p])‖^(k+1) := by
    rw [he,norm_mul,norm_pow,pow_succ]
    exact mul_le_mul_of_nonneg_left hdelta (by positivity)
  apply fieldPolynomial_replace_leading_bound _ s t _ (by positivity) ?_ hst n
  intro l
  simpa only [primeZeroBlockPoly,primeZeroAugmentedIndex,Fin.val_mk,s,t,e,k,q,c,u]
    using parameterZero_original_entry_leading lam hlam hu hone hferm hp4
      (primeZeroAugmentedIndex hp4 i) (primeZeroAugmentedIndex hp4 j)
      (by simpa only [primeZeroAugmentedIndex,Fin.val_mk] using hij) l

theorem parameterZero_rational_entry_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (i j : Fin 3)
    (hij : i.val+j.val < 4) :
    let k : Fin 5 := ⟨i.val+j.val,by omega⟩
    let c : ℚ := primeLocalUnit p ⟨0,by omega⟩
    GV p
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
        (primeZeroBlockPoly hp4 i*primeZeroBlockPoly hp4 j).map (Int.castRingHom ℚ)) -
        C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-3) *
          (c^2*6*(zeroShapeUValue lam k : ℚ))))
      ((i.val:ℚ)+(j.val:ℚ)-2) := by
  dsimp only
  have h := GV_of_cube_padic_leading_bound
    (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
      (primeZeroBlockPoly hp4 i*primeZeroBlockPoly hp4 j).map (Int.castRingHom ℚ)))
    ((primeLocalUnit p ⟨0,by omega⟩:ℚ)^2*6*
      (zeroShapeUValue lam
        (⟨i.val+j.val,by omega⟩ : Fin 5) : ℚ)) (i.val+j.val)
    (parameterZero_rational_entry_leading lam hlam hu hone hferm hp4 i j hij)
  convert h using 1 <;> push_cast <;> ring


end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterZero_rational_entry_GV

end

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma parameterZeroMoment_pair_eq_edge (lam : ℚ) (i j : Fin 2) (h : i.val+j.val < 5) :
    6*zeroShapeUValue lam ⟨i.val+j.val,h⟩ =
      fixedCornerBlock lam (primeZeroEdgeSlot i) (primeZeroEdgeSlot j) := by
  fin_cases i <;> fin_cases j <;> rfl

lemma parameterZeroMoment_top_eq_edge (lam : ℚ) (i : Fin 2) (h : i.val+2 < 5) :
    -(zeroShapeUValue lam ⟨i.val+2,h⟩) =
      fixedCornerBlock lam (primeZeroEdgeSlot i) 5 := by
  fin_cases i <;> rfl

lemma parameterZero_top_edge_symm (lam : ℚ) (i : Fin 2) :
    fixedCornerBlock lam 5 (primeZeroEdgeSlot i) =
      fixedCornerBlock lam (primeZeroEdgeSlot i) 5 := by
  fin_cases i <;> rfl

theorem parameterZero_pair_scaled_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hunit : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (i j : Fin 2) :
    let c : ℚ := primeLocalUnit p ⟨0,by omega⟩
    GV p
      (C (c⁻¹*c⁻¹)*Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
        (primeZeroBlockPoly hp4 i.castSucc*primeZeroBlockPoly hp4 j.castSucc).map
          (Int.castRingHom ℚ)) -
        C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-3) *
          fixedCornerBlock lam (primeZeroEdgeSlot i) (primeZeroEdgeSlot j)))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot j)) + 1) := by
  dsimp only
  let c : ℚ := primeLocalUnit p ⟨0,by omega⟩
  let q : ℚ := zeroShapeUValue lam
    (⟨i.val+j.val,by have hi := i.isLt; have hj := j.isLt; omega⟩ : Fin 5)
  let F := Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
    (primeZeroBlockPoly hp4 i.castSucc*primeZeroBlockPoly hp4 j.castSucc).map (Int.castRingHom ℚ))
  have hu : c ≠ 0 ∧ padicValRat p c = 0 := primeLocalUnit_unit p _
  have hi : VG p c⁻¹ 0 := rational_unit_inverse_VG c hu.1 hu.2
  have hraw := parameterZero_rational_entry_GV lam hlam hunit hone hferm hp4 i.castSucc j.castSucc
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
  have hq : 6*q = fixedCornerBlock lam (primeZeroEdgeSlot i) (primeZeroEdgeSlot j) :=
    parameterZeroMoment_pair_eq_edge lam i j _
  rw [hq] at hs
  convert hs using 1 <;> try simp only [primeBlockWeight_zeroSlot] <;> ring

/-- G remains unscaled; replace the remaining 6*c0 by -1 with proved error. -/
theorem parameterZero_top_scaled_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hunit : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (i : Fin 2) :
    let c : ℚ := primeLocalUnit p ⟨0,by omega⟩
    GV p
      (C c⁻¹*Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
        (primeZeroBlockPoly hp4 i.castSucc*primeZeroBlockPoly hp4 2).map (Int.castRingHom ℚ)) -
        C ((p:ℚ)^((i.val:ℤ)-1)*fixedCornerBlock lam (primeZeroEdgeSlot i) 5))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  dsimp only
  let c : ℚ := primeLocalUnit p ⟨0,by omega⟩
  let q : ℚ := zeroShapeUValue lam
    (⟨i.val+2,by have hi := i.isLt; omega⟩ : Fin 5)
  let F := Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
    (primeZeroBlockPoly hp4 i.castSucc*primeZeroBlockPoly hp4 2).map (Int.castRingHom ℚ))
  have hu : c ≠ 0 ∧ padicValRat p c = 0 := primeLocalUnit_unit p _
  have hi : VG p c⁻¹ 0 := rational_unit_inverse_VG c hu.1 hu.2
  have hraw := parameterZero_rational_entry_GV lam hlam hunit hone hferm hp4 i.castSucc (2:Fin 3)
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
    simpa only [zero_add] using hs
  have hc : VG p (c-(-1/6:ℚ)) 1 := by
    apply VG_of_padic_norm_pow_le _ 1
    simpa only [c,Rat.cast_sub,Rat.cast_intCast,Rat.cast_div,Rat.cast_neg,
      Rat.cast_one,Rat.cast_ofNat,pow_one] using primeLocalUnit_zero_norm (p := p) hp4
  have h6 : VG p (6*c+1) 1 := by
    convert (VG.natCast (p := p) 6).mul hc using 1 <;> ring
  have hq : VG p q 0 := by
    apply VG_of_padic_norm_pow_le _ 0
    simpa using zeroShapeUValue_norm_le_one lam hunit hone hferm hp4 _
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
  have hqedge : -q = fixedCornerBlock lam (primeZeroEdgeSlot i) 5 := parameterZeroMoment_top_eq_edge lam i _
  rw [hqedge] at hfinal
  have hw : primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
      primeBlockWeight (p := p) (Sum.inr 5) + 1 = (i.val:ℚ) := by
    rw [primeBlockWeight_zeroSlot, show primeBlockWeight (p := p) (Sum.inr 5) = 1/2 from rfl]
    ring
  rw [hw]
  exact hfinal

theorem parameterZero_pair_block_scaled_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hunit : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (i j : Fin 2) :
    GV p
      (C (primeBlockUnitScale hp4 (Sum.inr (primeZeroEdgeSlot i)) *
          primeBlockUnitScale hp4 (Sum.inr (primeZeroEdgeSlot j))) *
        parameterOriginalNumeratorEntry lam p (by omega)
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeZeroEdgeSlot i)))
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeZeroEdgeSlot j))) -
        C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-3) *
          fixedCornerBlock lam (primeZeroEdgeSlot i) (primeZeroEdgeSlot j)))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot j)) + 1) := by
  rw [primeZeroSlot_unit,primeZeroSlot_unit]
  unfold parameterOriginalNumeratorEntry
  rw [primeZeroSlot_basis,primeZeroSlot_basis]
  exact parameterZero_pair_scaled_GV lam hlam hunit hone hferm hp4 i j

theorem parameterZero_top_block_scaled_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hunit : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (i : Fin 2) :
    GV p
      (C (primeBlockUnitScale hp4 (Sum.inr (primeZeroEdgeSlot i)) *
          primeBlockUnitScale hp4 (Sum.inr 5)) *
        parameterOriginalNumeratorEntry lam p (by omega)
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeZeroEdgeSlot i)))
          ((primeOriginalBlockEquiv hp4).symm (Sum.inr 5)) -
        C ((p:ℚ)^((i.val:ℤ)-1)*fixedCornerBlock lam (primeZeroEdgeSlot i) 5))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  rw [primeZeroSlot_unit,primeBlockUnitScale_top,mul_one]
  unfold parameterOriginalNumeratorEntry
  rw [primeZeroSlot_basis,primeBlock_original_basis_top,← primeZeroBlockPoly_top hp4]
  exact parameterZero_top_scaled_GV lam hlam hunit hone hferm hp4 i


end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterZero_top_block_scaled_GV

end

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterNormalizedMatrix_low_cross_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p)
    (a b : Fin (p-4)) (i j : Fin 2) (hab : a ≠ b) :
    GV p (parameterNormalizedMatrix lam hp4 (Sum.inl (a,i)) (Sum.inl (b,j)))
      (primeBlockWeight (Sum.inl (a,i)) + primeBlockWeight (Sum.inl (b,j)) + 1) := by
  apply parameterNormalizedMatrix_GV_of_original lam hp4
  have h := (parameterOriginalBasis_low_cross_GV_strict lam hlam hu
    (parameterPowerRatio_integral lam hu hone hferm)
    (Ne.symm (sub_ne_zero.mp (one_sub_parameter_power_unit lam hone hferm).1)) hp4
    ((primeOriginalBlockEquiv hp4).symm (Sum.inl (a,i)))
    ((primeOriginalBlockEquiv hp4).symm (Sum.inl (b,j)))
    (primeLowBlockJet hp4 a i).1 (primeLowBlockJet hp4 b j).1
    (primeLowBlock_pos hp4 a i) (primeLowBlock_le hp4 a i)
    (primeLowBlock_pos hp4 b j) (primeLowBlock_le hp4 b j)
    (primeLowBlock_ne hp4 a b i j hab)
    (primeLowBlockJet hp4 a i).2 (primeLowBlockJet hp4 b j).2
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeLowBlockJet hp4 a i) rfl)
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeLowBlockJet hp4 b j) rfl)).1
  simpa only [primeBlockWeight_low,primeLowBlockJet,Fin.val_mk] using h

theorem parameterNormalizedMatrix_low_zero_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p)
    (a : Fin (p-4)) (i j : Fin 2) :
    GV p (parameterNormalizedMatrix lam hp4 (Sum.inl (a,i)) (Sum.inr (primeZeroEdgeSlot j)))
      (primeBlockWeight (Sum.inl (a,i)) +
        primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot j)) + (3/2-(i.val:ℚ))) := by
  apply parameterNormalizedMatrix_GV_of_original lam hp4
  have h := (parameterOriginalBasis_low_zero_GV_strict lam hlam hu
    (parameterPowerRatio_integral lam hu hone hferm)
    (Ne.symm (sub_ne_zero.mp (one_sub_parameter_power_unit lam hone hferm).1)) hp4
    ((primeOriginalBlockEquiv hp4).symm (Sum.inl (a,i)))
    ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeZeroEdgeSlot j)))
    (primeLowBlockJet hp4 a i).1 (primeZeroBlockJet hp4 j).1
    (primeLowBlock_pos hp4 a i) (primeLowBlock_le hp4 a i) rfl
    (primeLowBlockJet hp4 a i).2 (primeZeroBlockJet hp4 j).2
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeLowBlockJet hp4 a i) rfl)
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeZeroBlockJet hp4 j)
      (primeZeroEdgeSlot_encode hp4 j))).1
  simpa only [primeBlockWeight_low,primeBlockWeight_zeroSlot,
    primeLowBlockJet,primeZeroBlockJet,Fin.val_mk] using h

theorem parameterNormalizedMatrix_low_high_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p)
    (a : Fin (p-4)) (i : Fin 2) (ell : Fin 3) :
    GV p (parameterNormalizedMatrix lam hp4 (Sum.inl (a,i)) (Sum.inr (primeHighEdgeSlot ell)))
      (primeBlockWeight (Sum.inl (a,i)) +
        primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) + (3/2-(i.val:ℚ))) := by
  apply parameterNormalizedMatrix_GV_of_original lam hp4
  have h := (parameterOriginalBasis_low_high_GV_strict lam hlam hu
    (parameterPowerRatio_integral lam hu hone hferm)
    (Ne.symm (sub_ne_zero.mp (one_sub_parameter_power_unit lam hone hferm).1)) hp4
    ((primeOriginalBlockEquiv hp4).symm (Sum.inl (a,i)))
    ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot ell)))
    (primeLowBlockJet hp4 a i).1 (primeHighBlockJet hp4 ell).1
    (primeLowBlock_pos hp4 a i) (primeLowBlock_le hp4 a i)
    (primeHighBlock_above hp4 ell)
    (primeLowBlockJet hp4 a i).2 (primeHighBlockJet hp4 ell).2
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeLowBlockJet hp4 a i) rfl)
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeHighBlockJet hp4 ell)
      (primeHighEdgeSlot_encode hp4 ell))).1
  simpa only [primeBlockWeight_low,primeBlockWeight_highSlot,
    primeLowBlockJet,Fin.val_mk] using h

theorem parameterNormalizedMatrix_zero_high_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p)
    (i : Fin 2) (ell : Fin 3) :
    GV p (parameterNormalizedMatrix lam hp4
      (Sum.inr (primeZeroEdgeSlot i)) (Sum.inr (primeHighEdgeSlot ell)))
      (primeBlockWeight (p := p) (Sum.inr (primeZeroEdgeSlot i)) +
        primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) + 1) := by
  apply parameterNormalizedMatrix_GV_of_original lam hp4
  have h := (parameterOriginalBasis_zero_high_GV_strict lam hlam hu
    (parameterPowerRatio_integral lam hu hone hferm)
    (Ne.symm (sub_ne_zero.mp (one_sub_parameter_power_unit lam hone hferm).1)) hp4
    ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeZeroEdgeSlot i)))
    ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot ell)))
    (primeZeroBlockJet hp4 i).1 (primeHighBlockJet hp4 ell).1 rfl
    (primeHighBlock_above hp4 ell)
    (primeZeroBlockJet hp4 i).2 (primeHighBlockJet hp4 ell).2
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeZeroBlockJet hp4 i)
      (primeZeroEdgeSlot_encode hp4 i))
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeHighBlockJet hp4 ell)
      (primeHighEdgeSlot_encode hp4 ell))).1
  simpa only [primeBlockWeight_zeroSlot,primeBlockWeight_highSlot,
    primeZeroBlockJet,Fin.val_mk] using h

theorem parameterNormalizedMatrix_high_cross_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p)
    (ell m : Fin 3) (hem : ell ≠ m) :
    GV p (parameterNormalizedMatrix lam hp4
      (Sum.inr (primeHighEdgeSlot ell)) (Sum.inr (primeHighEdgeSlot m)))
      (primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot ell)) +
        primeBlockWeight (p := p) (Sum.inr (primeHighEdgeSlot m)) + 1) := by
  apply parameterNormalizedMatrix_GV_of_original lam hp4
  have h := (parameterOriginalBasis_high_cross_GV_strict lam hlam hu
    (parameterPowerRatio_integral lam hu hone hferm)
    (Ne.symm (sub_ne_zero.mp (one_sub_parameter_power_unit lam hone hferm).1)) hp4
    ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot ell)))
    ((primeOriginalBlockEquiv hp4).symm (Sum.inr (primeHighEdgeSlot m)))
    (primeHighBlockJet hp4 ell).1 (primeHighBlockJet hp4 m).1
    (primeHighBlock_above hp4 ell) (primeHighBlock_above hp4 m)
    (primeHighBlock_ne hp4 ell m hem)
    (primeHighBlockJet hp4 ell).2 (primeHighBlockJet hp4 m).2
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeHighBlockJet hp4 ell)
      (primeHighEdgeSlot_encode hp4 ell))
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeHighBlockJet hp4 m)
      (primeHighEdgeSlot_encode hp4 m))).1
  simpa only [primeBlockWeight_highSlot] using h

theorem parameterNormalizedMatrix_top_low_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p)
    (a : Fin (p-4)) (i : Fin 2) :
    GV p (parameterNormalizedMatrix lam hp4 (Sum.inr 5) (Sum.inl (a,i)))
      (primeBlockWeight (p := p) (Sum.inr 5) +
        primeBlockWeight (Sum.inl (a,i)) + 1/2) := by
  apply parameterNormalizedMatrix_GV_of_original lam hp4
  rw [primeOriginalBlockEquiv_symm_top]
  have h := (parameterOriginalBasis_top_low_GV_strict lam hlam hu
    (parameterPowerRatio_integral lam hu hone hferm)
    (Ne.symm (sub_ne_zero.mp (one_sub_parameter_power_unit lam hone hferm).1)) hp4
    ((primeOriginalBlockEquiv hp4).symm (Sum.inl (a,i)))
    (primeLowBlockJet hp4 a i).1
    (primeLowBlock_pos hp4 a i) (primeLowBlock_le hp4 a i)
    (primeLowBlockJet hp4 a i).2
    (primeOriginalBlockEquiv_symm_jet hp4 _ (primeLowBlockJet hp4 a i) rfl)).1
  simpa only [primeBlockWeight_top,primeBlockWeight_low,
    primeLowBlockJet,Fin.val_mk] using h

theorem parameterNormalizedMatrix_low_edge_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p)
    (a : Fin (p-4)) (i : Fin 2) (k : Fin 6) :
    GV p (parameterNormalizedMatrix lam hp4 (Sum.inl (a,i)) (Sum.inr k))
      (primeBlockWeight (Sum.inl (a,i)) + primeBlockWeight (p := p) (Sum.inr k) + 1/2) := by
  have hi : (i.val:ℚ) ≤ 1 := by
    have h : i.val ≤ 1 := by have h := i.isLt; omega
    exact_mod_cast h
  rcases primeEdgeSlot_cases k with ⟨ell,rfl⟩ | ⟨j,rfl⟩ | rfl
  · exact (parameterNormalizedMatrix_low_high_GV lam hlam hu hone hferm hp4 a i ell).mono (by linarith)
  · exact (parameterNormalizedMatrix_low_zero_GV lam hlam hu hone hferm hp4 a i j).mono (by linarith)
  · rw [parameterNormalizedMatrix_symm lam hp4 (Sum.inl (a,i)) (Sum.inr 5)]
    simpa only [add_comm] using parameterNormalizedMatrix_top_low_GV lam hlam hu hone hferm hp4 a i


end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterNormalizedMatrix_top_low_GV

end

section
open Polynomial Li2 Li2Unified.LambdaLift
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterLow_original_entry_leading (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (i j : Fin (primeMultiplicity p a)) (n : ℕ) :
    let T := primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩
    let k : Fin 3 := ⟨i.val+j.val,primeLow_pair_lt_three hp4 a ha i j⟩
    let c : ℚ_[p] := (p:ℚ_[p])^(i.val+j.val)*
      ((primeLocalUnit p a*primeLocalUnit p a:ℤ):ℚ_[p])*
      (-(a.val:ℚ_[p])*((primeDiscUnitConstant a.val a.isLt:ℚ_[p])*
        ((lowShapeVValue lam k:ℚ):ℚ_[p])))
    ‖(C ((p:ℚ_[p])^2)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])-C ((lam:ℚ_[p])⁻¹^a.val*c)).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  let T := primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩
  have hm : i.val+j.val+1 ≤ 3 := by have h := primeLow_pair_lt_three hp4 a ha i j; omega
  have hn : ‖(p:ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (p:ℤ_[p])
  have he : C ((p:ℚ_[p])^2)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p]) =
      ∑ b : Fin p, C ((lam:ℚ_[p])⁻¹^b.val)*(C ((p:ℚ_[p])^2)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 b T) := by
    rw [parameterNumerator_global_dissection lam hlam hu (parameterPowerRatio_integral lam hu hone hferm) hp4
      (Ne.symm (sub_ne_zero.mp (one_sub_parameter_power_unit lam hone hferm).1)),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  change ‖(C ((p:ℚ_[p])^2)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])-C _).coeff n‖ ≤ _
  rw [he]
  apply fieldPolynomial_sum_leading_bound _ a _ _ (by positivity)
  · intro l
    rw [parameterDiscContribution_scaled_low lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a ha0 ha T]
    have h := fieldPolynomial_integral_weight_leading
      ((parameterDiscTestScaled (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 a T (parameterIntegralEta lam hu (parameterPowerRatio_integral lam hu hone hferm))).map
        (algebraMap ℤ_[p] ℚ_[p])) (integralParameterInvPow lam hu.1 hu.2 a.val) _ _
      (parameterJet_actual_low_scaled_leading lam hu hone hferm hp4 a ha0 ha i j
        (parameterIntegralEta lam hu (parameterPowerRatio_integral lam hu hone hferm))) l
    simpa only [integralParameterInvPow,integralRational,Rat.cast_pow,Rat.cast_inv,PadicInt.coe_pow,PadicInt.coe_mul,PadicInt.coe_natCast,PadicInt.coe_intCast,
      PadicInt.coe_neg,PadicInt.coe_natCast] using h
  · intro b hb l
    have h := fieldPolynomial_integral_weight_bound
      (C ((p:ℚ_[p])^2)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 b T) (integralParameterInvPow lam hu.1 hu.2 b.val) _
      (parameterJet_other_contribution_scaled_bound lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a i j b hb) l
    have hw : ‖(C ((lam:ℚ_[p])⁻¹^b.val)*(C ((p:ℚ_[p])^2)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 b T)).coeff l‖ ≤
        ‖(p:ℚ_[p])‖^3 := by
      simpa only [integralParameterInvPow,integralRational,Rat.cast_pow,Rat.cast_inv,PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast] using h
    exact hw.trans (pow_le_pow_of_le_one (norm_nonneg _) hn hm)

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterLow_original_entry_leading

end


end
