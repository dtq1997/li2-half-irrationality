module
public import Li2Unified.Modular.Positive.Packed.P019
public import Li2Unified.Modular.Base.RationalBaseEvaluation

set_option backward.privateInPublic true

@[expose] public section

section
/-! The finite low block reconstructed from its actual rational
four-pole functional. This does not identify the complete prime-edge matrix. -/
open Polynomial Matrix
namespace Li2Unified.ParameterFamily
noncomputable section

def fixedLowMoment (lam : ℚ) (k : Fin 3) : ℚ :=
  (Li2.rationalPoleV lam (Li2.zeroShapeRegular ⟨k.val+2, by omega⟩)
    (Li2.zeroShapeResidue ⟨k.val+2, by omega⟩)).eval 0

def fixedLowBlock (lam : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j => fixedLowMoment lam ⟨i.val+j.val, by omega⟩

/-- The underlying rational numerator is u^(k+2)/((u+1)(u+2)(u+3)),
represented with the existing common four-pole denominator. -/
theorem fixedLowMoment_cleared (k : Fin 3) :
    Li2.rationalPoleNumerator (Li2.zeroShapeRegular ⟨k.val+2, by omega⟩)
      (Li2.zeroShapeResidue ⟨k.val+2, by omega⟩) = X^(k.val+3) := by
  simpa using Li2.zeroShape_cleared (⟨k.val+2, by omega⟩ : Fin 5)

theorem fixedLowBlock_negHalf : fixedLowBlock (-1/2) = Li2.lowBlock := by
  ext i j
  exact (Li2.lowBlock_from_functional i j).symm

theorem fixedLowBlock_det (lam : ℚ) (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    (fixedLowBlock lam).det = lowBlockConstant lam := by
  have hs : 1-lam ≠ 0 := sub_ne_zero.mpr h1.symm
  have hm : lam-1 ≠ 0 := sub_ne_zero.mpr h1
  have hV6 : Li2.parameterV lam (6:ℚ[X]) = 0 := Li2.parameterV_C lam 6
  rw [Matrix.det_fin_two]
  norm_num [fixedLowBlock, fixedLowMoment, Li2.rationalPoleV,
    Li2.zeroShapeRegular, Li2.zeroShapeResidue, Fin.sum_univ_succ,
    Li2.parameterV_zero, Li2.parameterV_one, Li2.parameterV_sub,
    Li2.parameterV_X, hV6, Li2.parameterV_natCast, Li2.parameterTau,
    Finset.sum_Icc_succ_top, Li2.parameterMoment, lowBlockConstant]
  field_simp
  <;> ring

end
end Li2Unified.ParameterFamily

end


end
