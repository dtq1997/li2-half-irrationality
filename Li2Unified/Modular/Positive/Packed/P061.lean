module
public import Li2Unified.Modular.Positive.Packed.P051
public import Li2Unified.Modular.Positive.Packed.P060

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
open Li2Unified.ParameterFamily

def fixedZeroMoment (lam : ℚ) (k : Fin 5) : ℚ :=
  (rationalPoleU lam (zeroShapeRegular k) (zeroShapeResidue k)).eval 0

def fixedHighMoment (lam : ℚ) (k : Fin 3) : ℚ :=
  (rationalPoleV lam (highShapeRegular k) (highShapeResidue k)).eval 0

/-- The high weights and derivatives of (u-1)(u-2)(u-3), as in the original local shapes. -/
def fixedCornerBlock (lam : ℚ) : Matrix (Fin 6) (Fin 6) ℚ :=
  arrowSix
    (-2 * fixedHighMoment lam 0)
    (lam/2 * fixedHighMoment lam 0)
    (-2*lam^2/3 * fixedHighMoment lam 0)
    (-fixedHighMoment lam 1)
    (-lam/2 * fixedHighMoment lam 1)
    (-lam^2/3 * fixedHighMoment lam 1)
    (6 * fixedZeroMoment lam 0)
    (6 * fixedZeroMoment lam 1)
    (6 * fixedZeroMoment lam 2)
    (-fixedZeroMoment lam 2)
    (-fixedZeroMoment lam 3)
    ((-1/2 + lam/2 - lam^2/6)*fixedHighMoment lam 2 + fixedZeroMoment lam 4/6)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem fixedCornerBlock_det (lam : ℚ) (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    (fixedCornerBlock lam).det = cornerBlockConstant lam := by
  have hs : 1-lam ≠ 0 := sub_ne_zero.mpr h1.symm
  have hm : lam-1 ≠ 0 := sub_ne_zero.mpr h1
  have hV3 : parameterV lam (X*3) = 3*parameterMoment lam 0 := by
    rw [mul_comm]
    exact parameterV_natCast_mul_X lam 3
  have hV3left : parameterV lam (3*X) = 3*parameterMoment lam 0 := parameterV_C_mul_X lam 3
  have hU6 : parameterU lam (6:ℚ[X]) = 6*parameterMoment lam 0 := parameterU_C lam 6
  have hVconst3 : parameterV lam (3:ℚ[X]) = 0 := parameterV_C lam 3
  have hVconst7 : parameterV lam (7:ℚ[X]) = 0 := parameterV_C lam 7
  rw [fixedCornerBlock, arrowSix_det]
  norm_num [fixedZeroMoment, fixedHighMoment, rationalPoleU, rationalPoleV,
    zeroShapeRegular, zeroShapeResidue, highShapeRegular, highShapeResidue,
    Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    parameterTau, Finset.sum_Icc_succ_top,
    parameterU_zero, parameterU_one, parameterU_sub, parameterU_X,
    parameterU_C, parameterU_natCast, parameterV_one, parameterV_add,
    parameterV_sub, parameterV_X, parameterV_C_mul_X, parameterV_X_sq,
    parameterV_C, parameterV_natCast, parameterV_natCast_mul_X,
    parameterMoment, cornerBlockConstant, hV3, hV3left, hU6, hVconst3, hVconst7]
  field_simp
  all_goals try simp only [hV3]
  all_goals norm_num [parameterMoment, Fin.sum_univ_succ]
  all_goals field_simp
  all_goals ring

end
end Li2Unified.Proofs.PrimeEdge

#print axioms Li2Unified.Proofs.PrimeEdge.fixedCornerBlock_det

end


end
