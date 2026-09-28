module
public import Li2Unified.Modular.Positive.Packed.P061
public import Li2Unified.Modular.Base.PrimeReferenceBounds

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
open Li2Unified.ParameterFamily

set_option maxHeartbeats 800000 in
theorem fixedLowBlock_half_den (i j : Fin 2) :
    (fixedLowBlock (1/2) i j).den ∣ 72 := by
  have hv6 : parameterV (1/2) (6:ℚ[X]) = 0 := parameterV_C _ _
  fin_cases i <;> fin_cases j <;>
    norm_num [fixedLowBlock, fixedLowMoment, rationalPoleV, zeroShapeRegular,
      zeroShapeResidue, Fin.sum_univ_succ, parameterTau, Finset.sum_Icc_succ_top,
      parameterV_zero, parameterV_one, parameterV_sub, parameterV_X, hv6,
      parameterMoment]

set_option maxHeartbeats 600000 in
theorem fixedZeroMoment_half :
    (fun k => fixedZeroMoment (1/2) k) = ![-35/12, 49/4, -179/4, 609/4, -1963/4] := by
  funext k
  have hu6 : parameterU (1/2) (6:ℚ[X]) = 6*parameterMoment (1/2) 0 := parameterU_C _ _
  fin_cases k <;>
    norm_num [fixedZeroMoment, rationalPoleU, zeroShapeRegular, zeroShapeResidue,
      Fin.sum_univ_succ, parameterTau, Finset.sum_Icc_succ_top,
      parameterU_zero, parameterU_one, parameterU_sub, parameterU_X, hu6,
      parameterMoment]

set_option maxHeartbeats 600000 in
theorem fixedHighMoment_half :
    (fun k => fixedHighMoment (1/2) k) = ![-8, 18, -34] := by
  funext k
  have hv3 : parameterV (1/2) (3:ℚ[X]) = 0 := parameterV_C _ _
  have hv7 : parameterV (1/2) (7:ℚ[X]) = 0 := parameterV_C _ _
  have hv3X : parameterV (1/2) (3*X) = 3*parameterMoment (1/2) 0 := parameterV_C_mul_X _ _
  fin_cases k <;>
    norm_num [fixedHighMoment, rationalPoleV, highShapeRegular, highShapeResidue,
      Fin.sum_univ_succ, parameterTau, Finset.sum_Icc_succ_top, parameterV_one,
      parameterV_add, parameterV_sub, parameterV_X, parameterV_X_sq,
      hv3, hv7, hv3X, parameterMoment]

set_option maxHeartbeats 600000 in
theorem fixedCornerBlock_half_den (i j : Fin 6) :
    (fixedCornerBlock (1/2) i j).den ∣ 72 := by
  have hz := congrFun fixedZeroMoment_half
  have hh := congrFun fixedHighMoment_half
  fin_cases i <;> fin_cases j <;>
    norm_num [fixedCornerBlock, arrowSix, hz, hh, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

theorem fixedLowBlock_half_VG (p : ℕ) [Fact p.Prime] (hp : 3 < p) (i j : Fin 2) :
    VG p (fixedLowBlock (1/2) i j) 0 :=
  primeReference_rational_VG hp _ (fixedLowBlock_half_den i j)

theorem fixedCornerBlock_half_VG (p : ℕ) [Fact p.Prime] (hp : 3 < p) (i j : Fin 6) :
    VG p (fixedCornerBlock (1/2) i j) 0 :=
  primeReference_rational_VG hp _ (fixedCornerBlock_half_den i j)

end
end Li2Unified.Proofs.PrimeEdge

#print axioms Li2Unified.Proofs.PrimeEdge.fixedCornerBlock_half_VG

end


end
