module
public import Li2Unified.Modular.Base.PrimeBaseShapes
public import Li2Unified.Modular.Base.ParameterDifferentialDissection
public import Li2Unified.Modular.Base.FiniteCertificates

set_option backward.privateInPublic true

@[expose] public section

/-! Literal rational four-pole presentations and their U/V values.
The cleared identities identify every tested monomial multiple; fixed values
are computed from the original parameter moments and finite pole sums. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section

def rationalPoleDenominator : ℚ[X] := X*(X+1)*(X+2)*(X+3)

def rationalPoleCofactor : Fin 4 → ℚ[X] :=
  ![(X+1)*(X+2)*(X+3), X*(X+2)*(X+3), X*(X+1)*(X+3), X*(X+1)*(X+2)]

def rationalPoleNumerator (f : ℚ[X]) (r : Fin 4 → ℚ) : ℚ[X] :=
  rationalPoleDenominator*f + ∑ j, C (r j)*rationalPoleCofactor j

def rationalPoleU (z : ℚ) (f : ℚ[X]) (r : Fin 4 → ℚ) : ℚ[X] :=
  C (parameterU z f) + ∑ j : Fin 4,
    C (r j*(j.val:ℚ)*z⁻¹^j.val)*(X-C (parameterTau z j.val))

def rationalPoleV (z : ℚ) (f : ℚ[X]) (r : Fin 4 → ℚ) : ℚ[X] :=
  C (parameterV z f) + ∑ j : Fin 4,
    C (-r j*z⁻¹^j.val)*(X-C (parameterTau z j.val))

def zeroShapeRegular (k : Fin 5) : ℚ[X] := ![0,0,0,1,X-6] k

def zeroShapeResidue (k : Fin 5) : Fin 4 → ℚ :=
  ![0, (1/2)*(-1)^k.val, -(-2)^k.val, (1/2)*(-3)^k.val]

def highShapeRegular (k : Fin 3) : ℚ[X] := ![1,X-3,X^2-3*X+7] k

def highShapeResidue (k : Fin 3) : Fin 4 → ℚ :=
  ![0, (-1)^k.val, -4*(-2)^k.val, 0]

theorem zeroShape_cleared (k : Fin 5) :
    rationalPoleNumerator (zeroShapeRegular k) (zeroShapeResidue k) = X^(k.val+1) := by
  fin_cases k <;> apply Polynomial.funext <;> intro x <;>
    norm_num [rationalPoleNumerator, rationalPoleDenominator, rationalPoleCofactor,
      zeroShapeRegular, zeroShapeResidue, highShapeRegular, highShapeResidue,
      Fin.sum_univ_succ, eval_finset_sum] <;> ring

theorem highShape_cleared (k : Fin 3) :
    rationalPoleNumerator (highShapeRegular k) (highShapeResidue k) = X^(k.val+3)*(X+3) := by
  fin_cases k <;> apply Polynomial.funext <;> intro x <;>
    norm_num [rationalPoleNumerator, rationalPoleDenominator, rationalPoleCofactor,
      zeroShapeRegular, zeroShapeResidue, highShapeRegular, highShapeResidue,
      Fin.sum_univ_succ, eval_finset_sum] <;> ring

lemma parameterG_zero (z : ℚ) : parameterG z 0 = 0 := by simp [parameterG]
lemma parameterG_C (z a : ℚ) : parameterG z (C a) = a*parameterMoment z 0 := by
  simpa only [monomial_zero_left] using parameterG_monomial z 0 a
lemma parameterG_one (z : ℚ) : parameterG z 1 = parameterMoment z 0 := by
  simpa using parameterG_C z 1
lemma parameterG_X (z : ℚ) : parameterG z X = parameterMoment z 1 := by
  simpa using parameterG_C_mul_X_pow z 1 1

lemma parameterU_add (z : ℚ) (f g : ℚ[X]) :
    parameterU z (f+g) = parameterU z f + parameterU z g := by
  simp [parameterU, mul_add, derivative_add, parameterG_add]
lemma parameterU_sub (z : ℚ) (f g : ℚ[X]) :
    parameterU z (f-g) = parameterU z f - parameterU z g := by
  simp [parameterU, mul_sub, derivative_sub, parameterG_sub]
lemma parameterU_zero (z : ℚ) : parameterU z 0 = 0 := by
  simp [parameterU, parameterG_zero]
lemma parameterU_C (z a : ℚ) : parameterU z (C a) = a*parameterMoment z 0 := by
  simp [parameterU, derivative_mul, parameterG_C]
lemma parameterU_one (z : ℚ) : parameterU z 1 = parameterMoment z 0 := by
  simpa using parameterU_C z 1
lemma parameterU_X (z : ℚ) : parameterU z X = 2*parameterMoment z 1 := by
  simp [parameterU, derivative_mul, parameterG_add, parameterG_X]
  ring

lemma parameterV_add (z : ℚ) (f g : ℚ[X]) :
    parameterV z (f+g) = parameterV z f + parameterV z g := by
  simp [parameterV, derivative_add, parameterG_add]
lemma parameterV_sub (z : ℚ) (f g : ℚ[X]) :
    parameterV z (f-g) = parameterV z f - parameterV z g := by
  simp [parameterV, derivative_sub, parameterG_sub]
lemma parameterV_zero (z : ℚ) : parameterV z 0 = 0 := by
  simp [parameterV, parameterG_zero]
lemma parameterV_C (z a : ℚ) : parameterV z (C a) = 0 := by
  simp [parameterV, parameterG_zero]
lemma parameterV_one (z : ℚ) : parameterV z 1 = 0 := by
  simpa using parameterV_C z 1
lemma parameterV_X (z : ℚ) : parameterV z X = parameterMoment z 0 := by
  simp [parameterV, parameterG_one]
lemma parameterV_C_mul_X (z a : ℚ) : parameterV z (C a*X) = a*parameterMoment z 0 := by
  simp [parameterV, derivative_mul, parameterG_C]
lemma parameterV_X_sq (z : ℚ) : parameterV z (X^2) = 2*parameterMoment z 1 := by
  simp [parameterV, derivative_pow, parameterG_C_mul, parameterG_X]

lemma parameterMoment_negHalf_zero : parameterMoment (-1/2) 0 = -1/3 := by
  norm_num [parameterMoment]
lemma parameterMoment_negHalf_one : parameterMoment (-1/2) 1 = -2/9 := by
  norm_num [parameterMoment, Fin.sum_univ_succ]

lemma parameterU_natCast (z : ℚ) (n : ℕ) : parameterU z (n:ℚ[X]) = n*parameterMoment z 0 := by
  simpa using parameterU_C z (n:ℚ)
lemma parameterV_natCast (z : ℚ) (n : ℕ) : parameterV z (n:ℚ[X]) = 0 := by
  simpa using parameterV_C z (n:ℚ)
lemma parameterV_natCast_mul_X (z : ℚ) (n : ℕ) :
    parameterV z ((n:ℚ[X])*X) = n*parameterMoment z 0 := by
  simpa using parameterV_C_mul_X z (n:ℚ)

lemma parameterTau_negHalf_small (j : Fin 4) :
    parameterTau (-1/2) j.val = ![0,-1/2,-7/16,-65/144] j := by
  fin_cases j <;> norm_num [parameterTau, Finset.sum_Icc_succ_top]

lemma parameterU_six : parameterU (-(1/2)) (6:ℚ[X]) = -2 := by
  change parameterU (-(1/2)) (C 6) = -2
  rw [parameterU_C]
  norm_num [parameterMoment]
lemma parameterV_three : parameterV (-(1/2)) (3:ℚ[X]) = 0 := parameterV_C _ _
lemma parameterV_six : parameterV (-(1/2)) (6:ℚ[X]) = 0 := parameterV_C _ _
lemma parameterV_seven : parameterV (-(1/2)) (7:ℚ[X]) = 0 := parameterV_C _ _
lemma parameterV_three_X : parameterV (-(1/2)) (3*X:ℚ[X]) = -1 := by
  change parameterV (-(1/2)) (C 3*X) = -1
  rw [parameterV_C_mul_X]
  norm_num [parameterMoment]

theorem zeroShape_U_values (k : Fin 5) :
    (rationalPoleU (-1/2) (zeroShapeRegular k) (zeroShapeResidue k)).eval 0 =
      ![-113/12,95/4,-253/4,2093/12,-17773/36] k := by
  fin_cases k <;>
    norm_num [rationalPoleU, zeroShapeRegular, zeroShapeResidue, Fin.sum_univ_succ,
      parameterU_six, parameterTau, Finset.sum_Icc_succ_top, parameterU_zero, parameterU_one, parameterU_sub, parameterU_X,
      show (6:ℚ[X]) = C 6 from rfl, parameterU_C, parameterU_natCast,
      parameterMoment_negHalf_zero, parameterMoment_negHalf_one, parameterMoment, Fin.sum_univ_succ]

  all_goals norm_num only [parameterU_six]

theorem lowShape_V_values (k : Fin 3) :
    (rationalPoleV (-1/2) (zeroShapeRegular ⟨k.val+2,by omega⟩)
      (zeroShapeResidue ⟨k.val+2,by omega⟩)).eval 0 =
      ![95/4,-253/4,2093/12] k := by
  fin_cases k <;>
    norm_num [rationalPoleV, zeroShapeRegular, zeroShapeResidue, Fin.sum_univ_succ,
      parameterV_six, parameterTau, Finset.sum_Icc_succ_top, parameterV_zero, parameterV_one, parameterV_sub, parameterV_X,
      show (6:ℚ[X]) = C 6 from rfl, parameterV_C, parameterV_natCast, parameterMoment_negHalf_zero, parameterMoment, Fin.sum_univ_succ]

  all_goals norm_num only [parameterV_six]

theorem highShape_V_values (k : Fin 3) :
    (rationalPoleV (-1/2) (highShapeRegular k) (highShapeResidue k)).eval 0 =
      ![8,-46/3,266/9] k := by
  fin_cases k <;>
    norm_num [rationalPoleV, highShapeRegular, highShapeResidue, Fin.sum_univ_succ,
      parameterV_three, parameterV_seven, parameterV_three_X, parameterTau, Finset.sum_Icc_succ_top, parameterV_one, parameterV_add, parameterV_sub, parameterV_X,
      show (3:ℚ[X]) = C 3 from rfl, show (7:ℚ[X]) = C 7 from rfl,
      parameterV_C_mul_X, parameterV_X_sq, parameterV_C, parameterV_natCast, parameterV_natCast_mul_X,
      parameterMoment_negHalf_zero, parameterMoment_negHalf_one, parameterMoment, Fin.sum_univ_succ]

  all_goals norm_num only [parameterV_three, parameterV_seven, parameterV_three_X]

theorem lowBlock_from_functional (i j : Fin 2) :
    lowBlock i j = (rationalPoleV (-1/2)
      (zeroShapeRegular ⟨i.val+j.val+2,by omega⟩)
      (zeroShapeResidue ⟨i.val+j.val+2,by omega⟩)).eval 0 := by
  have h := lowShape_V_values (⟨i.val+j.val,by omega⟩ : Fin 3)
  fin_cases i <;> fin_cases j <;> simpa [lowBlock] using h.symm

end
end Li2

end
