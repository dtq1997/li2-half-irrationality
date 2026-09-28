module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

set_option backward.privateInPublic true

@[expose] public section

/-! These exact finite certificates do not assert the all-prime edge theorem. -/
namespace Li2
open Matrix

def lowBlock : Matrix (Fin 2) (Fin 2) ℚ :=
  !![95/4, -253/4; -253/4, 2093/12]

theorem lowBlock_det : lowBlock.det = 851/6 := by
  norm_num [lowBlock, Matrix.det_fin_two]

def edgeBlock : Matrix (Fin 6) (Fin 6) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => -16
  | 0, 5 => 46/3
  | 1, 1 => -2
  | 1, 5 => -23/6
  | 2, 2 => -4/3
  | 2, 5 => 23/18
  | 3, 3 => -113/2
  | 3, 4 => 285/2
  | 3, 5 => 253/4
  | 4, 3 => 285/2
  | 4, 4 => -759/2
  | 4, 5 => -2093/12
  | 5, 0 => 46/3
  | 5, 1 => -23/6
  | 5, 2 => 23/18
  | 5, 3 => 253/4
  | 5, 4 => -2093/12
  | 5, 5 => -7609/72
  | _, _ => 0

def edgeL : Matrix (Fin 6) (Fin 6) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 2 => 1
  | 3, 3 => 1
  | 4, 3 => -285/113
  | 4, 4 => 1
  | 5, 0 => -23/24
  | 5, 1 => 23/12
  | 5, 2 => -23/24
  | 5, 3 => -253/226
  | 5, 4 => 10097/13626
  | 5, 5 => 1
  | _, _ => 0

def edgeU : Matrix (Fin 6) (Fin 6) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => -16
  | 0, 5 => 46/3
  | 1, 1 => -2
  | 1, 5 => -23/6
  | 2, 2 => -4/3
  | 2, 5 => 23/18
  | 3, 3 => -113/2
  | 3, 4 => 285/2
  | 3, 5 => 253/4
  | 4, 4 => -2271/113
  | 4, 5 => -10097/678
  | 5, 5 => -6935/12112
  | _, _ => 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
lemma edgeBlock_LU : edgeBlock = edgeL * edgeU := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [edgeBlock, edgeL, edgeU, Matrix.mul_apply, Fin.sum_univ_succ]

lemma edgeL_lower : edgeL.BlockTriangular OrderDual.toDual := by
  intro i j h
  change i < j at h
  fin_cases i <;> fin_cases j <;> norm_num [edgeL, Fin.lt_def] at *

lemma edgeU_upper : edgeU.BlockTriangular id := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [edgeU, Fin.lt_def] at *

theorem edgeBlock_det : edgeBlock.det = 27740 := by
  rw [edgeBlock_LU, Matrix.det_mul, Matrix.det_of_lowerTriangular edgeL edgeL_lower,
    Matrix.det_of_upperTriangular edgeU_upper]
  norm_num [edgeL, edgeU, Fin.prod_univ_succ]

theorem exceptional_factors : (851 : ℤ) = 23*37 ∧ (27740 : ℤ) = 4*5*19*73 := by
  norm_num

end Li2

end
