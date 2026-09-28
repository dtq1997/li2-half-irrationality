module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

set_option backward.privateInPublic true

@[expose] public section

section
/-! Division-free determinant for the six-by-six corner shape.
All entries are free over a commutative ring; zero pivots are permitted.
Identifying the actual prime matrix with this shape remains separate. -/
namespace Li2Unified.ParameterFamily
noncomputable section
variable {R : Type*} [CommRing R]

def arrowSix (a₀ a₁ a₂ b₀ b₁ b₂ z₀₀ z₀₁ z₁₁ c₀ c₁ t : R) :
    Matrix (Fin 6) (Fin 6) R :=
  !![a₀, 0, 0, 0, 0, b₀;
     0, a₁, 0, 0, 0, b₁;
     0, 0, a₂, 0, 0, b₂;
     0, 0, 0, z₀₀, z₀₁, c₀;
     0, 0, 0, z₀₁, z₁₁, c₁;
     b₀, b₁, b₂, c₀, c₁, t]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem arrowSix_det (a₀ a₁ a₂ b₀ b₁ b₂ z₀₀ z₀₁ z₁₁ c₀ c₁ t : R) :
    (arrowSix a₀ a₁ a₂ b₀ b₁ b₂ z₀₀ z₀₁ z₁₁ c₀ c₁ t).det =
      a₀*a₁*a₂*((z₀₀*z₁₁-z₀₁^2)*t-c₀^2*z₁₁+2*c₀*c₁*z₀₁-c₁^2*z₀₀)-
        (z₀₀*z₁₁-z₀₁^2)*(b₀^2*a₁*a₂+b₁^2*a₀*a₂+b₂^2*a₀*a₁) := by
  have hdet0 : (!![a₂, 0, 0, b₂; 0, z₀₀, z₀₁, c₀; 0, z₀₁, z₁₁, c₁; b₂, c₀, c₁, t] : Matrix (Fin 4) (Fin 4) R).det =
      (a₂)*((z₀₀)*((z₁₁)*(t)- (c₁)*(c₁))- (z₀₁)*((z₀₁)*(t)- (c₁)*(c₀))+ (c₀)*((z₀₁)*(c₁)- (z₁₁)*(c₀)))- (b₂)*(- (z₀₀)*(- (z₁₁)*(b₂))+ (z₀₁)*(- (z₀₁)*(b₂))) := by
    have hm0 : (!![a₂, 0, 0, b₂; 0, z₀₀, z₀₁, c₀; 0, z₀₁, z₁₁, c₁; b₂, c₀, c₁, t] : Matrix (Fin 4) (Fin 4) R).submatrix Fin.succ ((0 : Fin 4)).succAbove =
        !![z₀₀, z₀₁, c₀; z₀₁, z₁₁, c₁; c₀, c₁, t] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have hm3 : (!![a₂, 0, 0, b₂; 0, z₀₀, z₀₁, c₀; 0, z₀₁, z₁₁, c₁; b₂, c₀, c₁, t] : Matrix (Fin 4) (Fin 4) R).submatrix Fin.succ (((((0 : Fin 1)).succ).succ).succ).succAbove =
        !![0, z₀₀, z₀₁; 0, z₀₁, z₁₁; b₂, c₀, c₁] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rw [hm0, hm3]
    norm_num [Matrix.det_fin_three, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]
    <;> ring
  have hdet1 : (!![0, a₂, 0, 0; 0, 0, z₀₀, z₀₁; 0, 0, z₀₁, z₁₁; b₁, b₂, c₀, c₁] : Matrix (Fin 4) (Fin 4) R).det =
      - (a₂)*(- (z₀₀)*(- (z₁₁)*(b₁))+ (z₀₁)*(- (z₀₁)*(b₁))) := by
    have hm1 : (!![0, a₂, 0, 0; 0, 0, z₀₀, z₀₁; 0, 0, z₀₁, z₁₁; b₁, b₂, c₀, c₁] : Matrix (Fin 4) (Fin 4) R).submatrix Fin.succ (((0 : Fin 3)).succ).succAbove =
        !![0, z₀₀, z₀₁; 0, z₀₁, z₁₁; b₁, c₀, c₁] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rw [hm1]
    norm_num [Matrix.det_fin_three, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]
    <;> ring
  have hdet2 : (!![a₁, 0, 0, 0, b₁; 0, a₂, 0, 0, b₂; 0, 0, z₀₀, z₀₁, c₀; 0, 0, z₀₁, z₁₁, c₁; b₁, b₂, c₀, c₁, t] : Matrix (Fin 5) (Fin 5) R).det =
      (a₁)*((a₂)*((z₀₀)*((z₁₁)*(t)- (c₁)*(c₁))- (z₀₁)*((z₀₁)*(t)- (c₁)*(c₀))+ (c₀)*((z₀₁)*(c₁)- (z₁₁)*(c₀)))- (b₂)*(- (z₀₀)*(- (z₁₁)*(b₂))+ (z₀₁)*(- (z₀₁)*(b₂))))+ (b₁)*(- (a₂)*(- (z₀₀)*(- (z₁₁)*(b₁))+ (z₀₁)*(- (z₀₁)*(b₁)))) := by
    have hm0 : (!![a₁, 0, 0, 0, b₁; 0, a₂, 0, 0, b₂; 0, 0, z₀₀, z₀₁, c₀; 0, 0, z₀₁, z₁₁, c₁; b₁, b₂, c₀, c₁, t] : Matrix (Fin 5) (Fin 5) R).submatrix Fin.succ ((0 : Fin 5)).succAbove =
        !![a₂, 0, 0, b₂; 0, z₀₀, z₀₁, c₀; 0, z₀₁, z₁₁, c₁; b₂, c₀, c₁, t] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have hm4 : (!![a₁, 0, 0, 0, b₁; 0, a₂, 0, 0, b₂; 0, 0, z₀₀, z₀₁, c₀; 0, 0, z₀₁, z₁₁, c₁; b₁, b₂, c₀, c₁, t] : Matrix (Fin 5) (Fin 5) R).submatrix Fin.succ ((((((0 : Fin 1)).succ).succ).succ).succ).succAbove =
        !![0, a₂, 0, 0; 0, 0, z₀₀, z₀₁; 0, 0, z₀₁, z₁₁; b₁, b₂, c₀, c₁] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rw [hm0, hm4]
    rw [hdet0, hdet1]
    norm_num [Matrix.det_fin_three, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]
    <;> ring
  have hdet3 : (!![0, a₂, 0, 0; 0, 0, z₀₀, z₀₁; 0, 0, z₀₁, z₁₁; b₀, b₂, c₀, c₁] : Matrix (Fin 4) (Fin 4) R).det =
      - (a₂)*(- (z₀₀)*(- (z₁₁)*(b₀))+ (z₀₁)*(- (z₀₁)*(b₀))) := by
    have hm1 : (!![0, a₂, 0, 0; 0, 0, z₀₀, z₀₁; 0, 0, z₀₁, z₁₁; b₀, b₂, c₀, c₁] : Matrix (Fin 4) (Fin 4) R).submatrix Fin.succ (((0 : Fin 3)).succ).succAbove =
        !![0, z₀₀, z₀₁; 0, z₀₁, z₁₁; b₀, c₀, c₁] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rw [hm1]
    norm_num [Matrix.det_fin_three, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]
    <;> ring
  have hdet4 : (!![0, a₁, 0, 0, 0; 0, 0, a₂, 0, 0; 0, 0, 0, z₀₀, z₀₁; 0, 0, 0, z₀₁, z₁₁; b₀, b₁, b₂, c₀, c₁] : Matrix (Fin 5) (Fin 5) R).det =
      - (a₁)*(- (a₂)*(- (z₀₀)*(- (z₁₁)*(b₀))+ (z₀₁)*(- (z₀₁)*(b₀)))) := by
    have hm1 : (!![0, a₁, 0, 0, 0; 0, 0, a₂, 0, 0; 0, 0, 0, z₀₀, z₀₁; 0, 0, 0, z₀₁, z₁₁; b₀, b₁, b₂, c₀, c₁] : Matrix (Fin 5) (Fin 5) R).submatrix Fin.succ (((0 : Fin 4)).succ).succAbove =
        !![0, a₂, 0, 0; 0, 0, z₀₀, z₀₁; 0, 0, z₀₁, z₁₁; b₀, b₂, c₀, c₁] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rw [hm1]
    rw [hdet3]
    norm_num [Matrix.det_fin_three, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]
    <;> ring
  have hdet5 : (!![a₀, 0, 0, 0, 0, b₀; 0, a₁, 0, 0, 0, b₁; 0, 0, a₂, 0, 0, b₂; 0, 0, 0, z₀₀, z₀₁, c₀; 0, 0, 0, z₀₁, z₁₁, c₁; b₀, b₁, b₂, c₀, c₁, t] : Matrix (Fin 6) (Fin 6) R).det =
      (a₀)*((a₁)*((a₂)*((z₀₀)*((z₁₁)*(t)- (c₁)*(c₁))- (z₀₁)*((z₀₁)*(t)- (c₁)*(c₀))+ (c₀)*((z₀₁)*(c₁)- (z₁₁)*(c₀)))- (b₂)*(- (z₀₀)*(- (z₁₁)*(b₂))+ (z₀₁)*(- (z₀₁)*(b₂))))+ (b₁)*(- (a₂)*(- (z₀₀)*(- (z₁₁)*(b₁))+ (z₀₁)*(- (z₀₁)*(b₁)))))- (b₀)*(- (a₁)*(- (a₂)*(- (z₀₀)*(- (z₁₁)*(b₀))+ (z₀₁)*(- (z₀₁)*(b₀))))) := by
    have hm0 : (!![a₀, 0, 0, 0, 0, b₀; 0, a₁, 0, 0, 0, b₁; 0, 0, a₂, 0, 0, b₂; 0, 0, 0, z₀₀, z₀₁, c₀; 0, 0, 0, z₀₁, z₁₁, c₁; b₀, b₁, b₂, c₀, c₁, t] : Matrix (Fin 6) (Fin 6) R).submatrix Fin.succ ((0 : Fin 6)).succAbove =
        !![a₁, 0, 0, 0, b₁; 0, a₂, 0, 0, b₂; 0, 0, z₀₀, z₀₁, c₀; 0, 0, z₀₁, z₁₁, c₁; b₁, b₂, c₀, c₁, t] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have hm5 : (!![a₀, 0, 0, 0, 0, b₀; 0, a₁, 0, 0, 0, b₁; 0, 0, a₂, 0, 0, b₂; 0, 0, 0, z₀₀, z₀₁, c₀; 0, 0, 0, z₀₁, z₁₁, c₁; b₀, b₁, b₂, c₀, c₁, t] : Matrix (Fin 6) (Fin 6) R).submatrix Fin.succ (((((((0 : Fin 1)).succ).succ).succ).succ).succ).succAbove =
        !![0, a₁, 0, 0, 0; 0, 0, a₂, 0, 0; 0, 0, 0, z₀₀, z₀₁; 0, 0, 0, z₀₁, z₁₁; b₀, b₁, b₂, c₀, c₁] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rw [hm0, hm5]
    rw [hdet2, hdet4]
    norm_num [Matrix.det_fin_three, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]
    <;> ring
  change (!![a₀, 0, 0, 0, 0, b₀; 0, a₁, 0, 0, 0, b₁; 0, 0, a₂, 0, 0, b₂; 0, 0, 0, z₀₀, z₀₁, c₀; 0, 0, 0, z₀₁, z₁₁, c₁; b₀, b₁, b₂, c₀, c₁, t] : Matrix (Fin 6) (Fin 6) R).det = _
  rw [hdet5]
  ring

end
end Li2Unified.ParameterFamily

end


end
