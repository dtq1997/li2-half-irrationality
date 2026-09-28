module
public import Li2Unified.Modular.Positive.Packed.P025

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation

/-- Algebraic value of the integral of `c + d*x` from `u` to `v`. -/
def affinePrimitiveDifference (c d u v : ℝ) : ℝ :=
  c * (v-u) + d * (v^2-u^2)/2

/-- The six rational affine pieces indexed by θ = 1/x - A. -/
def profileCellAlgebraicSum (A : ℝ) : ℝ :=
  affinePrimitiveDifference (-2*A-5) (2*A^2+3*A) (4/(4*A+1)) (1/A) +
  affinePrimitiveDifference (-2*A+1) (2*A^2-A-1) (3/(3*A+1)) (4/(4*A+1)) +
  affinePrimitiveDifference (-2*A-2) (2*A^2+2*A) (2/(2*A+1)) (3/(3*A+1)) +
  affinePrimitiveDifference (-2*A) (2*A^2+2*A) (3/(3*A+2)) (2/(2*A+1)) +
  affinePrimitiveDifference (-2*A-3) (2*A^2+5*A+2) (4/(4*A+3)) (3/(3*A+2)) +
  affinePrimitiveDifference (-2*A+3) (2*A^2+A-1) (1/(A+1)) (4/(4*A+3))

/-- Literal rational cancellation for the six-cell formula; floor and integral
bridges are separate. -/
theorem profileCellAlgebraicSum_eq_cellIntegral (A : ℝ) (hA : 1 ≤ A) :
    profileCellAlgebraicSum A = cellIntegral A := by
  have h0 : A ≠ 0 := by linarith
  have h1 : A+1 ≠ 0 := by linarith
  have h2 : 2*A+1 ≠ 0 := by linarith
  have h3 : 3*A+1 ≠ 0 := by linarith
  have h4 : 3*A+2 ≠ 0 := by linarith
  have h5 : 4*A+1 ≠ 0 := by linarith
  have h6 : 4*A+3 ≠ 0 := by linarith
  unfold profileCellAlgebraicSum affinePrimitiveDifference cellIntegral
  field_simp [h0, h1, h2, h3, h4, h5, h6]
  ring

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.profileCellAlgebraicSum_eq_cellIntegral

end


end
