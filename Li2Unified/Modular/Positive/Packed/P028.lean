module
public import Li2Unified.Modular.Positive.Packed.P025
public import Li2Unified.Modular.Positive.Packed.P027
public import Li2Unified.Modular.Base.PrimeEndpointTerms
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation
open Li2.PrimeSums Finset Filter Topology
open scoped BigOperators

/-- Six affine coefficients of the actual profile on one reciprocal cell. -/
def profileWindowAlpha (A : ℝ) : Fin 6 → ℝ :=
  ![2*A^2+3*A, 2*A^2-A-1, 2*A^2+2*A,
    2*A^2+2*A, 2*A^2+5*A+2, 2*A^2+A-1]
def profileWindowBeta (A : ℝ) : Fin 6 → ℝ :=
  ![-2*A-5, -2*A+1, -2*A-2, -2*A, -2*A-3, -2*A+3]
def profileWindowLeft (A : ℝ) : Fin 6 → ℝ :=
  ![4/(4*A+1), 3/(3*A+1), 2/(2*A+1),
    3/(3*A+2), 4/(4*A+3), 1/(A+1)]
def profileWindowRight (A : ℝ) : Fin 6 → ℝ :=
  ![1/A, 4/(4*A+1), 3/(3*A+1),
    2/(2*A+1), 3/(3*A+2), 4/(4*A+3)]

end
end Li2Unified.Proofs.Arithmetic

end

end
