module
public import Li2Unified.Modular.Positive.Packed.P031
public import Li2Unified.Modular.Positive.Packed.P034
public import Li2Unified.Modular.Positive.Packed.P030
public import Li2Unified.Modular.Positive.Packed.P001

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation
open Li2.PrimeSums Finset
open scoped BigOperators

/-- Exact finite prime profile sum on the fixed interval `(n/200,n]`. -/
theorem profileWindowClosedSum_eq_profile (n : ℕ) (hn : 0 < n) :
    profileWindowClosedSum n =
      ∑ p ∈ Finset.Ioc ⌊((1:ℝ)/200)*(n:ℝ)⌋₊ n,
        ((n:ℝ)*profile ((p:ℝ)/(n:ℝ))*cPrime p) := by
  let f : ℕ → ℝ := fun p => (n:ℝ)*profile ((p:ℝ)/(n:ℝ))*cPrime p
  calc
    profileWindowClosedSum n =
        ∑ A ∈ Finset.Ico (1:ℕ) 200, ∑ j : Fin 6,
          ∑ p ∈ Finset.Ioc
            ⌊profileWindowLeft A j*(n:ℝ)⌋₊
            ⌊profileWindowRight A j*(n:ℝ)⌋₊, f p := by
      unfold profileWindowClosedSum
      apply Finset.sum_congr rfl
      intro A hA
      have hA1 : 1 ≤ A := (Finset.mem_Ico.mp hA).1
      apply Finset.sum_congr rfl
      intro j _
      exact profileWindowRow_eq_profile A n hA1 hn j
    _ = ∑ A ∈ Finset.Ico (1:ℕ) 200,
          ∑ p ∈ Finset.Ioc
            ⌊((1:ℝ)/((A:ℝ)+1))*(n:ℝ)⌋₊
            ⌊((1:ℝ)/(A:ℝ))*(n:ℝ)⌋₊, f p := by
      apply Finset.sum_congr rfl
      intro A hA
      exact profileWindowCell_partition A n (Finset.mem_Ico.mp hA).1 f
    _ = ∑ p ∈ Finset.Ioc ⌊((1:ℝ)/200)*(n:ℝ)⌋₊ n, f p := by
      simpa [show ((199:ℝ)+1)=200 by norm_num] using!
        profileWindowCells_partition 199 n (by decide) f

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.profileWindowClosedSum_eq_profile

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation
open Li2.PrimeSums Finset
open scoped BigOperators

/-- All six profile windows and all `N` reciprocal cells partition exactly
the prime interval `(n/(N+1),n]`. -/
theorem profileWindowClosedSumN_eq_profile (N n : ℕ)
    (hN : 1 ≤ N) (hn : 0 < n) :
    profileWindowClosedSumN N n =
      ∑ p ∈ Finset.Ioc ⌊((1:ℝ)/((N:ℝ)+1))*(n:ℝ)⌋₊ n,
        ((n:ℝ)*profile ((p:ℝ)/(n:ℝ))*cPrime p) := by
  let f : ℕ → ℝ := fun p => (n:ℝ)*profile ((p:ℝ)/(n:ℝ))*cPrime p
  calc
    profileWindowClosedSumN N n =
        ∑ A ∈ Finset.Ico (1:ℕ) (N+1), ∑ j : Fin 6,
          ∑ p ∈ Finset.Ioc
            ⌊profileWindowLeft A j*(n:ℝ)⌋₊
            ⌊profileWindowRight A j*(n:ℝ)⌋₊, f p := by
      unfold profileWindowClosedSumN
      apply Finset.sum_congr rfl
      intro A hA
      have hA1 : 1 ≤ A := (Finset.mem_Ico.mp hA).1
      apply Finset.sum_congr rfl
      intro j _
      exact profileWindowRow_eq_profile A n hA1 hn j
    _ = ∑ A ∈ Finset.Ico (1:ℕ) (N+1),
          ∑ p ∈ Finset.Ioc
            ⌊((1:ℝ)/((A:ℝ)+1))*(n:ℝ)⌋₊
            ⌊((1:ℝ)/(A:ℝ))*(n:ℝ)⌋₊, f p := by
      apply Finset.sum_congr rfl
      intro A hA
      exact profileWindowCell_partition A n (Finset.mem_Ico.mp hA).1 f
    _ = ∑ p ∈ Finset.Ioc ⌊((1:ℝ)/((N:ℝ)+1))*(n:ℝ)⌋₊ n, f p := by
      simpa using! profileWindowCells_partition N n hN f

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.profileWindowClosedSumN_eq_profile

end

section
/-! Literal equalities with the preserved negative-half family.
Primitive normalization is added in its own subsequent module. -/
open Polynomial
namespace Li2Unified.ParameterFamily
noncomputable section

 theorem slope_negHalf (n k : ℕ) : slope (-1/2) n k = Li2.slope n k := by
  simp only [slope, Li2.slope, show (-1/2:ℚ)⁻¹ = -2 by norm_num]

 theorem intercept_negHalf (n k : ℕ) : intercept (-1/2) n k = Li2.intercept n k := by
  simp only [intercept, Li2.intercept, Li2.parameterU_negHalf,
    Li2.parameterTau_negHalf, show (-1/2:ℚ)⁻¹ = -2 by norm_num]

 theorem B_negHalf (n : ℕ) : B (-1/2) n = Li2.B n := by
  ext i j
  exact slope_negHalf n (i.val+j.val)

 theorem A_negHalf (n : ℕ) : A (-1/2) n = Li2.A n := by
  ext i j
  exact intercept_negHalf n (i.val+j.val)

 theorem Q_negHalf (n : ℕ) : Q (-1/2) n = Li2.Q n := by
  rw [Q, B_negHalf, A_negHalf]
  rfl

 theorem Qtilde_negHalf (n : ℕ) : Qtilde (-1/2) n = Li2.Qtilde n := by
  rw [Qtilde, Q_negHalf]
  rfl

 theorem numeratorFunctional_negHalf (m : ℕ) (F : ℚ[X]) :
    numeratorFunctional (-1/2) m F = Li2.numeratorFunctional m F := by
  simp only [numeratorFunctional, Li2.numeratorFunctional, Li2.parameterU_negHalf,
    Li2.parameterTau_negHalf, show (-1/2:ℚ)⁻¹ = -2 by norm_num]

end
end Li2Unified.ParameterFamily

end


end
