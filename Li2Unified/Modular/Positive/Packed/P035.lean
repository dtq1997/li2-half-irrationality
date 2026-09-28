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

end
end Li2Unified.Proofs.Arithmetic

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

end
end Li2Unified.ParameterFamily

end

end
