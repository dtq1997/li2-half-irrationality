module
public import Li2Unified.Modular.Base.Definition
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Algebra.Polynomial.Div

set_option backward.privateInPublic true

@[expose] public section

/-! Literal rational family. The polynomial part and every simple-pole residue
are explicit. The recurrence for b_k includes its constant term 1. -/
open Polynomial
open scoped BigOperators
namespace Li2

noncomputable section

def D (m : ℕ) : ℚ[X] := ∏ j ∈ Finset.Icc 1 m, (X + C (j : ℚ))

def moment : ℕ → ℚ
  | 0 => -1/3
  | k+1 => -(1 + ∑ j : Fin (k+1), (Nat.choose (k+1) j.val : ℚ) * moment j.val)/3
termination_by k => k
decreasing_by exact j.isLt

def tau (j : ℕ) : ℚ :=
  ∑ a ∈ Finset.Icc 1 j, (-1/2 : ℚ)^a / (a : ℚ)^2

def numerator (n k : ℕ) : ℚ[X] := X^k * (D n)^3

def polynomialPart (n k : ℕ) : ℚ[X] := numerator n k /ₘ D (4*n)

def residue (n k j : ℕ) : ℚ :=
  (numerator n k).eval (-(j : ℚ)) /
    ∏ l ∈ (Finset.Icc 1 (4*n)).erase j, ((l : ℚ)-(j : ℚ))

def polynomialMoment (p : ℚ[X]) : ℚ :=
  p.sum fun k a => a * ((k+1 : ℕ) : ℚ) * moment k

def slope (n k : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 (4*n), residue n k j * (j : ℚ) * (-2 : ℚ)^j

def intercept (n k : ℕ) : ℚ := polynomialMoment (polynomialPart n k) -
  ∑ j ∈ Finset.Icc 1 (4*n), residue n k j * (j : ℚ) * (-2 : ℚ)^j * tau j

def B (n : ℕ) : Matrix (Fin (2*n)) (Fin (2*n)) ℚ :=
  fun i j => slope n (i.val+j.val)

def A (n : ℕ) : Matrix (Fin (2*n)) (Fin (2*n)) ℚ :=
  fun i j => intercept n (i.val+j.val)

def Q (n : ℕ) : ℚ[X] := Matrix.det ((X : ℚ[X]) • (B n).map C + (A n).map C)

/-- All n, including n=0. No assertion of exact degree or nonvanishing is used. -/
theorem Q_natDegree_le (n : ℕ) : (Q n).natDegree ≤ 2*n := by
  simpa [Q] using Polynomial.natDegree_det_X_add_C_le (B n) (A n)

/-- Mathlib's integer normalization has arbitrary sign, so this intermediate
primitive polynomial is used only in sign-invariant statements. -/
def primitiveQ (n : ℕ) : ℤ[X] :=
  if Q n = 0 then 0 else
    (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q n)).primPart

theorem primitiveQ_isPrimitive (n : ℕ) (hn : Q n ≠ 0) :
    (primitiveQ n).IsPrimitive := by
  simp only [primitiveQ, if_neg hn]
  exact Polynomial.isPrimitive_primPart _

theorem primitiveQ_natDegree_le (n : ℕ) : (primitiveQ n).natDegree ≤ 2*n := by
  unfold primitiveQ
  split_ifs with hn
  · simp
  rw [Polynomial.natDegree_primPart]
  apply le_trans _ (Q_natDegree_le n)
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  apply Polynomial.notMem_support_iff.mp
  intro h
  have hs := IsLocalization.integerNormalization_support (nonZeroDivisors ℤ) (Q n)
  exact (Polynomial.notMem_support_iff.mpr (Polynomial.coeff_eq_zero_of_natDegree_lt hk)) (hs h)

theorem moment_zero : moment 0 = -1/3 := by rw [moment]
theorem moment_one : moment 1 = -2/9 := by norm_num [moment, Fin.sum_univ_succ]
theorem moment_two : moment 2 = -2/27 := by norm_num [moment, Fin.sum_univ_succ]

end
end Li2

end
