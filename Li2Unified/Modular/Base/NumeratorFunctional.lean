module
public import Li2Unified.Modular.Base.PoleFamily
public import Mathlib.Tactic.LinearCombination

set_option backward.privateInPublic true

@[expose] public section

/-! Linearity in the numerator, adapted from the generic part of Apery/Arith/BasisChange.lean in mo271/Zeta5 by Moritz Firsching (https://github.com/mo271/Zeta5, commit f19a1960609f7d38e7b63fd2acb05e6f60a7b741), Apache-2.0; see licenses/LICENSE-Zeta5.txt. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

lemma divByMonic_add {q : ℚ[X]} (hq : q.Monic) (F G : ℚ[X]) :
    (F+G) /ₘ q = F /ₘ q + G /ₘ q := by
  refine (div_modByMonic_unique (F /ₘ q + G /ₘ q) (F %ₘ q + G %ₘ q) hq ⟨?_, ?_⟩).1
  · have hF := modByMonic_add_div F q
    have hG := modByMonic_add_div G q
    rw [mul_add]
    linear_combination hF + hG
  · exact (degree_add_le _ _).trans_lt
      (max_lt (degree_modByMonic_lt _ hq) (degree_modByMonic_lt _ hq))

lemma divByMonic_C_mul {q : ℚ[X]} (hq : q.Monic) (c : ℚ) (F : ℚ[X]) :
    (C c * F) /ₘ q = C c * (F /ₘ q) := by
  refine (div_modByMonic_unique (C c * (F /ₘ q)) (C c * (F %ₘ q)) hq ⟨?_, ?_⟩).1
  · have hF := modByMonic_add_div F q
    linear_combination C c * hF
  · rw [← smul_eq_C_mul]
    exact (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)

lemma polynomialMoment_add (F G : ℚ[X]) :
    polynomialMoment (F+G) = polynomialMoment F + polynomialMoment G := by
  unfold polynomialMoment
  exact Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

lemma polynomialMoment_C_mul (c : ℚ) (F : ℚ[X]) :
    polynomialMoment (C c * F) = c * polynomialMoment F := by
  unfold polynomialMoment
  rw [← smul_eq_C_mul, Polynomial.sum_smul_index _ _ _ (fun _ => by simp),
    Polynomial.sum, Polynomial.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

def numeratorFunctional (m : ℕ) (F : ℚ[X]) : ℚ[X] :=
  C (polynomialMoment (F /ₘ D m)) +
    ∑ j ∈ Finset.Icc 1 m,
      C (F.eval (-(j:ℚ)) / ∏ l ∈ (Finset.Icc 1 m).erase j, ((l:ℚ)-(j:ℚ))) *
        (C ((j:ℚ)*(-2:ℚ)^j) * (X-C (tau j)))

lemma numeratorFunctional_add (m : ℕ) (F G : ℚ[X]) :
    numeratorFunctional m (F+G) = numeratorFunctional m F + numeratorFunctional m G := by
  unfold numeratorFunctional
  rw [divByMonic_add (D_monic m), polynomialMoment_add, map_add]
  simp only [eval_add, add_div, map_add, add_mul, Finset.sum_add_distrib]
  ring

lemma numeratorFunctional_C_mul (m : ℕ) (c : ℚ) (F : ℚ[X]) :
    numeratorFunctional m (C c * F) = C c * numeratorFunctional m F := by
  unfold numeratorFunctional
  rw [divByMonic_C_mul (D_monic m), polynomialMoment_C_mul, map_mul, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [eval_mul, eval_C, mul_div_assoc, map_mul]
  ring

lemma numeratorFunctional_sum {ι : Type*} (m : ℕ) (s : Finset ι) (F : ι → ℚ[X]) :
    numeratorFunctional m (∑ i ∈ s, F i) = ∑ i ∈ s, numeratorFunctional m (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := numeratorFunctional_C_mul m 0 0
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, numeratorFunctional_add, ih]

theorem numeratorFunctional_entry (n k : ℕ) :
    numeratorFunctional (4*n) (numerator n k) =
      C (intercept n k) + X * C (slope n k) := by
  unfold numeratorFunctional intercept slope polynomialPart residue
  simp only [mul_sub, ← mul_assoc, ← C_mul]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [← map_sum, map_sub]
  ring

end
end Li2

end
