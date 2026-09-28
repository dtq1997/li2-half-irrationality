module
public import Li2Unified.Modular.Base.ParameterMoments
public import Mathlib.Tactic.FieldSimp

set_option backward.privateInPublic true

@[expose] public section

/-! Exact polynomial shift identity for the variable-parameter moment functional. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

lemma parameterG_add (z : ℚ) (P Q : ℚ[X]) :
    parameterG z (P+Q) = parameterG z P + parameterG z Q := by
  unfold parameterG
  exact Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

lemma parameterG_C_mul (z a : ℚ) (P : ℚ[X]) :
    parameterG z (C a*P) = a*parameterG z P := by
  unfold parameterG
  rw [← smul_eq_C_mul, Polynomial.sum_smul_index _ _ _ (fun _ => by simp),
    Polynomial.sum, Polynomial.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma parameterG_monomial (z : ℚ) (k : ℕ) (a : ℚ) :
    parameterG z (monomial k a) = a*parameterMoment z k := by
  simp [parameterG, Polynomial.sum_monomial_index]

lemma parameterG_C_mul_X_pow (z a : ℚ) (k : ℕ) :
    parameterG z (C a*X^k) = a*parameterMoment z k := by
  rw [C_mul_X_pow_eq_monomial, parameterG_monomial]

lemma parameterG_sum {ι : Type*} (z : ℚ) (s : Finset ι) (P : ι → ℚ[X]) :
    parameterG z (∑ i ∈ s, P i) = ∑ i ∈ s, parameterG z (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [parameterG, Polynomial.sum_zero_index]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, parameterG_add, ih]

lemma parameterMoment_full_recurrence (z : ℚ) (hz : z ≠ 1) (k : ℕ) :
    parameterMoment z k = z + z *
      ∑ j ∈ Finset.range (k+1), (Nat.choose k j : ℚ)*parameterMoment z j := by
  have hd : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  cases k with
  | zero =>
    norm_num [parameterMoment]
    field_simp
    <;> ring
  | succ k =>
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul]
    have h : (1-z)*parameterMoment z (k+1) = z*(1+
        ∑ j ∈ Finset.range (k+1), (Nat.choose (k+1) j : ℚ)*parameterMoment z j) := by
      rw [parameterMoment, Fin.sum_univ_eq_sum_range
        (fun j : ℕ => (Nat.choose (k+1) j : ℚ)*parameterMoment z j) (k+1)]
      field_simp
      <;> ring
    nlinarith

lemma parameterG_X_add_one_pow (z : ℚ) (k : ℕ) :
    parameterG z ((X+1)^k) =
      ∑ j ∈ Finset.range (k+1), (Nat.choose k j : ℚ)*parameterMoment z j := by
  have h : ((X:ℚ[X])+1)^k = ∑ j ∈ Finset.range (k+1), C (Nat.choose k j : ℚ)*X^j := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro j _
    simp [mul_comm]
  rw [h, parameterG_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact parameterG_C_mul_X_pow z _ _

theorem parameterG_shift_one (z : ℚ) (hz : z ≠ 1) (P : ℚ[X]) :
    z*parameterG z (P.comp (X+1)) = parameterG z P-z*P.eval 1 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [add_comp, parameterG_add, parameterG_add, eval_add, mul_add, hP, hQ]
    ring
  | monomial k a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp,
      parameterG_C_mul, parameterG_C_mul_X_pow, eval_mul, eval_C, eval_pow, eval_X,
      one_pow, mul_one, parameterG_X_add_one_pow, parameterMoment_full_recurrence z hz k]
    ring

end
end Li2

end
