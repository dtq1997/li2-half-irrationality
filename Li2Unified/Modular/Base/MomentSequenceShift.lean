module
public import Li2Unified.Modular.Base.ParameterShift

set_option backward.privateInPublic true

@[expose] public section

/-! The finite polynomial shift argument over an arbitrary commutative ring.
Only the explicit moment recurrence is used; the p-adic instance is supplied later. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {R : Type*} [CommRing R]

def sequenceG (μ : ℕ → R) (P : R[X]) : R := P.sum fun k a => a*μ k

lemma sequenceG_add (μ : ℕ → R) (P Q : R[X]) :
    sequenceG μ (P+Q) = sequenceG μ P+sequenceG μ Q := by
  unfold sequenceG
  exact Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

lemma sequenceG_C_mul (μ : ℕ → R) (a : R) (P : R[X]) :
    sequenceG μ (C a*P) = a*sequenceG μ P := by
  unfold sequenceG
  rw [← smul_eq_C_mul, Polynomial.sum_smul_index _ _ _ (fun _ => by simp),
    Polynomial.sum, Polynomial.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma sequenceG_C_mul_X_pow (μ : ℕ → R) (a : R) (k : ℕ) :
    sequenceG μ (C a*X^k) = a*μ k := by
  rw [C_mul_X_pow_eq_monomial]
  simp [sequenceG, Polynomial.sum_monomial_index]

lemma sequenceG_sum {ι : Type*} (μ : ℕ → R) (s : Finset ι) (P : ι → R[X]) :
    sequenceG μ (∑ i ∈ s, P i) = ∑ i ∈ s, sequenceG μ (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sequenceG, Polynomial.sum_zero_index]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, sequenceG_add, ih]

lemma sequenceG_X_add_one_pow (μ : ℕ → R) (k : ℕ) :
    sequenceG μ ((X+1)^k) = ∑ j ∈ Finset.range (k+1), (Nat.choose k j : R)*μ j := by
  have h : ((X:R[X])+1)^k = ∑ j ∈ Finset.range (k+1), C (Nat.choose k j : R)*X^j := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro j _
    simp [mul_comm]
  rw [h, sequenceG_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact sequenceG_C_mul_X_pow μ _ _

theorem sequenceG_shift_one (μ : ℕ → R) (z : R)
    (hrec : ∀ k, μ k = z+z*∑ j ∈ Finset.range (k+1), (Nat.choose k j : R)*μ j)
    (P : R[X]) : z*sequenceG μ (P.comp (X+1)) = sequenceG μ P-z*P.eval 1 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [add_comp, sequenceG_add, sequenceG_add, eval_add, mul_add, hP, hQ]
    ring
  | monomial k a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp,
      sequenceG_C_mul, sequenceG_C_mul_X_pow, eval_mul, eval_C, eval_pow, eval_X,
      one_pow, mul_one, sequenceG_X_add_one_pow, hrec k]
    ring

theorem sequenceG_shift_scaled (μ : ℕ → R) (z : R)
    (hrec : ∀ k, μ k = z+z*∑ j ∈ Finset.range (k+1), (Nat.choose k j : R)*μ j)
    (P : R[X]) (k : ℕ) :
    z^k*sequenceG μ (P.comp (X+C (k:R))) = sequenceG μ P-
      ∑ j ∈ Finset.range k, z^(j+1)*P.eval ((j:R)+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : (P.comp (X+C (k:R))).comp (X+1) = P.comp (X+C ((k+1:ℕ):R)) := by
      rw [comp_assoc, add_comp, X_comp, C_comp]
      congr 1
      push_cast
      simp only [map_add, map_one]
      ring
    have he : (P.comp (X+C (k:R))).eval 1 = P.eval ((k:R)+1) := by
      simp only [eval_comp, eval_add, eval_X, eval_C, add_comm]
    rw [pow_succ, mul_assoc, ← hc, sequenceG_shift_one μ z hrec, mul_sub, ih,
      Finset.sum_range_succ, he]
    rw [pow_succ]
    ring

end
end Li2

end
