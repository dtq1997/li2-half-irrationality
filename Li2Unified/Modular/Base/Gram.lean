module
public import Li2Unified.Modular.Base.NumeratorFunctional

set_option backward.privateInPublic true

@[expose] public section

/-! Generic polynomial Gram basis change, with basis vectors stored as rows. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def coeffMat {h : ℕ} (E : Fin h → ℚ[X]) : Matrix (Fin h) (Fin h) ℚ :=
  fun a k => (E a).coeff k

lemma sum_coeffMat {h : ℕ} (E : Fin h → ℚ[X])
    (hE : ∀ a, (E a).natDegree < h) (a : Fin h) :
    E a = ∑ k : Fin h, C (coeffMat E a k) * X^(k:ℕ) := by
  conv_lhs => rw [as_sum_range' (E a) h (hE a)]
  rw [Finset.sum_range (fun k => monomial k ((E a).coeff k))]
  apply Finset.sum_congr rfl
  intro k _
  exact C_mul_X_pow_eq_monomial.symm

def hankelFor (m h : ℕ) (R : ℚ[X]) : Matrix (Fin h) (Fin h) ℚ[X] :=
  fun i j => numeratorFunctional m (R * X^(i.val+j.val))

theorem gram_basis_change (m h : ℕ) (R : ℚ[X]) (E : Fin h → ℚ[X])
    (hE : ∀ a, (E a).natDegree < h) :
    (Matrix.of fun a b => numeratorFunctional m (R * E a * E b)).det =
      C ((coeffMat E).det^2) * (hankelFor m h R).det := by
  let T := (coeffMat E).map (C : ℚ →+* ℚ[X])
  have hM : (Matrix.of fun a b => numeratorFunctional m (R * E a * E b)) =
      T * hankelFor m h R * T.transpose := by
    apply Matrix.ext
    intro a b
    have he : R * E a * E b = ∑ k : Fin h, ∑ l : Fin h,
        C (coeffMat E a k * coeffMat E b l) * (R * X^(k.val+l.val)) := by
      rw [sum_coeffMat E hE a, sum_coeffMat E hE b]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [C_mul, pow_add]
      ring
    rw [Matrix.of_apply, he, numeratorFunctional_sum]
    simp only [numeratorFunctional_sum, numeratorFunctional_C_mul, Matrix.mul_apply,
      Matrix.transpose_apply, T, Matrix.map_apply, hankelFor, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    rw [C_mul]
    ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  dsimp only [T]
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_pow]
  ring

lemma hankelFor_original (n : ℕ) : hankelFor (4*n) (2*n) ((D n)^3) =
    (X:ℚ[X]) • (B n).map C + (A n).map C := by
  apply Matrix.ext
  intro i j
  simp only [hankelFor, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, B, A, smul_eq_mul]
  rw [mul_comm ((D n)^3)]
  exact (numeratorFunctional_entry n (i.val+j.val)).trans (add_comm _ _)

theorem original_gram_basis_change (n : ℕ) (E : Fin (2*n) → ℚ[X])
    (hE : ∀ a, (E a).natDegree < 2*n) :
    (Matrix.of fun a b => numeratorFunctional (4*n) ((D n)^3 * E a * E b)).det =
      C ((coeffMat E).det^2) * Q n := by
  rw [gram_basis_change _ _ _ _ hE, hankelFor_original]
  rfl

end
end Li2

end
