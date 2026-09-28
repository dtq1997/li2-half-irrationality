module
public import Li2Unified.Modular.Base.ClassBasisDegree
public import Mathlib.Algebra.Polynomial.Div

set_option backward.privateInPublic true

@[expose] public section

/-! Exact, finite polynomial identities for the local expansions of a product basis.
These identities do not assume a p-adic completion or a local functional. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {R : Type*} [CommRing R] [Nontrivial R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem polynomial_scaled_expansion (P : R[X]) (a b : R) :
    ∃ A : R[X], P.comp (C a + C b * X) = C (P.eval a) + C b * A := by
  obtain ⟨Q, hQ⟩ := X_sub_C_dvd_sub_C_eval (p := P) (a := a)
  refine ⟨X * Q.comp (C a + C b * X), ?_⟩
  have hP : P = (X-C a)*Q + C (P.eval a) := (sub_eq_iff_eq_add).mp hQ
  conv_lhs => rw [hP]
  rw [add_comp, mul_comp, sub_comp, X_comp, C_comp, C_comp, add_sub_cancel_left]
  ring

theorem polynomial_scaled_factor (P : R[X]) (a b : R) (m : ℕ)
    (h : (X-C a)^m ∣ P) :
    ∃ A : R[X], P.comp (C a + C b * X) = C (b^m) * X^m * A := by
  obtain ⟨A, rfl⟩ := h
  refine ⟨A.comp (C a + C b * X), ?_⟩
  rw [mul_comp, pow_comp, sub_comp, X_comp, C_comp, add_sub_cancel_left,
    mul_pow, ← C_pow]

lemma fullClassProduct_split (γ : ι → R) (L : ι → ℕ) (a : ι) :
    fullClassProduct γ L = classProduct γ L a * (X-C (γ a))^(L a) := by
  exact (Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ a)).symm

lemma classBasisPoly_other_dvd (γ : ι → R) (L : ι → ℕ) (a b : ι) (i : ℕ)
    (hba : b ≠ a) : (X-C (γ b))^(L b) ∣ classBasisPoly γ L a i := by
  apply Dvd.dvd.mul_right
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hba, Finset.mem_univ b⟩)

theorem classBasisPoly_own_expansion (γ : ι → R) (L : ι → ℕ) (a : ι) (i : ℕ) (b : R) :
    ∃ A : R[X], (classBasisPoly γ L a i).comp (C (γ a)+C b*X) =
      C (b^i) * X^i * (C ((classProduct γ L a).eval (γ a)) + C b*A) := by
  obtain ⟨A, hA⟩ := polynomial_scaled_expansion (classProduct γ L a) (γ a) b
  refine ⟨A, ?_⟩
  rw [classBasisPoly, mul_comp, pow_comp, sub_comp, X_comp, C_comp,
    add_sub_cancel_left, hA, mul_pow, ← C_pow]
  ring

theorem classBasisPoly_other_expansion (γ : ι → R) (L : ι → ℕ) (a c : ι) (i : ℕ) (b : R)
    (hca : c ≠ a) :
    ∃ A : R[X], (classBasisPoly γ L a i).comp (C (γ c)+C b*X) =
      C (b^(L c)) * X^(L c) * A :=
  polynomial_scaled_factor _ _ _ _ (classBasisPoly_other_dvd γ L a c i hca)

theorem fullClassProduct_expansion (γ : ι → R) (L : ι → ℕ) (a : ι) (b : R) :
    ∃ A : R[X], (fullClassProduct γ L).comp (C (γ a)+C b*X) =
      C (b^(L a)) * X^(L a) * (C ((classProduct γ L a).eval (γ a)) + C b*A) := by
  rw [fullClassProduct_split γ L a]
  exact classBasisPoly_own_expansion γ L a (L a) b

end

section Field
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem classProduct_eval_ne_zero (γ : ι → F) (hγ : Function.Injective γ)
    (L : ι → ℕ) (a : ι) : (classProduct γ L a).eval (γ a) ≠ 0 := by
  simp only [classProduct, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro b hb
  apply pow_ne_zero
  exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hb).1 (hγ he).symm)

end Field
end Li2

end
