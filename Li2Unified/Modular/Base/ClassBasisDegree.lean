module
public import Li2Unified.Modular.Base.ClassBasis

set_option backward.privateInPublic true

@[expose] public section

/-! Literal products and degree bounds for a CRT basis over a commutative ring. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {R : Type*} [CommRing R] [Nontrivial R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def classProduct (γ : ι → R) (L : ι → ℕ) (a : ι) : R[X] :=
  ∏ b ∈ Finset.univ.erase a, (X-C (γ b))^(L b)

def classBasisPoly (γ : ι → R) (L : ι → ℕ) (a : ι) (i : ℕ) : R[X] :=
  classProduct γ L a * (X-C (γ a))^i

def fullClassProduct (γ : ι → R) (L : ι → ℕ) : R[X] :=
  ∏ a, (X-C (γ a))^(L a)

lemma classProduct_monic (γ : ι → R) (L : ι → ℕ) (a : ι) :
    (classProduct γ L a).Monic :=
  monic_prod_of_monic _ _ (fun b _ => (monic_X_sub_C _).pow _)

lemma fullClassProduct_monic (γ : ι → R) (L : ι → ℕ) :
    (fullClassProduct γ L).Monic :=
  monic_prod_of_monic _ _ (fun a _ => (monic_X_sub_C _).pow _)

lemma classProduct_natDegree (γ : ι → R) (L : ι → ℕ) (a : ι) :
    (classProduct γ L a).natDegree = ∑ b ∈ Finset.univ.erase a, L b := by
  unfold classProduct
  rw [natDegree_prod_of_monic _ _ (fun b _ => (monic_X_sub_C _).pow _)]
  apply Finset.sum_congr rfl
  intro b _
  rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]

lemma fullClassProduct_natDegree (γ : ι → R) (L : ι → ℕ) :
    (fullClassProduct γ L).natDegree = ∑ a, L a := by
  unfold fullClassProduct
  rw [natDegree_prod_of_monic _ _ (fun a _ => (monic_X_sub_C _).pow _)]
  apply Finset.sum_congr rfl
  intro a _
  rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]

theorem classBasisPoly_natDegree_lt (γ : ι → R) (L : ι → ℕ) (a : ι) (i : ℕ)
    (hi : i < L a) : (classBasisPoly γ L a i).natDegree < ∑ b, L b := by
  unfold classBasisPoly
  rw [(classProduct_monic γ L a).natDegree_mul ((monic_X_sub_C _).pow _),
    classProduct_natDegree, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [← Finset.sum_erase_add Finset.univ L (Finset.mem_univ a)]
  exact Nat.add_lt_add_left hi _

lemma classBasisPoly_map {S : Type*} [CommRing S] [Nontrivial S]
    (f : R →+* S) (γ : ι → R) (L : ι → ℕ) (a : ι) (i : ℕ) :
    (classBasisPoly γ L a i).map f = classBasisPoly (fun b => f (γ b)) L a i := by
  simp only [classBasisPoly, classProduct, Polynomial.map_mul, Polynomial.map_prod,
    Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

end
end Li2

end
