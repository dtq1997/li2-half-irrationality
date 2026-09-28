module
public import Li2Unified.Modular.Base.PrimeFactorClasses
public import Mathlib.Tactic.Ring

set_option backward.privateInPublic true

@[expose] public section

/-! Exact matching factors of D_m(pu-a). The remaining factors stay explicit;
no local leading unit constant or p-adic estimate is assumed. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def matchingDiscProduct (p a m : ℕ) : ℚ[X] :=
  ∏ j ∈ (Finset.Icc 1 m).filter (fun j => j%p = a),
    (C (p:ℚ)*X+C ((j:ℚ)-(a:ℚ)))

def nonmatchingDiscProduct (p a m : ℕ) : ℚ[X] :=
  ∏ j ∈ (Finset.Icc 1 m).filter (fun j => j%p ≠ a),
    (C (p:ℚ)*X+C ((j:ℚ)-(a:ℚ)))

theorem D_disc_factorization (p a m : ℕ) :
    (D m).comp (C (p:ℚ)*X-C (a:ℚ)) =
      matchingDiscProduct p a m*nonmatchingDiscProduct p a m := by
  unfold matchingDiscProduct nonmatchingDiscProduct
  rw [Finset.prod_filter_mul_prod_filter_not]
  simp only [D, prod_comp, add_comp, X_comp, C_comp]
  apply Finset.prod_congr rfl
  intro j _
  rw [C_sub]
  ring

theorem numerator_matching_zero (p : ℕ) (hp : 0 < p) :
    matchingDiscProduct p 0 (p-1) = 1 := by
  have he : (Finset.Icc 1 (p-1)).filter (fun j => j%p = 0) = ∅ := by
    ext j
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    rw [numerator_prime_factor_class p 0 j hp]
    omega
  simp [matchingDiscProduct, he]

theorem numerator_matching_nonzero (p a : ℕ) (ha0 : 0 < a) (ha : a < p) :
    matchingDiscProduct p a (p-1) = C (p:ℚ)*X := by
  have he : (Finset.Icc 1 (p-1)).filter (fun j => j%p = a) = {a} := by
    ext j
    simpa only [Finset.mem_filter, Finset.mem_singleton, ha0, true_and] using
      numerator_prime_factor_class p a j ha
  simp [matchingDiscProduct, he]

theorem denominator_matching_zero (p : ℕ) (hp : 3 < p) :
    matchingDiscProduct p 0 (4*(p-1)) =
      C ((p:ℚ)^3)*((X+1)*(X+C 2)*(X+C 3)) := by
  have he : (Finset.Icc 1 (4*(p-1))).filter (fun j => j%p = 0) = {p,2*p,3*p} := by
    ext j
    simpa only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] using
      denominator_zero_factor_class p j hp
  rw [matchingDiscProduct, he]
  simp (disch := (simp only [Finset.mem_insert, Finset.mem_singleton]; omega)) only [Finset.prod_insert, Finset.prod_singleton,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, sub_zero,
    C_mul, C_ofNat, C_pow]
  ring

theorem denominator_matching_low (p a : ℕ) (hp : 3 < p)
    (ha0 : 0 < a) (ha : a ≤ p-4) :
    matchingDiscProduct p a (4*(p-1)) =
      C ((p:ℚ)^4)*(X*(X+1)*(X+C 2)*(X+C 3)) := by
  have he : (Finset.Icc 1 (4*(p-1))).filter (fun j => j%p = a) =
      {a,a+p,a+2*p,a+3*p} := by
    ext j
    simpa only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] using
      denominator_low_factor_class p a j hp ha0 ha
  rw [matchingDiscProduct, he]
  simp (disch := (simp only [Finset.mem_insert, Finset.mem_singleton]; omega)) only [Finset.prod_insert, Finset.prod_singleton,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, sub_self, map_zero,
    C_add, C_sub, C_mul, C_ofNat, C_pow, add_zero]
  ring

theorem denominator_matching_high (p a : ℕ) (hp : 3 < p)
    (ha : p-3 ≤ a) (hap : a < p) :
    matchingDiscProduct p a (4*(p-1)) =
      C ((p:ℚ)^3)*(X*(X+1)*(X+C 2)) := by
  have he : (Finset.Icc 1 (4*(p-1))).filter (fun j => j%p = a) =
      {a,a+p,a+2*p} := by
    ext j
    simpa only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] using
      denominator_high_factor_class p a j hp ha hap
  rw [matchingDiscProduct, he]
  simp (disch := (simp only [Finset.mem_insert, Finset.mem_singleton]; omega)) only [Finset.prod_insert, Finset.prod_singleton,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, sub_self, map_zero,
    C_add, C_sub, C_mul, C_ofNat, C_pow, add_zero]
  ring

end
end Li2

end
