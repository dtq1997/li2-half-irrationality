module
public import Li2Unified.Modular.Positive.Packed.P000
public import Li2Unified.Modular.Base.ParameterDifferentialDissection
public import Li2Unified.Modular.Base.ParameterPoleValues
public import Li2Unified.Modular.Base.DecayNormalization

set_option backward.privateInPublic true

@[expose] public section

section
/-! The same original numerator, denominator and 2n determinant.
Only the moment parameter and pole weights vary. No nonvanishing is assumed. -/
open Polynomial
open scoped BigOperators
namespace Li2Unified.ParameterFamily
noncomputable section

 def slope (lam : ℚ) (n k : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 (4*n), Li2.residue n k j * (j : ℚ) * lam⁻¹^j

 def intercept (lam : ℚ) (n k : ℕ) : ℚ :=
  Li2.parameterU lam (Li2.polynomialPart n k) -
    ∑ j ∈ Finset.Icc 1 (4*n),
      Li2.residue n k j * (j : ℚ) * lam⁻¹^j * Li2.parameterTau lam j

 def B (lam : ℚ) (n : ℕ) : Matrix (Fin (2*n)) (Fin (2*n)) ℚ :=
  fun i j => slope lam n (i.val+j.val)

 def A (lam : ℚ) (n : ℕ) : Matrix (Fin (2*n)) (Fin (2*n)) ℚ :=
  fun i j => intercept lam n (i.val+j.val)

 def Q (lam : ℚ) (n : ℕ) : ℚ[X] :=
  Matrix.det ((X : ℚ[X]) • (B lam n).map C + (A lam n).map C)

 theorem Q_natDegree_le (lam : ℚ) (n : ℕ) : (Q lam n).natDegree ≤ 2*n := by
  simpa [Q] using Polynomial.natDegree_det_X_add_C_le (B lam n) (A lam n)

 def Qtilde (lam : ℚ) (n : ℕ) : ℚ[X] :=
  C (Li2.Sn n ^ (2*n) / Li2.Fn n) * Q lam n

 theorem Qtilde_ne_zero_iff (lam : ℚ) (n : ℕ) : Qtilde lam n ≠ 0 ↔ Q lam n ≠ 0 := by
  rw [Qtilde, Ne, mul_eq_zero, not_or, C_eq_zero]
  exact and_iff_right (Li2.Qtilde_scale_pos n).ne'

 def numeratorFunctional (lam : ℚ) (m : ℕ) (F : ℚ[X]) : ℚ[X] :=
  C (Li2.parameterU lam (F /ₘ Li2.D m)) +
    ∑ j ∈ Finset.Icc 1 m,
      C (F.eval (-(j:ℚ)) / ∏ l ∈ (Finset.Icc 1 m).erase j, ((l:ℚ)-(j:ℚ))) *
        (C ((j:ℚ)*lam⁻¹^j) * (X-C (Li2.parameterTau lam j)))

 theorem numeratorFunctional_entry (lam : ℚ) (n k : ℕ) :
    numeratorFunctional lam (4*n) (Li2.numerator n k) =
      C (intercept lam n k) + X * C (slope lam n k) := by
  unfold numeratorFunctional intercept slope Li2.polynomialPart Li2.residue
  simp only [mul_sub, ← mul_assoc, ← C_mul]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [← map_sum, map_sub]
  ring

end
end Li2Unified.ParameterFamily

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section

theorem pole_index_decompose (p j : ℕ) :
    j = j % p + p * (j / p) := by
  simpa using (Nat.mod_add_div j p).symm

theorem pole_index_window (p m j : ℕ) (hp : 0 < p)
    (hm : m < p * p) (hj : j ≤ m) : j / p < p := by
  exact (Nat.div_lt_iff_lt_mul hp).mpr (lt_of_le_of_lt hj hm)

theorem pole_index_zero_boundary (p j : ℕ)
    (hj : 0 < j) (hmod : j % p = 0) : 0 < (j / p : ℕ) := by
  have hdec := pole_index_decompose p j
  rw [hmod] at hdec
  by_contra h
  have hq : (j / p : ℕ) = 0 := Nat.eq_zero_of_not_pos h
  simp [hq] at hdec
  omega

theorem matching_affine_factor (p j : ℕ) (a : Fin p)
    (hmod : j % p = a.val) (u : ℚ) :
    (-(a.val : ℚ) + (p : ℚ) * u) + (j : ℚ) =
      (p : ℚ) * (u + ((j / p : ℕ) : ℚ)) := by
  have hj : j = a.val + p * (j / p) := by
    simpa [hmod] using pole_index_decompose p j
  have hjq := congrArg (fun v : ℕ => (v : ℚ)) hj
  push_cast at hjq
  linear_combination hjq

theorem disc_D_factor (n p : ℕ) (a : Fin p) (u : ℚ) :
    (Li2.D n).eval (-(a.val : ℚ) + (p : ℚ) * u) =
      (∏ j ∈ (Finset.Icc 1 n).filter (fun j => j % p = a.val),
        (p : ℚ) * (u + ((j / p : ℕ) : ℚ))) *
      (∏ j ∈ (Finset.Icc 1 n).filter (fun j => j % p ≠ a.val),
        ((-(a.val : ℚ) + (p : ℚ) * u) + (j : ℚ))) := by
  classical
  let s := Finset.Icc 1 n
  let f : ℕ → ℚ := fun j => (-(a.val : ℚ) + (p : ℚ) * u) + (j : ℚ)
  calc
    (Li2.D n).eval (-(a.val : ℚ) + (p : ℚ) * u) = ∏ j ∈ s, f j := by
      simp [Li2.D, s, f, Polynomial.eval_prod]
    _ = (∏ j ∈ s with j % p = a.val, f j) *
        (∏ j ∈ s with j % p ≠ a.val, f j) := by
      exact (Finset.prod_filter_mul_prod_filter_not s
        (fun j : ℕ => j % p = a.val) f).symm
    _ = (∏ j ∈ (Finset.Icc 1 n).filter (fun j => j % p = a.val),
          (p : ℚ) * (u + ((j / p : ℕ) : ℚ))) *
        (∏ j ∈ (Finset.Icc 1 n).filter (fun j => j % p ≠ a.val),
          ((-(a.val : ℚ) + (p : ℚ) * u) + (j : ℚ))) := by
      congr 1
      · apply Finset.prod_congr rfl
        intro j hj
        exact matching_affine_factor p j a (Finset.mem_filter.mp hj).2 u

#print axioms pole_index_zero_boundary
#print axioms disc_D_factor

end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section

def matchingCount (n p : ℕ) (a : Fin p) : ℕ :=
  ((Finset.Icc 1 n).filter (fun j => j % p = a.val)).card

def matchingProduct (n p : ℕ) (a : Fin p) (u : ℚ) : ℚ :=
  ∏ j ∈ (Finset.Icc 1 n).filter (fun j => j % p = a.val),
    (u + ((j / p : ℕ) : ℚ))

def nonmatchingProduct (n p : ℕ) (a : Fin p) (u : ℚ) : ℚ :=
  ∏ j ∈ (Finset.Icc 1 n).filter (fun j => j % p ≠ a.val),
    ((-(a.val : ℚ) + (p : ℚ) * u) + (j : ℚ))

theorem disc_D_scaled (n p : ℕ) (a : Fin p) (u : ℚ) :
    (Li2.D n).eval (-(a.val : ℚ) + (p : ℚ) * u) =
      (p : ℚ) ^ matchingCount n p a *
        matchingProduct n p a u * nonmatchingProduct n p a u := by
  rw [disc_D_factor]
  let s := (Finset.Icc 1 n).filter (fun j => j % p = a.val)
  have hs : (∏ j ∈ s, (p : ℚ) * (u + ((j / p : ℕ) : ℚ))) =
      (p : ℚ) ^ s.card * ∏ j ∈ s, (u + ((j / p : ℕ) : ℚ)) := by
    rw [Finset.prod_mul_distrib]
    simp
  simpa only [matchingCount, matchingProduct, nonmatchingProduct, s] using
    congrArg (fun v : ℚ => v * nonmatchingProduct n p a u) hs

def localRationalCore (n p : ℕ) (a : Fin p) (u : ℚ) : ℚ :=
  (Li2.D n).eval (-(a.val : ℚ) + (p : ℚ) * u) ^ 3 /
    (Li2.D (4 * n)).eval (-(a.val : ℚ) + (p : ℚ) * u)

def nonmatchingRatio (n p : ℕ) (a : Fin p) (u : ℚ) : ℚ :=
  nonmatchingProduct n p a u ^ 3 / nonmatchingProduct (4 * n) p a u

def matchingRatio (n p : ℕ) (a : Fin p) (u : ℚ) : ℚ :=
  matchingProduct n p a u ^ 3 / matchingProduct (4 * n) p a u

theorem localRationalCore_scaled (n p : ℕ) (a : Fin p) (u : ℚ)
    (hm : matchingProduct (4 * n) p a u ≠ 0)
    (hu : nonmatchingProduct (4 * n) p a u ≠ 0) :
    (p : ℚ) ^ matchingCount (4 * n) p a * localRationalCore n p a u =
      (p : ℚ) ^ (3 * matchingCount n p a) *
        nonmatchingRatio n p a u * matchingRatio n p a u := by
  have hpN : 0 < p := by have := a.isLt; omega
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hpN)
  rw [localRationalCore, nonmatchingRatio, matchingRatio,
    disc_D_scaled n p a u, disc_D_scaled (4 * n) p a u]
  rw [show 3 * matchingCount n p a = matchingCount n p a * 3 by omega, pow_mul]
  field_simp [hm, hu, hpq]

theorem localRationalCore_zpow (n p : ℕ) (a : Fin p) (u : ℚ)
    (hm : matchingProduct (4 * n) p a u ≠ 0)
    (hu : nonmatchingProduct (4 * n) p a u ≠ 0) :
    localRationalCore n p a u =
      (p : ℚ) ^ ((3 * matchingCount n p a : ℕ) - (matchingCount (4 * n) p a : ℤ)) *
        nonmatchingRatio n p a u * matchingRatio n p a u := by
  have hpN : 0 < p := by have := a.isLt; omega
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hpN)
  have hscaled := localRationalCore_scaled n p a u hm hu
  calc
    localRationalCore n p a u =
        ((p : ℚ) ^ (3 * matchingCount n p a) *
          nonmatchingRatio n p a u * matchingRatio n p a u) /
          (p : ℚ) ^ matchingCount (4 * n) p a := by
      apply (eq_div_iff (pow_ne_zero _ hpq)).mpr
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
    _ = (p : ℚ) ^ ((3 * matchingCount n p a : ℕ) -
          (matchingCount (4 * n) p a : ℤ)) *
          nonmatchingRatio n p a u * matchingRatio n p a u := by
      rw [zpow_sub₀ hpq]
      simp only [zpow_natCast]
      ring

#print axioms disc_D_scaled
#print axioms localRationalCore_zpow

end
end Li2Unified.Proofs.Hermite

end


end
