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

end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section

def matchingCount (n p : ℕ) (a : Fin p) : ℕ :=
  ((Finset.Icc 1 n).filter (fun j => j % p = a.val)).card

end
end Li2Unified.Proofs.Hermite

end

end
