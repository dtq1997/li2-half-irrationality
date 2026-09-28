module
public import Li2Unified.Modular.Base.PrimeBlockIndex
public import Li2Unified.Modular.Base.PrimeCrossValuation

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ}

/-- The original numerator matrix, explicitly reordered and scaled only by p-units. -/
def primeNormalizedMatrix (hp4 : 3 < p) :
    Matrix (PrimeBlockIndex p) (PrimeBlockIndex p) ℚ[X] := fun x y =>
  C (primeBlockUnitScale hp4 x * primeBlockUnitScale hp4 y) *
    primeOriginalNumeratorEntry p (by omega)
      ((primeOriginalBlockEquiv hp4).symm x)
      ((primeOriginalBlockEquiv hp4).symm y)

lemma primeNormalizedMatrix_symm (hp4 : 3 < p) (x y : PrimeBlockIndex p) :
    primeNormalizedMatrix hp4 x y = primeNormalizedMatrix hp4 y x := by
  simp only [primeNormalizedMatrix, primeOriginalNumeratorEntry, mul_comm]

lemma primeNormalizedMatrix_GV_of_original [Fact p.Prime] (hp4 : 3 < p)
    (x y : PrimeBlockIndex p) (r : ℚ)
    (h : GV p (primeOriginalNumeratorEntry p (by omega)
      ((primeOriginalBlockEquiv hp4).symm x)
      ((primeOriginalBlockEquiv hp4).symm y)) r) :
    GV p (primeNormalizedMatrix hp4 x y) r := by
  have hx : VG p (primeBlockUnitScale hp4 x) 0 := by
    right
    rw [(primeBlockUnitScale_unit hp4 x).2]
    norm_num
  have hy : VG p (primeBlockUnitScale hp4 y) 0 := by
    right
    rw [(primeBlockUnitScale_unit hp4 y).2]
    norm_num
  simpa only [primeNormalizedMatrix, zero_add] using GV.C_mul (hx.mul hy) h

lemma rational_prime_unit_finset_prod [Fact p.Prime] {ι : Type*}
    (S : Finset ι) (u : ι → ℚ)
    (hu : ∀ i ∈ S, u i ≠ 0 ∧ padicValRat p (u i) = 0) :
    (∏ i ∈ S, u i) ≠ 0 ∧ padicValRat p (∏ i ∈ S, u i) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      have hA := hu a (Finset.mem_insert_self a S)
      have hS := ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_insert ha]
      exact ⟨mul_ne_zero hA.1 hS.1, by rw [padicValRat.mul hA.1 hS.1, hA.2, hS.2, add_zero]⟩

/-- Exact determinant connection, before any leading-block or error estimate. -/
theorem primeNormalizedMatrix_det (hp4 : 3 < p) :
    (primeNormalizedMatrix hp4).det =
      C ((∏ x : PrimeBlockIndex p, primeBlockUnitScale hp4 x)^2) *
        (Matrix.of (primeOriginalNumeratorEntry p (by omega))).det := by
  classical
  let B : Matrix (PrimeBlockIndex p) (PrimeBlockIndex p) ℚ[X] :=
    (Matrix.of (primeOriginalNumeratorEntry p (by omega))).submatrix
      (primeOriginalBlockEquiv hp4).symm (primeOriginalBlockEquiv hp4).symm
  have he : primeNormalizedMatrix hp4 =
      Matrix.of (fun x y => C (primeBlockUnitScale hp4 x) *
        (C (primeBlockUnitScale hp4 y) * B x y)) := by
    ext x y
    simp only [primeNormalizedMatrix, Matrix.of_apply, B, Matrix.submatrix_apply, C_mul]
    ring
  rw [he, Matrix.det_mul_column]
  change (∏ x : PrimeBlockIndex p, C (primeBlockUnitScale hp4 x)) *
    (Matrix.of (fun x y => C (primeBlockUnitScale hp4 y) * B x y)).det = _
  rw [Matrix.det_mul_row]
  have hb : B.det = (Matrix.of (primeOriginalNumeratorEntry p (by omega))).det :=
    Matrix.det_submatrix_equiv_self (primeOriginalBlockEquiv hp4).symm _
  rw [hb, ← map_prod, ← mul_assoc, ← C_mul, ← pow_two]

def primeNormalizedDetScale (hp4 : 3 < p) : ℚ :=
  ((∏ x : PrimeBlockIndex p, primeBlockUnitScale hp4 x) *
    (coeffMat fun a => (primeOriginalBasis p (by omega) a).map (Int.castRingHom ℚ)).det)^2

theorem primeNormalizedMatrix_det_eq_Q (hp4 : 3 < p) :
    (primeNormalizedMatrix hp4).det = C (primeNormalizedDetScale hp4) * Q (p-1) := by
  classical
  have hA : Matrix.of (primeOriginalNumeratorEntry p (by omega)) =
      Matrix.of (fun a b => numeratorFunctional (4*(p-1))
        ((D (p-1))^3 * (primeOriginalBasis p (by omega) a).map (Int.castRingHom ℚ) *
          (primeOriginalBasis p (by omega) b).map (Int.castRingHom ℚ))) := by
    ext a b
    simp only [Matrix.of_apply, primeOriginalNumeratorEntry, Polynomial.map_mul, mul_assoc]
  rw [primeNormalizedMatrix_det, hA, primeOriginalBasis_gram]
  simp only [primeNormalizedDetScale, mul_pow, C_mul, C_pow]
  ring

theorem primeNormalizedDetScale_unit [Fact p.Prime] (hp4 : 3 < p) :
    primeNormalizedDetScale hp4 ≠ 0 ∧ padicValRat p (primeNormalizedDetScale hp4) = 0 := by
  have hs := rational_prime_unit_finset_prod (p := p) Finset.univ
    (primeBlockUnitScale hp4) (fun x _ => primeBlockUnitScale_unit hp4 x)
  have hb := primeOriginalBasis_det_unit p (by omega)
  have hne := mul_ne_zero hs.1 hb.1
  unfold primeNormalizedDetScale
  refine ⟨pow_ne_zero 2 hne, ?_⟩
  rw [padicValRat.pow hne, padicValRat.mul hs.1 hb.1, hs.2, hb.2]
  norm_num

end
end Li2

end
