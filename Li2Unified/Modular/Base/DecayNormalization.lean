module
public import Li2Unified.Modular.Base.Gram
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.LinearAlgebra.Matrix.Block

set_option backward.privateInPublic true

@[expose] public section

/-! the binomial normalization of the SAME determinant Q n.
S_n=(4n)!/(n!)^3, F_n=prod_{i<2n}(i!)^2 and Qtilde_n=S_n^(2n)/F_n * Q_n.
The entry numeratorFunctional (4n) (S_n D_n^3 b_a b_b) is U_X applied to
binom(t+n,n)^3 binom(t,a) binom(t,b)/binom(t+4n,4n). -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def Sn (n : ℕ) : ℚ := ((4*n).factorial : ℚ) / ((n.factorial : ℚ)^3)

def Fn (n : ℕ) : ℚ := ∏ i ∈ Finset.range (2*n), ((i.factorial : ℚ))^2

def Qtilde (n : ℕ) : ℚ[X] := C (Sn n ^ (2*n) / Fn n) * Q n

lemma Sn_pos (n : ℕ) : 0 < Sn n := by
  unfold Sn; positivity

lemma Fn_pos (n : ℕ) : 0 < Fn n := by
  unfold Fn
  exact Finset.prod_pos fun i _ => by positivity

lemma Qtilde_scale_pos (n : ℕ) : 0 < Sn n ^ (2*n) / Fn n :=
  div_pos (pow_pos (Sn_pos n) _) (Fn_pos n)

/-- binom(t,a)=descPochhammer a/a!. -/
def binomPoly (a : ℕ) : ℚ[X] := C ((a.factorial : ℚ)⁻¹) * descPochhammer ℚ a

lemma binomPoly_eval_nat (a m : ℕ) : (binomPoly a).eval (m : ℚ) = (m.choose a : ℚ) := by
  rw [binomPoly, eval_mul, eval_C, Nat.cast_choose_eq_descPochhammer_div, div_eq_inv_mul]

lemma binomPoly_natDegree (a : ℕ) : (binomPoly a).natDegree = a := by
  unfold binomPoly
  rw [natDegree_C_mul (inv_ne_zero (by positivity)), descPochhammer_natDegree]

lemma binomPoly_coeff_self (a : ℕ) : (binomPoly a).coeff a = (a.factorial : ℚ)⁻¹ := by
  have h := (monic_descPochhammer ℚ a).coeff_natDegree
  rw [descPochhammer_natDegree] at h
  rw [binomPoly, coeff_C_mul, h, mul_one]

lemma coeffMat_binom_lowerTriangular (h : ℕ) :
    (coeffMat (fun a : Fin h => binomPoly a)).BlockTriangular OrderDual.toDual := by
  intro a k hk
  exact coeff_eq_zero_of_natDegree_lt (by rw [binomPoly_natDegree]; exact hk)

lemma coeffMat_binom_det (h : ℕ) :
    (coeffMat (fun a : Fin h => binomPoly a)).det =
      ∏ i ∈ Finset.range h, ((i.factorial : ℚ))⁻¹ := by
  rw [Matrix.det_of_lowerTriangular _ (coeffMat_binom_lowerTriangular h)]
  rw [← Fin.prod_univ_eq_prod_range (fun i => ((i.factorial : ℚ))⁻¹)]
  exact Finset.prod_congr rfl fun a _ => binomPoly_coeff_self a

lemma coeffMat_binom_det_sq (n : ℕ) :
    (coeffMat (fun a : Fin (2*n) => binomPoly a)).det ^ 2 = (Fn n)⁻¹ := by
  rw [coeffMat_binom_det, Fn, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [inv_pow]

/-- The binomial Gram matrix with the scalar S_n inside every entry. -/
def binomGram (n : ℕ) : Matrix (Fin (2*n)) (Fin (2*n)) ℚ[X] :=
  Matrix.of fun a b =>
    numeratorFunctional (4*n) (C (Sn n) * (D n)^3 * binomPoly a * binomPoly b)

theorem Qtilde_eq_binomGram_det (n : ℕ) : Qtilde n = (binomGram n).det := by
  have hM : binomGram n = C (Sn n) •
      Matrix.of fun a b : Fin (2*n) =>
        numeratorFunctional (4*n) ((D n)^3 * binomPoly a * binomPoly b) := by
    apply Matrix.ext
    intro a b
    simp only [binomGram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← numeratorFunctional_C_mul]
    congr 1
    ring
  rw [hM, Matrix.det_smul, Fintype.card_fin,
    original_gram_basis_change n (fun a => binomPoly a)
      (fun a => by rw [binomPoly_natDegree]; exact a.isLt),
    coeffMat_binom_det_sq, Qtilde, div_eq_mul_inv, C_mul, map_pow]
  ring

/-- n=0 is allowed; no nonvanishing is asserted. -/
theorem Qtilde_ne_zero_iff (n : ℕ) : Qtilde n ≠ 0 ↔ Q n ≠ 0 := by
  rw [Qtilde, Ne, mul_eq_zero, not_or, C_eq_zero]
  exact and_iff_right (Qtilde_scale_pos n).ne'

end
end Li2

end
