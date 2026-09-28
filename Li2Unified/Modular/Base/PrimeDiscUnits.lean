module
public import Li2Unified.Modular.Base.PrimeNonmatchingInverses

set_option backward.privateInPublic true

@[expose] public section

/-! The actual nonmatching numerator and denominator unit on each residue disc.
The rational-polynomial map is literal; leading residues are not assumed. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem integralNonmatchingDiscPolynomial_map (a m : ℕ) :
    (integralNonmatchingDiscPolynomial (p := p) a m).map
      (algebraMap ℤ_[p] ℚ_[p]) =
    (nonmatchingDiscProduct p a m).map (Rat.castHom ℚ_[p]) := by
  simp [integralNonmatchingDiscPolynomial, nonmatchingDiscProduct,
    nonmatchingDiscIndices, Polynomial.map_prod]

def nonmatchingDiscConstant (a m : ℕ) : ℤ_[p] :=
  ∏ j ∈ nonmatchingDiscIndices p a m, ((j:ℤ_[p])-(a:ℤ_[p]))

lemma affineForward_constant_error (b d : ℤ_[p]) (n : ℕ) :
    ‖PowerSeries.coeff n
      (PowerSeries.C b*PowerSeries.X+PowerSeries.C d-PowerSeries.C d)‖ ≤ ‖b‖ := by
  simp only [add_sub_cancel_right, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  split_ifs <;> simp

theorem nonmatchingDiscPolynomial_constant_error (a m n : ℕ) :
    ‖PowerSeries.coeff n
      ((integralNonmatchingDiscPolynomial (p := p) a m : PowerSeries ℤ_[p])-
        PowerSeries.C (nonmatchingDiscConstant a m))‖ ≤ ‖(p:ℤ_[p])‖ := by
  unfold integralNonmatchingDiscPolynomial nonmatchingDiscConstant
  rw [polynomial_coe_finset_prod]
  apply powerSeries_prod_constant_error_bound _ _ _ _ (norm_nonneg _)
  intro j _ k
  simpa only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_X] using affineForward_constant_error (p:ℤ_[p])
      ((j:ℤ_[p])-(a:ℤ_[p])) k

lemma powerSeries_pow_constant_error_bound (f : PowerSeries ℤ_[p]) (a : ℤ_[p])
    (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n, ‖PowerSeries.coeff n (f-PowerSeries.C a)‖ ≤ B) (d n : ℕ) :
    ‖PowerSeries.coeff n (f^d-PowerSeries.C (a^d))‖ ≤ B := by
  induction d generalizing n with
  | zero => simpa using hB
  | succ d ih =>
    rw [pow_succ, pow_succ]
    exact powerSeries_mul_constant_error_bound _ _ _ _ B hB ih hf n

lemma restricted_pow (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (d : ℕ) : PowerSeries.IsRestricted 1 (f^d) := by
  induction d with
  | zero => simpa using PowerSeries.isRestricted_one (R := ℤ_[p]) 1
  | succ d ih =>
    rw [pow_succ]
    exact PowerSeries.isRestricted.mul 1 ih hf

def primeDiscUnit (a : ℕ) (ha : a < p) : PowerSeries ℤ_[p] :=
  (integralNonmatchingDiscPolynomial (p := p) a (p-1) : PowerSeries ℤ_[p])^3 *
    nonmatchingDiscInverse a (4*(p-1)) ha

def primeDiscUnitConstant (a : ℕ) (ha : a < p) : ℤ_[p] :=
  nonmatchingDiscConstant a (p-1)^3 * nonmatchingInverseConstant a (4*(p-1)) ha

theorem primeDiscUnit_isRestricted (a : ℕ) (ha : a < p) :
    PowerSeries.IsRestricted 1 (primeDiscUnit a ha) := by
  exact PowerSeries.isRestricted.mul 1
    (restricted_pow _ (polynomial_isRestricted _) 3)
    (nonmatchingDiscInverse_isRestricted a _ ha)

theorem primeDiscUnit_constant_error (a : ℕ) (ha : a < p) (n : ℕ) :
    ‖PowerSeries.coeff n (primeDiscUnit a ha-PowerSeries.C
      (primeDiscUnitConstant a ha))‖ ≤ ‖(p:ℤ_[p])‖ := by
  apply powerSeries_mul_constant_error_bound _ _ _ _ _ (norm_nonneg _)
  · exact powerSeries_pow_constant_error_bound _ _ _ (norm_nonneg _)
      (nonmatchingDiscPolynomial_constant_error a (p-1)) 3
  · exact nonmatchingDiscInverse_constant_error a _ ha

theorem primeDiscUnit_cleared (a : ℕ) (ha : a < p) :
    primeDiscUnit a ha *
      (integralNonmatchingDiscPolynomial (p := p) a (4*(p-1)) : PowerSeries ℤ_[p]) =
      (integralNonmatchingDiscPolynomial (p := p) a (p-1) : PowerSeries ℤ_[p])^3 := by
  rw [primeDiscUnit, mul_assoc, nonmatchingDiscInverse_identity, mul_one]

end
end Li2

end
