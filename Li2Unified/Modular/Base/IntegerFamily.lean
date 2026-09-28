module
public import Li2Unified.Modular.Base.MomentArithmetic

set_option backward.privateInPublic true

@[expose] public section

/-! The polynomial quotient of the original rational family has integer coefficients. -/
open Polynomial
namespace Li2
noncomputable section

def integerD (m : ℕ) : ℤ[X] := ∏ j ∈ Finset.Icc 1 m, (X + C (j:ℤ))

lemma integerD_monic (m : ℕ) : (integerD m).Monic := by
  apply monic_prod_of_monic
  intro j _
  exact monic_X_add_C _

lemma integerD_map (m : ℕ) : (integerD m).map (Int.castRingHom ℚ) = D m := by
  simp only [integerD, D, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_C, Int.coe_castRingHom, Int.cast_natCast]

def integerPolynomialPart (n k : ℕ) : ℤ[X] :=
  (X^k * (integerD n)^3) /ₘ integerD (4*n)

theorem integerPolynomialPart_map (n k : ℕ) :
    (integerPolynomialPart n k).map (Int.castRingHom ℚ) = polynomialPart n k := by
  unfold integerPolynomialPart polynomialPart numerator
  rw [map_divByMonic _ (integerD_monic _)]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, integerD_map]

theorem polynomialPart_GV (p : ℕ) (n k : ℕ) : GV p (polynomialPart n k) 0 := by
  rw [← integerPolynomialPart_map]
  intro j
  rw [coeff_map]
  exact VG.intCast _

end
end Li2

end
