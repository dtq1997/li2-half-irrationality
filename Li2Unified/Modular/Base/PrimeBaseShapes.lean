module
public import Li2Unified.Modular.Base.PrimePoleExtension
public import Li2Unified.Modular.Base.PrimeNonmatchingInverses
public import Mathlib.Tactic.LinearCombination

set_option backward.privateInPublic true

@[expose] public section

/-! Exact integral simple-pole presentations of r_0, r_L and r_H.
All use the existing four centers and have literal cleared numerators. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def primeIntegralHalf (hp4 : 3 < p) : ℤ_[p] :=
  ↑(integralRationalUnit (p := p) (2:ℚ) (by norm_num)
    (by simpa using (nonmatching_rational_unit (p := p) 0 2 hp.out.pos
      (by rw [Nat.mod_eq_of_lt (by omega)]; omega)).2))⁻¹

theorem primeIntegralHalf_spec (hp4 : 3 < p) : (2:ℤ_[p])*primeIntegralHalf hp4 = 1 := by
  apply PadicInt.ext
  simp only [PadicInt.coe_mul, PadicInt.coe_one, primeIntegralHalf]
  change (2:ℚ_[p])*(2:ℚ)⁻¹ = 1
  norm_num

def primeZeroShapeResidue (hp4 : 3 < p) : Fin 4 → ℤ_[p] :=
  ![0, primeIntegralHalf hp4, -1, primeIntegralHalf hp4]

def primeLowShapeResidue (hp4 : 3 < p) : Fin 4 → ℤ_[p] :=
  ![0, primeIntegralHalf hp4, -4, 9*primeIntegralHalf hp4]

def primeHighShapeResidue : Fin 4 → ℤ_[p] := ![0, 1, -4, 0]

lemma primePoleDenominator_explicit : integralPoleDenominator (primePoleCenters p) =
    X*(X+1)*(X+C 2)*(X+C 3) := by
  simp [integralPoleDenominator, primePoleCenters, Fin.prod_univ_succ]
  simp only [C_ofNat]
  ring

lemma primePoleCofactor_one : integralPoleCofactor (primePoleCenters p) 1 =
    X*(X+C 2)*(X+C 3) := by
  have hs : (univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  simp [integralPoleCofactor, hs, primePoleCenters]
  simp only [C_ofNat]
  ring

lemma primePoleCofactor_two : integralPoleCofactor (primePoleCenters p) 2 =
    X*(X+1)*(X+C 3) := by
  have hs : (univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  simp [integralPoleCofactor, hs, primePoleCenters]
  simp only [C_ofNat]
  ring

lemma primePoleCofactor_three : integralPoleCofactor (primePoleCenters p) 3 =
    X*(X+1)*(X+C 2) := by
  have hs : (univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  simp [integralPoleCofactor, hs, primePoleCenters]
  simp only [C_ofNat]
  ring

theorem primeZeroShape_cleared (hp4 : 3 < p) :
    integralPoleNumerator (primePoleCenters p) 0 (primeZeroShapeResidue hp4) =
      PowerSeries.X := by
  have hc : (2:(ℤ_[p])[X])*C (primeIntegralHalf hp4) = 1 := by
    simpa using congrArg (C : ℤ_[p] → (ℤ_[p])[X]) (primeIntegralHalf_spec hp4)
  have hpoly : (∑ i, C (primeZeroShapeResidue hp4 i)*
      integralPoleCofactor (primePoleCenters p) i : (ℤ_[p])[X]) = X := by
    norm_num [Fin.sum_univ_succ, primeZeroShapeResidue,
      primePoleCofactor_one (p := p), primePoleCofactor_two (p := p),
      primePoleCofactor_three (p := p)]
    simp only [show (Fin.succ (2:Fin 3):Fin 4) = 3 from rfl,
      primePoleCofactor_three (p := p), C_ofNat]
    linear_combination (X*(X+2)^2)*hc
  simpa only [integralPoleNumerator, mul_zero, zero_add, hpoly, Polynomial.coe_X]

theorem primeLowShape_cleared (hp4 : 3 < p) :
    integralPoleNumerator (primePoleCenters p) 0 (primeLowShapeResidue hp4) =
      PowerSeries.X^3 := by
  have hc : (2:(ℤ_[p])[X])*C (primeIntegralHalf hp4) = 1 := by
    simpa using congrArg (C : ℤ_[p] → (ℤ_[p])[X]) (primeIntegralHalf_spec hp4)
  have hpoly : (∑ i, C (primeLowShapeResidue hp4 i)*
      integralPoleCofactor (primePoleCenters p) i : (ℤ_[p])[X]) = X^3 := by
    norm_num [Fin.sum_univ_succ, primeLowShapeResidue,
      primePoleCofactor_one (p := p), primePoleCofactor_two (p := p),
      primePoleCofactor_three (p := p)]
    simp only [show (Fin.succ (2:Fin 3):Fin 4) = 3 from rfl,
      primePoleCofactor_three (p := p), C_ofNat]
    linear_combination (5*X^3+16*X^2+12*X)*hc
  simpa only [integralPoleNumerator, mul_zero, zero_add, hpoly,
    Polynomial.coe_pow, Polynomial.coe_X]

theorem primeHighShape_cleared :
    integralPoleNumerator (primePoleCenters p) 1 (primeHighShapeResidue (p := p)) =
      PowerSeries.X^3*(PowerSeries.X+PowerSeries.C 3) := by
  have he : integralPoleDenominator (primePoleCenters p) +
      (∑ i, C (primeHighShapeResidue (p := p) i)*
        integralPoleCofactor (primePoleCenters p) i : (ℤ_[p])[X]) = X^3*(X+C 3) := by
    norm_num [Fin.sum_univ_succ, primeHighShapeResidue,
      primePoleCofactor_one (p := p), primePoleCofactor_two (p := p),
      primePoleCofactor_three (p := p), primePoleDenominator_explicit (p := p)]
    simp only [C_ofNat]
    ring
  have h := congrArg (fun P : (ℤ_[p])[X] => (P : PowerSeries ℤ_[p])) he
  simpa only [integralPoleNumerator, mul_one, Polynomial.coe_add,
    Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C] using h

end
end Li2

end
