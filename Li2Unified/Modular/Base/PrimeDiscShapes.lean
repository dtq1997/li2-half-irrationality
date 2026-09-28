module
public import Li2Unified.Modular.Base.PrimeDiscUnits

set_option backward.privateInPublic true

@[expose] public section

/-! Cleared identities for the ORIGINAL D_(p-1)^3 / D_(4p-4) on every
residue disc. These identify the independently built unit in each local shape;
the later bounded simple-pole functional compatibility is a separate obligation. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def rationalPolynomialSeries : ℚ[X] →+* PowerSeries ℚ_[p] :=
  Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom (Rat.castHom ℚ_[p]))

def primeDiscPolynomialSeries (a m : ℕ) : PowerSeries ℚ_[p] :=
  rationalPolynomialSeries (p := p) ((D m).comp (C (p:ℚ)*X-C (a:ℚ)))

lemma rationalPolynomialSeries_C (q : ℚ) :
    rationalPolynomialSeries (p := p) (C q) = PowerSeries.C (q:ℚ_[p]) := by
  simp [rationalPolynomialSeries]

lemma rationalPolynomialSeries_X :
    rationalPolynomialSeries (p := p) X = PowerSeries.X := by
  simp [rationalPolynomialSeries]

theorem nonmatchingDiscPolynomialSeries_eq (a m : ℕ) :
    rationalPolynomialSeries (p := p) (nonmatchingDiscProduct p a m) =
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
        (integralNonmatchingDiscPolynomial (p := p) a m : PowerSeries ℤ_[p]) := by
  change (((nonmatchingDiscProduct p a m).map (Rat.castHom ℚ_[p]) : (ℚ_[p])[X]) :
    PowerSeries ℚ_[p]) = _
  rw [← integralNonmatchingDiscPolynomial_map, Polynomial.polynomial_map_coe]

theorem primeDiscUnit_cleared_field (a : ℕ) (ha : a < p) :
    PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (primeDiscUnit a ha) *
      rationalPolynomialSeries (nonmatchingDiscProduct p a (4*(p-1))) =
      rationalPolynomialSeries (nonmatchingDiscProduct p a (p-1))^3 := by
  have he := congrArg (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]))
    (primeDiscUnit_cleared a ha)
  simpa only [map_mul, map_pow, ← nonmatchingDiscPolynomialSeries_eq] using he

lemma primeDiscPolynomialSeries_factorization (a m : ℕ) :
    primeDiscPolynomialSeries (p := p) a m =
      rationalPolynomialSeries (matchingDiscProduct p a m) *
        rationalPolynomialSeries (nonmatchingDiscProduct p a m) := by
  rw [primeDiscPolynomialSeries, D_disc_factorization, map_mul]

theorem primeDiscShape_low_cleared (hp4 : 3 < p) (a : ℕ)
    (ha0 : 0 < a) (ha : a ≤ p-4) :
    PowerSeries.C (p:ℚ_[p]) * primeDiscPolynomialSeries a (p-1)^3 *
      ((PowerSeries.X+1)*(PowerSeries.X+PowerSeries.C 2)*
        (PowerSeries.X+PowerSeries.C 3)) =
      primeDiscPolynomialSeries a (4*(p-1)) *
        PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (primeDiscUnit a (by omega)) *
          PowerSeries.X^2 := by
  rw [primeDiscPolynomialSeries_factorization,
    primeDiscPolynomialSeries_factorization,
    numerator_matching_nonzero p a ha0 (by omega),
    denominator_matching_low p a hp4 ha0 ha]
  simp only [map_mul, map_add, map_one, map_pow, rationalPolynomialSeries_C,
    rationalPolynomialSeries_X, Rat.cast_natCast, Rat.cast_ofNat]
  have he := primeDiscUnit_cleared_field (p := p) a (by omega)
  calc
    _ = (PowerSeries.C (p:ℚ_[p]))^4 * PowerSeries.X^3 *
        ((PowerSeries.X+1)*(PowerSeries.X+PowerSeries.C 2)*(PowerSeries.X+PowerSeries.C 3)) *
        (rationalPolynomialSeries (nonmatchingDiscProduct p a (p-1)))^3 := by ring
    _ = _ := by rw [← he]; ring

theorem primeDiscShape_high_cleared (hp4 : 3 < p) (a : ℕ)
    (ha : p-3 ≤ a) (hap : a < p) :
    primeDiscPolynomialSeries (p := p) a (p-1)^3 *
      ((PowerSeries.X+1)*(PowerSeries.X+PowerSeries.C 2)) =
      primeDiscPolynomialSeries a (4*(p-1)) *
        PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (primeDiscUnit a hap) *
          PowerSeries.X^2 := by
  rw [primeDiscPolynomialSeries_factorization,
    primeDiscPolynomialSeries_factorization,
    numerator_matching_nonzero p a (by omega) hap,
    denominator_matching_high p a hp4 ha hap]
  simp only [map_mul, map_add, map_one, map_pow, rationalPolynomialSeries_C,
    rationalPolynomialSeries_X, Rat.cast_natCast, Rat.cast_ofNat]
  have he := primeDiscUnit_cleared_field (p := p) a hap
  calc
    _ = (PowerSeries.C (p:ℚ_[p]))^3 * PowerSeries.X^3 *
        ((PowerSeries.X+1)*(PowerSeries.X+PowerSeries.C 2)) *
        (rationalPolynomialSeries (nonmatchingDiscProduct p a (p-1)))^3 := by ring
    _ = _ := by rw [← he]; ring

theorem primeDiscShape_zero_cleared (hp4 : 3 < p) :
    PowerSeries.C ((p:ℚ_[p])^3) * primeDiscPolynomialSeries 0 (p-1)^3 *
      ((PowerSeries.X+1)*(PowerSeries.X+PowerSeries.C 2)*
        (PowerSeries.X+PowerSeries.C 3)) =
      primeDiscPolynomialSeries 0 (4*(p-1)) *
        PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (primeDiscUnit 0 hp.out.pos) := by
  rw [primeDiscPolynomialSeries_factorization,
    primeDiscPolynomialSeries_factorization,
    numerator_matching_zero p hp.out.pos, denominator_matching_zero p hp4]
  simp only [map_mul, map_add, map_one, map_pow, one_mul, rationalPolynomialSeries_C,
    rationalPolynomialSeries_X, Rat.cast_natCast, Rat.cast_ofNat]
  rw [← primeDiscUnit_cleared_field 0 hp.out.pos]
  ring

end
end Li2

end
