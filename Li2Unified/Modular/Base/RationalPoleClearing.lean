module
public import Li2Unified.Modular.Base.RationalPoleCompatibility

set_option backward.privateInPublic true

@[expose] public section

/-! Compare independently constructed integral pole presentations with the
rational base presentations by their cleared numerators. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma rationalPoleDenominator_map :
    rationalPoleDenominator.map (Rat.castHom ℚ_[p]) =
      fieldPoleDenominator (primePoleCenters p) := by
  simp [rationalPoleDenominator, fieldPoleDenominator, primePoleCenters, Fin.prod_univ_succ]
  ring

lemma rationalPoleCofactor_map (j : Fin 4) :
    (rationalPoleCofactor j).map (Rat.castHom ℚ_[p]) =
      fieldPoleCofactor (primePoleCenters p) j := by
  have hs : ∀ i : Fin 4, (univ : Finset (Fin 4)).erase i =
      ![{1,2,3},{0,2,3},{0,1,3},{0,1,2}] i := by decide
  simp only [fieldPoleCofactor, hs]
  fin_cases j <;> simp [rationalPoleCofactor, primePoleCenters] <;> ring

theorem rationalPoleNumerator_map (f : ℚ[X]) (r : Fin 4 → ℚ) :
    ((rationalPoleNumerator f r).map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p]) =
      fieldPoleNumerator (primePoleCenters p)
        (f.map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p]) (fun j => (r j:ℚ_[p])) := by
  simp only [rationalPoleNumerator, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_sum, Polynomial.map_C, rationalPoleDenominator_map,
    rationalPoleCofactor_map, Rat.coe_castHom, Polynomial.coe_add,
    Polynomial.coe_mul, fieldPoleNumerator]

theorem primePoleUV_rational_of_cleared (hp4 : 3 < p)
    (g : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g)
    (s : Fin 4 → ℤ_[p]) (f : ℚ[X]) (r : Fin 4 → ℚ)
    (he : PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
        (integralPoleNumerator (primePoleCenters p) g s) =
      ((rationalPoleNumerator f r).map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p]))
    (Y : ℚ_[p]) :
    (primePoleU hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleU (primeParameter p) f r).eval₂ (Rat.castHom ℚ_[p]) Y ∧
      (primePoleV hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleV (primeParameter p) f r).eval₂ (Rat.castHom ℚ_[p]) Y := by
  rw [← fieldPoleNumerator_integral, rationalPoleNumerator_map] at he
  obtain ⟨hf, hr⟩ := fieldPoleNumerator_injective (primePoleCenters p)
    primePoleCenters_injective _ _ (field_map_isRestricted g hg)
    (field_polynomial_isRestricted _) _ _ he
  constructor
  · rw [← eval_map, ← fieldPrimePoleU_integral hp4 g hg s, hf, hr]
    exact fieldPrimePoleU_rational hp4 f r Y
  · rw [← eval_map, ← fieldPrimePoleV_integral hp4 g hg s, hf, hr]
    exact fieldPrimePoleV_rational hp4 f r Y

theorem primeZeroShape_monomial_rational (hp4 : 3 < p) (k : Fin 5) (Y : ℚ_[p]) :
    let g := integralPoleMulRegular (primePoleCenters p)
      ((X^(k.val) : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) 0 (primeZeroShapeResidue hp4)
    let s := integralPoleMulResidue (primePoleCenters p)
      ((X^(k.val) : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) (primeZeroShapeResidue hp4)
    (primePoleU hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleU (primeParameter p) (zeroShapeRegular k) (zeroShapeResidue k)).eval₂
          (Rat.castHom ℚ_[p]) Y ∧
      (primePoleV hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleV (primeParameter p) (zeroShapeRegular k) (zeroShapeResidue k)).eval₂
          (Rat.castHom ℚ_[p]) Y := by
  dsimp only
  apply primePoleUV_rational_of_cleared hp4
  · exact integralPoleMulRegular_isRestricted _ _ _ (polynomial_isRestricted _)
      (by simpa using polynomial_isRestricted (p := p) (0:(ℤ_[p])[X])) _
  · rw [integralPoleNumerator_mul _ _ _ (polynomial_isRestricted _),
      primeZeroShape_cleared, zeroShape_cleared]
    simp [pow_succ]

theorem primeHighShape_monomial_rational (hp4 : 3 < p) (k : Fin 3) (Y : ℚ_[p]) :
    let g := integralPoleMulRegular (primePoleCenters p)
      ((X^(k.val) : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) 1 primeHighShapeResidue
    let s := integralPoleMulResidue (primePoleCenters p)
      ((X^(k.val) : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) primeHighShapeResidue
    (primePoleU hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleU (primeParameter p) (highShapeRegular k) (highShapeResidue k)).eval₂
          (Rat.castHom ℚ_[p]) Y ∧
      (primePoleV hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleV (primeParameter p) (highShapeRegular k) (highShapeResidue k)).eval₂
          (Rat.castHom ℚ_[p]) Y := by
  dsimp only
  apply primePoleUV_rational_of_cleared hp4
  · exact integralPoleMulRegular_isRestricted _ _ _ (polynomial_isRestricted _)
      (by simpa using polynomial_isRestricted (p := p) (1:(ℤ_[p])[X])) _
  · rw [integralPoleNumerator_mul _ _ _ (polynomial_isRestricted _),
      primeHighShape_cleared, highShape_cleared]
    simp [pow_add, mul_assoc]
    rw [← Polynomial.coe_C]
    congr 1

theorem primeLowShape_monomial_rational (hp4 : 3 < p) (k : Fin 3) (Y : ℚ_[p]) :
    let g := integralPoleMulRegular (primePoleCenters p)
      ((X^(k.val) : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) 0 (primeLowShapeResidue hp4)
    let s := integralPoleMulResidue (primePoleCenters p)
      ((X^(k.val) : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) (primeLowShapeResidue hp4)
    (primePoleU hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleU (primeParameter p)
          (zeroShapeRegular ⟨k.val+2,by omega⟩) (zeroShapeResidue ⟨k.val+2,by omega⟩)).eval₂
          (Rat.castHom ℚ_[p]) Y ∧
      (primePoleV hp4 g s).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
        (rationalPoleV (primeParameter p)
          (zeroShapeRegular ⟨k.val+2,by omega⟩) (zeroShapeResidue ⟨k.val+2,by omega⟩)).eval₂
          (Rat.castHom ℚ_[p]) Y := by
  dsimp only
  apply primePoleUV_rational_of_cleared hp4
  · exact integralPoleMulRegular_isRestricted _ _ _ (polynomial_isRestricted _)
      (by simpa using polynomial_isRestricted (p := p) (0:(ℤ_[p])[X])) _
  · rw [integralPoleNumerator_mul _ _ _ (polynomial_isRestricted _),
      primeLowShape_cleared, zeroShape_cleared]
    simp [pow_add, mul_assoc]
    ring

end
end Li2

end
