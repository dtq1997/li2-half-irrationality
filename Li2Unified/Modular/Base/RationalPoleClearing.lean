module
public import Li2Unified.Modular.Base.RationalBaseEvaluation
public import Li2Unified.Modular.Base.FieldPoleCompatibility
public import Li2Unified.Modular.Base.FieldParameterFunctional
public import Li2Unified.Modular.Base.PrimePoleExtension

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

end
end Li2

end
