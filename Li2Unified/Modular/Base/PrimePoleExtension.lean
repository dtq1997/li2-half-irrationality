module
public import Li2Unified.Modular.Base.RestrictedPoleBounds
public import Li2Unified.Modular.Base.ParameterPoleValues

set_option backward.privateInPublic true

@[expose] public section

/-! The bounded U/V extensions with the actual z=(-1/2)^p parameter,
on the four simple poles u=0,-1,-2,-3. Y is the polynomial variable. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def primePoleCenters (p : ℕ) [Fact p.Prime] : Fin 4 → ℤ_[p] := fun i => -(i.val:ℤ_[p])

lemma primePoleCenters_injective : Function.Injective (primePoleCenters p) := by
  intro i j h
  apply Fin.ext
  have he : (i.val:ℤ_[p]) = (j.val:ℤ_[p]) := neg_injective h
  exact_mod_cast he

end
end Li2

end
