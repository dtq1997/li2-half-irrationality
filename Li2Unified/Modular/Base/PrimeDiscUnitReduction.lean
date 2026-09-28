module
public import Li2Unified.Modular.Base.PrimeDiscUnits
public import Li2Unified.Modular.Base.PrimeFieldLeadingConstants
public import Mathlib.NumberTheory.Padics.RingHoms

set_option backward.privateInPublic true

@[expose] public section

/-! Reduction of the independently constructed integral disc unit is the
literal finite-field product used in the leading-constant calculation. -/
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem nonmatchingDiscConstant_reduction (a m : ℕ) :
    PadicInt.toZMod (nonmatchingDiscConstant (p := p) a m) =
      primeFieldUnitProduct a m := by
  rw [primeFieldUnitProduct_filter]
  simp [nonmatchingDiscConstant, nonmatchingDiscIndices]

theorem nonmatchingInverseConstant_reduction (a m : ℕ) (ha : a < p) :
    PadicInt.toZMod (nonmatchingInverseConstant (p := p) a m ha) =
      (primeFieldUnitProduct a m)⁻¹ := by
  unfold nonmatchingInverseConstant
  rw [map_prod, primeFieldUnitProduct_filter, ← Finset.prod_inv_distrib]
  change _ = ∏ j ∈ nonmatchingDiscIndices p a m, ((j:ZMod p)-(a:ZMod p))⁻¹
  rw [← Finset.prod_coe_sort (nonmatchingDiscIndices p a m)
    (fun j : ℕ => ((j:ZMod p)-(a:ZMod p))⁻¹)]
  apply Finset.prod_congr rfl
  intro j _
  rw [map_units_inv]
  have hc : ((integralRationalUnit ((j.val:ℚ)-(a:ℚ))
      (nonmatching_rational_unit (p := p) a j.val ha (Finset.mem_filter.mp j.property).2).1
      (nonmatching_rational_unit (p := p) a j.val ha (Finset.mem_filter.mp j.property).2).2):ℤ_[p]) =
        (j.val:ℤ_[p])-(a:ℤ_[p]) := by
    apply PadicInt.ext
    simp
  rw [hc]
  simp

theorem primeDiscUnitConstant_reduction (a : ℕ) (ha : a < p) :
    PadicInt.toZMod (primeDiscUnitConstant (p := p) a ha) =
      primeFieldLeadingUnit a := by
  simp only [primeDiscUnitConstant, map_mul, map_pow,
    nonmatchingDiscConstant_reduction, nonmatchingInverseConstant_reduction,
    primeFieldLeadingUnit, div_eq_mul_inv]

end
end Li2

end
