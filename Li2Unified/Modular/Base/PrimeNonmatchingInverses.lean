module
public import Li2Unified.Modular.Base.PrimeMatchingProducts
public import Li2Unified.Modular.Base.PadicReciprocalSeries
public import Li2Unified.Modular.Base.RestrictedUnitProducts

set_option backward.privateInPublic true

@[expose] public section

/-! Independently constructed inverse of the complete nonmatching denominator
product on a residue disc, with its integral coefficient error bound. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma nonmatching_rational_unit (a j : ℕ) (ha : a < p) (hj : j%p ≠ a) :
    (j:ℚ)-(a:ℚ) ≠ 0 ∧ padicValRat p ((j:ℚ)-(a:ℚ)) = 0 := by
  have hi : ¬(p:ℤ) ∣ (j:ℤ)-(a:ℤ) := by
    intro h
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd ((j:ℤ)-(a:ℤ)) p).mpr h
    simp only [Int.cast_sub, Int.cast_natCast] at hz
    have he := (ZMod.natCast_eq_natCast_iff' j a p).mp (sub_eq_zero.mp hz)
    exact hj (he.trans (Nat.mod_eq_of_lt ha))
  have hn : (j:ℤ)-(a:ℤ) ≠ 0 := fun h => hi (h ▸ dvd_zero _)
  refine ⟨by exact_mod_cast hn, ?_⟩
  have h : padicValRat p (((j:ℤ)-(a:ℤ):ℤ):ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hi]
    rfl
  simpa only [Int.cast_sub, Int.cast_natCast] using h

def nonmatchingDiscIndices (p a m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 m).filter (fun j => j%p ≠ a)

def integralNonmatchingDiscPolynomial (a m : ℕ) : (ℤ_[p])[X] :=
  ∏ j ∈ nonmatchingDiscIndices p a m,
    (C (p:ℤ_[p])*X+C ((j:ℤ_[p])-(a:ℤ_[p])))

def nonmatchingDiscInverse (a m : ℕ) (ha : a < p) : PowerSeries ℤ_[p] :=
  ∏ j : nonmatchingDiscIndices p a m,
    padicReciprocalSeries ((j.val:ℚ)-(a:ℚ))
      (nonmatching_rational_unit (p := p) a j.val ha (Finset.mem_filter.mp j.property).2).1
      (nonmatching_rational_unit (p := p) a j.val ha (Finset.mem_filter.mp j.property).2).2 1

def nonmatchingInverseConstant (a m : ℕ) (ha : a < p) : ℤ_[p] :=
  ∏ j : nonmatchingDiscIndices p a m,
    (↑(integralRationalUnit ((j.val:ℚ)-(a:ℚ))
      (nonmatching_rational_unit (p := p) a j.val ha (Finset.mem_filter.mp j.property).2).1
      (nonmatching_rational_unit (p := p) a j.val ha (Finset.mem_filter.mp j.property).2).2)⁻¹:ℤ_[p])

lemma polynomial_coe_finset_prod {ι : Type*} (s : Finset ι) (f : ι → (ℤ_[p])[X]) :
    ((∏ i ∈ s, f i : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) =
      ∏ i ∈ s, (f i : PowerSeries ℤ_[p]) :=
  map_prod Polynomial.coeToPowerSeries.ringHom f s

lemma restricted_finset_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℤ_[p])
    (hf : ∀ i ∈ s, PowerSeries.IsRestricted 1 (f i)) :
    PowerSeries.IsRestricted 1 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PowerSeries.isRestricted_one (R := ℤ_[p]) 1
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact PowerSeries.isRestricted.mul 1 (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem nonmatchingDiscInverse_isRestricted (a m : ℕ) (ha : a < p) :
    PowerSeries.IsRestricted 1 (nonmatchingDiscInverse a m ha) := by
  apply restricted_finset_prod
  intro j _
  exact padicReciprocalSeries_isRestricted _ _ _ 1

theorem nonmatchingDiscInverse_constant_error (a m : ℕ) (ha : a < p) (n : ℕ) :
    ‖PowerSeries.coeff n (nonmatchingDiscInverse a m ha-
      PowerSeries.C (nonmatchingInverseConstant a m ha))‖ ≤ ‖(p:ℤ_[p])‖ := by
  apply powerSeries_prod_constant_error_bound _ _ _ _ (norm_nonneg _)
  intro j _ k
  simpa only [padicReciprocalSeries, pow_one] using
    affineInverseSeries_constant_error_bound
      (integralRationalUnit ((j.val:ℚ)-(a:ℚ))
        (nonmatching_rational_unit (p := p) a j.val ha (Finset.mem_filter.mp j.property).2).1
        (nonmatching_rational_unit (p := p) a j.val ha (Finset.mem_filter.mp j.property).2).2)
      (p:ℤ_[p]) 1 k

theorem nonmatchingDiscInverse_identity (a m : ℕ) (ha : a < p) :
    nonmatchingDiscInverse a m ha*
      (integralNonmatchingDiscPolynomial (p := p) a m : PowerSeries ℤ_[p]) = 1 := by
  unfold nonmatchingDiscInverse integralNonmatchingDiscPolynomial
  rw [polynomial_coe_finset_prod]
  simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]
  rw [← Finset.prod_coe_sort (nonmatchingDiscIndices p a m)
    (fun j : ℕ => PowerSeries.C (p:ℤ_[p])*PowerSeries.X+
      PowerSeries.C ((j:ℤ_[p])-(a:ℤ_[p])))]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j _
  have h := affineInverseSeries_identity
    (integralRationalUnit ((j.val:ℚ)-(a:ℚ))
      (nonmatching_rational_unit (p := p) a j.val ha (Finset.mem_filter.mp j.property).2).1
      (nonmatching_rational_unit (p := p) a j.val ha (Finset.mem_filter.mp j.property).2).2) (p:ℤ_[p]) 1
  have hc : ((integralRationalUnit ((j.val:ℚ)-(a:ℚ))
      (nonmatching_rational_unit (p := p) a j.val ha (Finset.mem_filter.mp j.property).2).1
      (nonmatching_rational_unit (p := p) a j.val ha (Finset.mem_filter.mp j.property).2).2):ℤ_[p]) =
        (j.val:ℤ_[p])-(a:ℤ_[p]) := by
    apply PadicInt.ext
    simp
  rw [hc, pow_one] at h
  simpa only [padicReciprocalSeries, add_comm] using h

end
end Li2

end
