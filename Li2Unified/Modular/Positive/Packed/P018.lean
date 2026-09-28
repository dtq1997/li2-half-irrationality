module
public import Li2Unified.Modular.Positive.Packed.P015
public import Li2Unified.Modular.Base.OriginalNumeratorClearing
public import Li2Unified.Modular.Positive.Packed.P017

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem generalPulledPole_cleared (m j : ℕ) (hm : m < p * p)
    (hj : j ≤ m) (a : Fin p) :
    pulledAffineFactor j a.val *
      fieldPoleNumerator (generalPoleCenters (p := p)) (pulledPoleRegular j a.val)
        (generalPulledPoleResidue m j hm hj a) =
      (fieldPoleDenominator (generalPoleCenters (p := p)) : PowerSeries ℚ_[p]) := by
  classical
  by_cases hmod : j % p = a.val
  · have hshift := (matching_shift_dvd_iff p j a).2 hmod
    rw [pulledPoleRegular, generalPulledPoleResidue_matching m j hm hj a hmod,
      dif_pos hshift, fieldPoleNumerator_single]
    let k := generalMatchingPoleIndex p m j a hp.out.pos hm hj hmod
    have hA : pulledAffineFactor (p := p) j a.val =
        PowerSeries.C (p : ℚ_[p]) *
          ((X - C (generalPoleCenters k : ℚ_[p]) : (ℚ_[p])[X]) : PowerSeries ℚ_[p]) := by
      rw [pulledAffineFactor]
      have hden := generalMatchingPole_denominator p m j a hp.out.pos hm hj hmod
      have hdenp : (j : ℚ_[p]) - (a.val : ℚ_[p]) =
          (p : ℚ_[p]) * (k.val : ℚ_[p]) := by
        exact_mod_cast hden
      rw [hdenp]
      simp only [generalPoleCenters, PadicInt.coe_neg, PadicInt.coe_natCast,
        Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C, map_neg, map_mul,
        Polynomial.coe_neg, k]
      ring
    have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hc : PowerSeries.C (p : ℚ_[p]) * PowerSeries.C (p : ℚ_[p])⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hpne, map_one]
    rw [hA, fieldPoleDenominator_factor _ k, Polynomial.coe_mul]
    change (PowerSeries.C (p : ℚ_[p]) * _) *
      (PowerSeries.C (p : ℚ_[p])⁻¹ * _) = _
    calc
      _ = (PowerSeries.C (p : ℚ_[p]) * PowerSeries.C (p : ℚ_[p])⁻¹) *
        (((X - C (generalPoleCenters k : ℚ_[p]) : (ℚ_[p])[X]) : PowerSeries ℚ_[p]) *
          (fieldPoleCofactor (generalPoleCenters (p := p)) k : PowerSeries ℚ_[p])) := by ring
      _ = _ := by rw [hc, one_mul]
  · have hshift : ¬p ∣ j + (p - 1 - a.val) + 1 := by
      intro hs
      exact hmod ((matching_shift_dvd_iff p j a).1 hs)
    have hi := pulledPoleRegular_inverse (p := p) j a.val a.isLt hshift
    rw [generalPulledPoleResidue_nonmatching m j hm hj a hmod]
    simp only [fieldPoleNumerator, Pi.zero_apply, map_zero, zero_mul,
      Finset.sum_const_zero, Polynomial.coe_zero, add_zero]
    calc
      _ = (fieldPoleDenominator (generalPoleCenters (p := p)) : PowerSeries ℚ_[p]) *
        (pulledAffineFactor j a.val * pulledPoleRegular j a.val) := by ring
      _ = _ := by rw [hi, mul_one]

#print axioms generalPulledPole_cleared

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalOriginal_fieldPoleNumerator (m : ℕ) (hm : m < p * p)
    (F : ℚ[X]) (a : Fin p) :
    fieldPoleNumerator (generalPoleCenters (p := p)) (originalPulledRegular m F a)
      (generalOriginalPulledResidue m hm F a) =
    (fieldPoleDenominator (generalPoleCenters (p := p)) : PowerSeries ℚ_[p]) *
      rationalPolynomialSeries ((F /ₘ D m).comp (C (p : ℚ) * X - C (a.val : ℚ))) +
      ∑ j : ↥(Finset.Icc 1 m), PowerSeries.C (originalResidue m F j.val : ℚ_[p]) *
        fieldPoleNumerator (generalPoleCenters (p := p))
          (pulledPoleRegular j.val a.val)
          (generalPulledPoleResidue m j.val hm (Finset.mem_Icc.mp j.property).2 a) := by
  classical
  rw [originalPulledRegular_subtype]
  have hr : generalOriginalPulledResidue m hm F a =
      0 + generalOriginalPulledResidue m hm F a := by simp
  rw [hr, fieldPoleNumerator_add]
  have hz (g : PowerSeries ℚ_[p]) :
      fieldPoleNumerator (generalPoleCenters (p := p)) g 0 =
        (fieldPoleDenominator (generalPoleCenters (p := p)) : PowerSeries ℚ_[p]) * g := by
    simp only [fieldPoleNumerator, Pi.zero_apply, map_zero, zero_mul,
      Finset.sum_const_zero, Polynomial.coe_zero, add_zero]
  rw [hz]
  congr 1
  unfold generalOriginalPulledResidue
  rw [fieldPoleNumerator_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact fieldPoleNumerator_smul _ _ _ _

theorem generalOriginalPulled_cleared (m : ℕ) (hm : m < p * p)
    (F : ℚ[X]) (a : Fin p) :
    primeDiscPolynomialSeries a.val m *
      fieldPoleNumerator (generalPoleCenters (p := p)) (originalPulledRegular m F a)
        (generalOriginalPulledResidue m hm F a) =
    (fieldPoleDenominator (generalPoleCenters (p := p)) : PowerSeries ℚ_[p]) *
      rationalPolynomialSeries (F.comp (C (p : ℚ) * X - C (a.val : ℚ))) := by
  have hpf := congrArg
    (fun P : ℚ[X] => rationalPolynomialSeries (p := p)
      (P.comp (C (p : ℚ) * X - C (a.val : ℚ)))) (original_partial_fractions m F)
  simp only [add_comp, mul_comp, sum_comp, prod_comp, C_comp,
    map_add, map_mul, map_sum, map_prod, rationalPolynomialSeries_C,
    Rat.cast_natCast] at hpf
  have hfactor (j : ℕ) :
      rationalPolynomialSeries (p := p) (X.comp (C (p : ℚ) * X - C (a.val : ℚ))) +
        PowerSeries.C (j : ℚ_[p]) = pulledAffineFactor j a.val := by
    simp only [X_comp, map_sub, map_mul, rationalPolynomialSeries_C,
      rationalPolynomialSeries_X, Rat.cast_natCast, pulledAffineFactor]
    ring
  simp only [hfactor] at hpf
  have hterm (j : ↥(Finset.Icc 1 m)) :
      primeDiscPolynomialSeries (p := p) a.val m *
        fieldPoleNumerator (generalPoleCenters (p := p))
          (pulledPoleRegular j.val a.val)
          (generalPulledPoleResidue m j.val hm (Finset.mem_Icc.mp j.property).2 a) =
      (fieldPoleDenominator (generalPoleCenters (p := p)) : PowerSeries ℚ_[p]) *
        ∏ l ∈ (Finset.Icc 1 m).erase j.val, pulledAffineFactor l a.val := by
    rw [primeDiscPolynomialSeries_product,
      ← Finset.mul_prod_erase _ _ j.property]
    calc
      _ = (∏ l ∈ (Finset.Icc 1 m).erase j.val, pulledAffineFactor l a.val) *
        (pulledAffineFactor j.val a.val * fieldPoleNumerator (generalPoleCenters (p := p))
          (pulledPoleRegular j.val a.val)
          (generalPulledPoleResidue m j.val hm (Finset.mem_Icc.mp j.property).2 a)) := by ring
      _ = _ := by rw [generalPulledPole_cleared]; ring
  rw [generalOriginal_fieldPoleNumerator, mul_add, Finset.mul_sum, hpf, mul_add]
  congr 1
  · change _ = _ * (_ * primeDiscPolynomialSeries a.val m)
    ring
  · rw [Finset.mul_sum]
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = PowerSeries.C (originalResidue m F j.val : ℚ_[p]) *
        (primeDiscPolynomialSeries a.val m * fieldPoleNumerator (generalPoleCenters (p := p))
          (pulledPoleRegular j.val a.val)
          (generalPulledPoleResidue m j.val hm (Finset.mem_Icc.mp j.property).2 a)) := by ring
      _ = _ := by rw [hterm]; ring

#print axioms generalOriginal_fieldPoleNumerator
#print axioms generalOriginalPulled_cleared

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalOriginalPulled_eq_integral_of_cleared
    (m : ℕ) (hm : m < p * p) (F : ℚ[X]) (a : Fin p) (c : ℚ_[p])
    (g : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g)
    (r : Fin p → ℤ_[p])
    (he : primeDiscPolynomialSeries a.val m *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
        (integralPoleNumerator (generalPoleCenters (p := p)) g r) =
      PowerSeries.C c *
        (fieldPoleDenominator (generalPoleCenters (p := p)) : PowerSeries ℚ_[p]) *
          rationalPolynomialSeries (F.comp (C (p : ℚ) * X - C (a.val : ℚ)))) :
    c • originalPulledRegular m F a =
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) g ∧
    (fun k => c * generalOriginalPulledResidue m hm F a k) =
      (fun k => (r k : ℚ_[p])) := by
  apply fieldPoleNumerator_injective (generalPoleCenters (p := p))
    generalPoleCenters_injective _ _
    (PowerSeries.IsRestricted.smul 1 (originalPulledRegular_isRestricted m F a) c)
    (field_map_isRestricted g hg)
  rw [fieldPoleNumerator_smul, fieldPoleNumerator_integral]
  apply mul_left_cancel₀ (primeDiscPolynomialSeries_ne_zero (p := p) a.val m)
  rw [he]
  calc
    _ = PowerSeries.C c * (primeDiscPolynomialSeries a.val m *
      fieldPoleNumerator (generalPoleCenters (p := p)) (originalPulledRegular m F a)
        (generalOriginalPulledResidue m hm F a)) := by ring
    _ = _ := by rw [generalOriginalPulled_cleared]; ring

theorem parameterPulledValue_integral_of_cleared (lam : ℚ)
    (hunit : lam ^ p ≠ 0 ∧ padicValRat p (lam ^ p) = 0)
    (hreg : VG p (lam ^ p / (1 - lam ^ p)) 0) (Y : ℚ_[p])
    (m : ℕ) (hm : m < p * p) (F : ℚ[X]) (a : Fin p) (c : ℚ_[p])
    (g : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g)
    (r : Fin p → ℤ_[p])
    (he : primeDiscPolynomialSeries a.val m *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
        (integralPoleNumerator (generalPoleCenters (p := p)) g r) =
      PowerSeries.C c *
        (fieldPoleDenominator (generalPoleCenters (p := p)) : PowerSeries ℚ_[p]) *
          rationalPolynomialSeries (F.comp (C (p : ℚ) * X - C (a.val : ℚ)))) :
    c * parameterPulledValue lam hreg Y m F a =
      (generalPoleU (lam ^ p) hunit hreg g r).eval₂
        (algebraMap ℤ_[p] ℚ_[p]) Y -
      (a.val : ℚ_[p]) / (p : ℚ_[p]) *
        (generalPoleV (lam ^ p) hunit hreg g r).eval₂
          (algebraMap ℤ_[p] ℚ_[p]) Y := by
  obtain ⟨hgEq, hrEq⟩ :=
    generalOriginalPulled_eq_integral_of_cleared m hm F a c g hg r he
  have hu : C c * generalFieldPoleU (lam ^ p) hunit hreg
      (originalPulledRegular m F a) (generalOriginalPulledResidue m hm F a) =
      (generalPoleU (lam ^ p) hunit hreg g r).map (algebraMap ℤ_[p] ℚ_[p]) := by
    change C c * fieldPoleFunctional _ _ _ _ = _
    rw [← fieldPoleFunctional_smul _ _ _
      (originalPulledRegular_isRestricted m F a) _ c, hgEq, hrEq]
    exact generalFieldPoleU_integral (lam ^ p) hunit hreg g hg r
  have hv : C c * generalFieldPoleV (lam ^ p) hunit hreg
      (originalPulledRegular m F a) (generalOriginalPulledResidue m hm F a) =
      (generalPoleV (lam ^ p) hunit hreg g r).map (algebraMap ℤ_[p] ℚ_[p]) := by
    change C c * fieldPoleFunctional _ _ _ _ = _
    rw [← fieldPoleFunctional_smul _ _ _
      (originalPulledRegular_isRestricted m F a) _ c, hgEq, hrEq]
    exact generalFieldPoleV_integral (lam ^ p) hunit hreg g hg r
  have hu' := congrArg (fun P : (ℚ_[p])[X] => P.eval Y) hu
  have hv' := congrArg (fun P : (ℚ_[p])[X] => P.eval Y) hv
  simp only [eval_mul, eval_C, eval_map] at hu' hv'
  rw [parameterPulledValue_generalField lam hunit hreg Y m hm F a, mul_sub, hu']
  rw [← hv']
  ring

#print axioms generalOriginalPulled_eq_integral_of_cleared
#print axioms parameterPulledValue_integral_of_cleared

end
end Li2Unified.Proofs.Hermite

end


end
