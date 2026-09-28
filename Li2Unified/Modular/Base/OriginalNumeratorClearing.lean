module
public import Li2Unified.Modular.Base.OriginalFunctionalAssembly
public import Li2Unified.Modular.Base.OriginalPoleClearing

set_option backward.privateInPublic true

@[expose] public section

/-! The independently constructed pulled regular part and original residues
have exactly the numerator obtained from the original rational function. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeDiscPolynomialSeries_product (a m : ℕ) :
    primeDiscPolynomialSeries (p := p) a m =
      ∏ j ∈ Finset.Icc 1 m, pulledAffineFactor j a := by
  simp only [primeDiscPolynomialSeries, D, prod_comp, map_prod, pulledAffineFactor_eq]

lemma primeDiscPolynomialSeries_ne_zero (a m : ℕ) :
    primeDiscPolynomialSeries (p := p) a m ≠ 0 := by
  rw [primeDiscPolynomialSeries_product]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _ hj
  have hc := congrArg (PowerSeries.coeff 1) hj
  have hpne : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hcoeff : PowerSeries.coeff 1 (pulledAffineFactor (p := p) j a) = (p:ℚ_[p]) := by
    unfold pulledAffineFactor
    rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C, PowerSeries.coeff_X]
    norm_num
  exact hpne (by simpa only [map_zero] using hcoeff.symm.trans hc)

lemma original_fieldPoleNumerator (m : ℕ) (hm : m ≤ 4*p-4) (F : ℚ[X]) (a : Fin p) :
    fieldPoleNumerator (primePoleCenters p) (originalPulledRegular m F a)
      (originalPulledResidue m hm F a) =
    (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
      rationalPolynomialSeries ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ))) +
      ∑ j : ↥(Finset.Icc 1 m), PowerSeries.C (originalResidue m F j.val : ℚ_[p]) *
        fieldPoleNumerator (primePoleCenters p) (pulledPoleRegular j.val a.val)
          (pulledPoleResidue j.val a.val ((Finset.mem_Icc.mp j.property).2.trans hm) a.isLt) := by
  classical
  rw [originalPulledRegular_subtype]
  have hr : originalPulledResidue m hm F a = 0 + originalPulledResidue m hm F a := by simp
  rw [hr, fieldPoleNumerator_add]
  have hz (g : PowerSeries ℚ_[p]) :
      fieldPoleNumerator (primePoleCenters p) g 0 =
        (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p])*g := by
    simp only [fieldPoleNumerator, Pi.zero_apply, map_zero, zero_mul,
      Finset.sum_const_zero, Polynomial.coe_zero, add_zero]
  rw [hz]
  congr 1
  unfold originalPulledResidue
  rw [fieldPoleNumerator_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact fieldPoleNumerator_smul _ _ _ _

theorem originalPulled_cleared (m : ℕ) (hm : m ≤ 4*p-4) (F : ℚ[X]) (a : Fin p) :
    primeDiscPolynomialSeries a.val m *
      fieldPoleNumerator (primePoleCenters p) (originalPulledRegular m F a)
        (originalPulledResidue m hm F a) =
    (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
      rationalPolynomialSeries (F.comp (C (p:ℚ)*X-C (a.val:ℚ))) := by
  have hpf := congrArg
    (fun P : ℚ[X] => rationalPolynomialSeries (p := p)
      (P.comp (C (p:ℚ)*X-C (a.val:ℚ)))) (original_partial_fractions m F)
  simp only [add_comp, mul_comp, sum_comp, prod_comp, C_comp,
    map_add, map_mul, map_sum, map_prod, rationalPolynomialSeries_C,
    Rat.cast_natCast] at hpf
  have hfactor (j : ℕ) :
      rationalPolynomialSeries (p := p) (X.comp (C (p:ℚ)*X-C (a.val:ℚ))) +
        PowerSeries.C (j:ℚ_[p]) = pulledAffineFactor j a.val := by
    simp only [X_comp, map_sub, map_mul, rationalPolynomialSeries_C,
      rationalPolynomialSeries_X, Rat.cast_natCast, pulledAffineFactor]
    ring
  simp only [hfactor] at hpf
  have hterm (j : ↥(Finset.Icc 1 m)) :
      primeDiscPolynomialSeries (p := p) a.val m *
        fieldPoleNumerator (primePoleCenters p) (pulledPoleRegular j.val a.val)
          (pulledPoleResidue j.val a.val ((Finset.mem_Icc.mp j.property).2.trans hm) a.isLt) =
      (fieldPoleDenominator (primePoleCenters p) : PowerSeries ℚ_[p]) *
        ∏ l ∈ (Finset.Icc 1 m).erase j.val, pulledAffineFactor l a.val := by
    rw [primeDiscPolynomialSeries_product,
      ← Finset.mul_prod_erase _ _ j.property]
    calc
      _ = (∏ l ∈ (Finset.Icc 1 m).erase j.val, pulledAffineFactor l a.val) *
        (pulledAffineFactor j.val a.val * fieldPoleNumerator (primePoleCenters p)
          (pulledPoleRegular j.val a.val)
          (pulledPoleResidue j.val a.val ((Finset.mem_Icc.mp j.property).2.trans hm) a.isLt)) := by ring
      _ = _ := by rw [pulledPole_cleared]; ring
  rw [original_fieldPoleNumerator, mul_add, Finset.mul_sum, hpf, mul_add]
  congr 1
  · change _ = _ * (_ * primeDiscPolynomialSeries a.val m)
    ring
  · rw [Finset.mul_sum]
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = PowerSeries.C (originalResidue m F j.val : ℚ_[p]) *
        (primeDiscPolynomialSeries a.val m * fieldPoleNumerator (primePoleCenters p)
          (pulledPoleRegular j.val a.val)
          (pulledPoleResidue j.val a.val ((Finset.mem_Icc.mp j.property).2.trans hm) a.isLt)) := by ring
      _ = _ := by rw [hterm]; ring

end
end Li2

end
