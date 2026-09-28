module
public import Li2Unified.Modular.Positive.Packed.P018
public import Li2Unified.Modular.Base.OriginalIntegerTests
public import Li2Unified.Modular.Positive.Packed.P001
public import Li2Unified.Modular.Base.ParameterPoleValues

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem general_original_test_integral_cleared
    (m : ℕ) (F : ℚ[X]) (a : Fin p) (c : ℚ_[p])
    (g : PowerSeries ℤ_[p]) (r : Fin p → ℤ_[p])
    (he : primeDiscPolynomialSeries a.val m *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
        (integralPoleNumerator (generalPoleCenters (p := p)) g r) =
      PowerSeries.C c *
        (fieldPoleDenominator (generalPoleCenters (p := p)) : PowerSeries ℚ_[p]) *
          rationalPolynomialSeries (F.comp (C (p : ℚ) * X - C (a.val : ℚ))))
    (T : ℤ[X]) :
    primeDiscPolynomialSeries a.val m *
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
        (integralPoleNumerator (generalPoleCenters (p := p))
          (integralPoleMulRegular (generalPoleCenters (p := p))
            (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) g r)
          (integralPoleMulResidue (generalPoleCenters (p := p))
            (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) r)) =
    PowerSeries.C c *
      (fieldPoleDenominator (generalPoleCenters (p := p)) : PowerSeries ℚ_[p]) *
        rationalPolynomialSeries ((F * T.map (Int.castRingHom ℚ)).comp
          (C (p : ℚ) * X - C (a.val : ℚ))) := by
  rw [integralPoleNumerator_mul _ _ _ (polynomial_isRestricted _), map_mul,
    integralDiscTestSeries_map, mul_comp, map_mul]
  calc
    _ = rationalPolynomialSeries ((T.map (Int.castRingHom ℚ)).comp
        (C (p : ℚ) * X - C (a.val : ℚ))) *
      (primeDiscPolynomialSeries a.val m *
        PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
          (integralPoleNumerator (generalPoleCenters (p := p)) g r)) := by ring
    _ = _ := by rw [he]; ring

theorem parameterPulledValue_integer_test (lam : ℚ)
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
          rationalPolynomialSeries (F.comp (C (p : ℚ) * X - C (a.val : ℚ))))
    (T : ℤ[X]) :
    let gT := integralPoleMulRegular (generalPoleCenters (p := p))
      (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) g r
    let rT := integralPoleMulResidue (generalPoleCenters (p := p))
      (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) r
    c * parameterPulledValue lam hreg Y m (F * T.map (Int.castRingHom ℚ)) a =
      (generalPoleU (lam ^ p) hunit hreg gT rT).eval₂
        (algebraMap ℤ_[p] ℚ_[p]) Y -
      (a.val : ℚ_[p]) / (p : ℚ_[p]) *
        (generalPoleV (lam ^ p) hunit hreg gT rT).eval₂
          (algebraMap ℤ_[p] ℚ_[p]) Y := by
  apply parameterPulledValue_integral_of_cleared lam hunit hreg Y m hm
  · exact integralPoleMulRegular_isRestricted _ _ _
      (polynomial_isRestricted _) hg _
  · exact general_original_test_integral_cleared m F a c g r he T

#print axioms general_original_test_integral_cleared
#print axioms parameterPulledValue_integer_test

end
end Li2Unified.Proofs.Hermite

end

section
/-! Exact unit and integrality input for lambda=1/q. These results do
not assert any congruence for the original determinant matrix. -/
namespace Li2Unified.ParameterFamily
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def inverseParameter (q : ℕ) : ℚ := (q : ℚ)⁻¹

lemma nat_valuation_zero (q : ℕ) (h : ¬p ∣ q) : padicValRat p (q:ℚ) = 0 := by
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h]
  rfl

lemma inverseParameter_unit (q : ℕ) (hq : 0 < q) (hpq : ¬p ∣ q) :
    inverseParameter q ≠ 0 ∧ padicValRat p (inverseParameter q) = 0 := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  refine ⟨inv_ne_zero hq0, ?_⟩
  rw [inverseParameter, padicValRat.inv, nat_valuation_zero q hpq, neg_zero]

lemma one_sub_inverseParameter (q : ℕ) (hq : 1 < q) :
    1-inverseParameter q = ((q-1:ℕ):ℚ)/(q:ℚ) := by
  have hq0 : (q:ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one, inverseParameter]
  field_simp

lemma inverseParameter_one_sub_unit (q : ℕ) (hq : 1 < q)
    (hpq : ¬p ∣ q) (hpm : ¬p ∣ q-1) :
    1-inverseParameter q ≠ 0 ∧ padicValRat p (1-inverseParameter q) = 0 := by
  have hq0 : (q:ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hm0 : ((q-1:ℕ):ℚ) ≠ 0 := by exact_mod_cast (by omega : q-1 ≠ 0)
  rw [one_sub_inverseParameter q hq]
  refine ⟨div_ne_zero hm0 hq0, ?_⟩
  rw [padicValRat.div hm0 hq0, nat_valuation_zero (q-1) hpm,
    nat_valuation_zero q hpq, sub_self]

lemma inverseParameter_prime_pow_congr (q : ℕ) (hq : 0 < q) (hpq : ¬p ∣ q) :
    Li2.VG p ((inverseParameter q)^p-inverseParameter q) 1 := by
  have hmod : (((q:ℤ)-(q:ℤ)^p : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.pow_card, sub_self]
  have hdiv : (p:ℤ) ∣ (q:ℤ)-(q:ℤ)^p :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
  have hnum : Li2.VG p ((q:ℚ)-(q:ℚ)^p) 1 := by
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast] using
      Li2.VG.intCast_of_dvd hdiv
  have hq0 : (q:ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hval : padicValRat p ((q:ℚ)^p) = 0 := by
    rw [padicValRat.pow hq0, nat_valuation_zero q hpq]
    simp
  have hi : Li2.VG p ((q:ℚ)^p)⁻¹ 0 := by
    simpa using Li2.VG.inv (p := p) (pow_ne_zero _ hq0)
      (show (padicValRat p ((q:ℚ)^p):ℚ) ≤ 0 by rw [hval]; norm_num)
  have hiq : Li2.VG p (q:ℚ)⁻¹ 0 := by
    simpa using Li2.VG.inv (p := p) hq0
      (show (padicValRat p (q:ℚ):ℚ) ≤ 0 by rw [nat_valuation_zero q hpq]; norm_num)
  have he : (inverseParameter q)^p-inverseParameter q =
      ((q:ℚ)-(q:ℚ)^p)*((q:ℚ)^p)⁻¹*(q:ℚ)⁻¹ := by
    rw [inverseParameter, inv_pow]
    field_simp
    <;> ring
  rw [he]
  simpa only [add_zero] using (hnum.mul hi).mul hiq

lemma inverseParameter_power_unit (q : ℕ) (hq : 0 < q) (hpq : ¬p ∣ q) :
    (inverseParameter q)^p ≠ 0 ∧ padicValRat p ((inverseParameter q)^p) = 0 := by
  obtain ⟨h0,hv⟩ := inverseParameter_unit (p := p) q hq hpq
  refine ⟨pow_ne_zero _ h0, ?_⟩
  rw [padicValRat.pow h0, hv]
  simp

lemma inverseParameter_power_one_sub_unit (q : ℕ) (hq : 1 < q)
    (hpq : ¬p ∣ q) (hpm : ¬p ∣ q-1) :
    1-(inverseParameter q)^p ≠ 0 ∧ padicValRat p (1-(inverseParameter q)^p) = 0 := by
  obtain ⟨h0,hv⟩ := inverseParameter_one_sub_unit (p := p) q hq hpq hpm
  apply Li2.unit_of_VG_sub h0 hv
  have h := (inverseParameter_prime_pow_congr (p := p) q (by omega) hpq).neg
  convert h using 1 <;> ring

lemma moment_ratio_integral_of_units (z : ℚ) (hz : z ≠ 0) (hv : padicValRat p z = 0)
    (h1 : 1-z ≠ 0) (hv1 : padicValRat p (1-z) = 0) : Li2.VG p (z/(1-z)) 0 := by
  right
  rw [padicValRat.div hz h1, hv, hv1]
  norm_num

lemma inverseParameter_moment_integral (q : ℕ) (hq : 1 < q)
    (hpq : ¬p ∣ q) (hpm : ¬p ∣ q-1) :
    Li2.VG p (inverseParameter q/(1-inverseParameter q)) 0 := by
  obtain ⟨h0,hv⟩ := inverseParameter_unit (p := p) q (by omega) hpq
  obtain ⟨h1,hv1⟩ := inverseParameter_one_sub_unit (p := p) q hq hpq hpm
  exact moment_ratio_integral_of_units _ h0 hv h1 hv1

lemma inverseParameter_power_moment_integral (q : ℕ) (hq : 1 < q)
    (hpq : ¬p ∣ q) (hpm : ¬p ∣ q-1) :
    Li2.VG p ((inverseParameter q)^p/(1-(inverseParameter q)^p)) 0 := by
  obtain ⟨h0,hv⟩ := inverseParameter_power_unit (p := p) q (by omega) hpq
  obtain ⟨h1,hv1⟩ := inverseParameter_power_one_sub_unit (p := p) q hq hpq hpm
  exact moment_ratio_integral_of_units _ h0 hv h1 hv1

/-- Rational formulas from the manuscript, not yet determinants of Lean blocks. -/
def lowBlockConstant (lam : ℚ) : ℚ := -(lam+12)*(13*lam-12)/(8*lam^3*(lam-1))
def cornerBlockConstant (lam : ℚ) : ℚ :=
  -4*(185*lam^5-767*lam^4+1711*lam^3+1724*lam^2-5616*lam+2880)/(3*lam^3*(lam-1)^2)

end
end Li2Unified.ParameterFamily

end

section
namespace Li2Unified.LambdaLift
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma parameter_power_unit (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0) :
    lam^p ≠ 0 ∧ padicValRat p (lam^p) = 0 := by
  refine ⟨pow_ne_zero _ hu.1, ?_⟩
  rw [padicValRat.pow hu.1, hu.2]
  simp

lemma one_sub_parameter_power_unit (lam : ℚ)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : Li2.VG p (lam^p-lam) 1) :
    1-lam^p ≠ 0 ∧ padicValRat p (1-lam^p) = 0 := by
  apply Li2.unit_of_VG_sub hone.1 hone.2
  have h := hferm.neg
  convert h using 1 <;> ring

theorem parameter_all_moments_congr (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : Li2.VG p (lam^p-lam) 1) (k : ℕ) :
    Li2.VG p (Li2.parameterMoment (lam^p) k - Li2.parameterMoment lam k) 1 := by
  have hup := parameter_power_unit lam hu
  have honep := one_sub_parameter_power_unit lam hone hferm
  have hr := Li2Unified.ParameterFamily.moment_ratio_integral_of_units
    (p := p) lam hu.1 hu.2 hone.1 hone.2
  have hrp := Li2Unified.ParameterFamily.moment_ratio_integral_of_units
    (p := p) (lam^p) hup.1 hup.2 honep.1 honep.2
  have hip := Li2.rational_unit_inverse_VG (p := p)
    (1-lam^p) honep.1 honep.2
  have hi := Li2.rational_unit_inverse_VG (p := p)
    (1-lam) hone.1 hone.2
  have hratio : Li2.VG p (lam^p/(1-lam^p)-lam/(1-lam)) 1 := by
    have he : lam^p/(1-lam^p)-lam/(1-lam) =
        (lam^p-lam)*(1-lam^p)⁻¹*(1-lam)⁻¹ := by
      field_simp [honep.1, hone.1]
      <;> ring
    rw [he]
    simpa only [add_zero] using (hferm.mul hip).mul hi
  exact Li2.parameterMoment_congr p (lam^p) lam 1 hrp hr hratio k

end
end Li2Unified.LambdaLift

end


end
