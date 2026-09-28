module
public import Li2Unified.Modular.Positive.Packed.P019
public import Li2Unified.Modular.Base.RationalPoleCongruence
public import Li2Unified.Modular.Base.RationalPoleParameter
public import Li2Unified.Modular.Base.RationalBaseEvaluation
public import Li2Unified.Modular.Base.RationalBaseCongruence
public import Li2Unified.Modular.Positive.Packed.P053
public import Li2Unified.Modular.Base.PrimeNormReduction
public import Li2Unified.Modular.Positive.Packed.P013
public import Li2Unified.Modular.Base.PrimeLocalLeadingBounds
public import Li2Unified.Modular.Base.PrimeMonomialLeading

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Finset
open scoped BigOperators
namespace Li2Unified.LambdaLift
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameter_inverse_pow_congr (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hferm : Li2.VG p (lam^p-lam) 1) (j : ℕ) :
    Li2.VG p ((lam^p)⁻¹^j-lam⁻¹^j) 1 := by
  have hup := parameter_power_unit lam hu
  have hip := Li2.rational_unit_inverse_VG (p := p) (lam^p) hup.1 hup.2
  have hi := Li2.rational_unit_inverse_VG (p := p) lam hu.1 hu.2
  have hbase : Li2.VG p ((lam^p)⁻¹-lam⁻¹) 1 :=
    Li2.VG.inv_congr hup.1 hu.1 hip hi hferm
  exact Li2.VG.pow_congr hip hi hbase j

theorem parameter_tau_congr (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hferm : Li2.VG p (lam^p-lam) 1)
    (j : ℕ) (hj : j < p) :
    Li2.VG p (Li2.parameterTau (lam^p) j-Li2.parameterTau lam j) 1 := by
  unfold Li2.parameterTau
  rw [← Finset.sum_sub_distrib]
  apply Li2.VG.sum
  intro b hb
  have hb0 := (Finset.mem_Icc.mp hb).1
  have hbp : b < p := lt_of_le_of_lt (Finset.mem_Icc.mp hb).2 hj
  have hv : padicValRat p (b:ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd
      (Nat.not_dvd_of_pos_of_lt (by omega) hbp)]
    rfl
  have hi : Li2.VG p ((b:ℚ)⁻¹^2) 0 := by
    simpa using (Li2.rational_unit_inverse_VG (p := p) (b:ℚ)
      (by exact_mod_cast (by omega : b ≠ 0)) hv).pow 2
  have hup := parameter_power_unit lam hu
  have hl : Li2.VG p lam 0 := Or.inr (by rw [hu.2]; norm_num)
  have hlp : Li2.VG p (lam^p) 0 := Or.inr (by rw [hup.2]; norm_num)
  rw [← sub_div, div_eq_mul_inv, ← inv_pow]
  simpa using (Li2.VG.pow_congr hlp hl hferm b).mul hi

theorem parameterG_congr (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : Li2.VG p (lam^p-lam) 1)
    (f : ℚ[X]) (hf : Li2.GV p f 0) :
    Li2.VG p (Li2.parameterG (lam^p) f-Li2.parameterG lam f) 1 := by
  unfold Li2.parameterG Polynomial.sum
  rw [← Finset.sum_sub_distrib]
  apply Li2.VG.sum
  intro k _
  rw [← mul_sub]
  simpa using (hf k).mul (parameter_all_moments_congr lam hu hone hferm k)

theorem parameterU_congr (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : Li2.VG p (lam^p-lam) 1)
    (f : ℚ[X]) (hf : Li2.GV p f 0) :
    Li2.VG p (Li2.parameterU (lam^p) f-Li2.parameterU lam f) 1 := by
  apply parameterG_congr lam hu hone hferm
  have hprod : Li2.GV p (X*f) 0 := by simpa using (Li2.GV.X (p := p)).mul hf
  exact hprod.derivative

theorem parameterV_congr (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : Li2.VG p (lam^p-lam) 1)
    (f : ℚ[X]) (hf : Li2.GV p f 0) :
    Li2.VG p (Li2.parameterV (lam^p) f-Li2.parameterV lam f) 1 :=
  parameterG_congr lam hu hone hferm _ hf.derivative

end
end Li2Unified.LambdaLift

end

section
open Polynomial Finset
open scoped BigOperators
namespace Li2Unified.LambdaLift
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem rationalPoleTerm_congr (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hferm : Li2.VG p (lam^p-lam) 1)
    (a : ℚ) (ha : Li2.VG p a 0)
    (j : ℕ) (hj : j < p) :
    Li2.GV p
      (C (a*(lam^p)⁻¹^j)*(X-C (Li2.parameterTau (lam^p) j)) -
       C (a*lam⁻¹^j)*(X-C (Li2.parameterTau lam j))) 1 := by
  have hup := parameter_power_unit lam hu
  have hi := Li2.rational_unit_inverse_VG (p := p) lam hu.1 hu.2
  have hlp : Li2.VG p (lam^p) 0 := Or.inr (by rw [hup.2]; norm_num)
  apply Li2.GV.mul_congr
  · exact Li2.GV.X.sub
      (Li2.GV.C (Li2.parameterTau_VG (lam^p) hlp j hj))
  · exact Li2.GV.C (by simpa using ha.mul (hi.pow j))
  · rw [← map_sub, ← mul_sub]
    exact Li2.GV.C (by
      simpa using (ha.mul (parameter_inverse_pow_congr lam hu hferm j)))
  · have h := (Li2.GV.C (parameter_tau_congr lam hu hferm j hj)).neg
    convert h using 1 <;> simp only [map_neg, map_sub] <;> ring

theorem rationalPoleU_congr (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : Li2.VG p (lam^p-lam) 1)
    (hp4 : 3 < p) (f : ℚ[X]) (r : Fin 4 → ℚ)
    (hf : Li2.GV p f 0) (hr : ∀ j, Li2.VG p (r j) 0) :
    Li2.GV p (Li2.rationalPoleU (lam^p) f r-Li2.rationalPoleU lam f r) 1 := by
  unfold Li2.rationalPoleU
  rw [add_sub_add_comm, ← map_sub, ← Finset.sum_sub_distrib]
  apply (Li2.GV.C (parameterU_congr lam hu hone hferm f hf)).add
  apply Li2.GV.sum
  intro j _
  exact rationalPoleTerm_congr lam hu hferm (r j*(j.val:ℚ))
    (by simpa using (hr j).mul (Li2.VG.natCast (p := p) j.val))
    j.val (by omega)

theorem rationalPoleV_congr (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : Li2.VG p (lam^p-lam) 1)
    (hp4 : 3 < p) (f : ℚ[X]) (r : Fin 4 → ℚ)
    (hf : Li2.GV p f 0) (hr : ∀ j, Li2.VG p (r j) 0) :
    Li2.GV p (Li2.rationalPoleV (lam^p) f r-Li2.rationalPoleV lam f r) 1 := by
  unfold Li2.rationalPoleV
  rw [add_sub_add_comm, ← map_sub, ← Finset.sum_sub_distrib]
  apply (Li2.GV.C (parameterV_congr lam hu hone hferm f hf)).add
  apply Li2.GV.sum
  intro j _
  exact rationalPoleTerm_congr lam hu hferm (-r j) (hr j).neg j.val (by omega)

end
end Li2Unified.LambdaLift

end

section
namespace Li2Unified.LambdaLift
noncomputable section

def zeroShapeUValue (lam : ℚ) (k : Fin 5) : ℚ :=
  (Li2.rationalPoleU lam (Li2.zeroShapeRegular k)
    (Li2.zeroShapeResidue k)).eval 0

def lowShapeVValue (lam : ℚ) (k : Fin 3) : ℚ :=
  (Li2.rationalPoleV lam
    (Li2.zeroShapeRegular ⟨k.val+2, by omega⟩)
    (Li2.zeroShapeResidue ⟨k.val+2, by omega⟩)).eval 0

def highShapeVValue (lam : ℚ) (k : Fin 3) : ℚ :=
  (Li2.rationalPoleV lam (Li2.highShapeRegular k)
    (Li2.highShapeResidue k)).eval 0

end
end Li2Unified.LambdaLift

end

section
open Polynomial
namespace Li2Unified.LambdaLift
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem zeroShape_U_congr (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : Li2.VG p (lam^p-lam) 1)
    (hp4 : 3 < p) (k : Fin 5) :
    Li2.VG p ((Li2.rationalPoleU (lam^p)
      (Li2.zeroShapeRegular k) (Li2.zeroShapeResidue k)).eval 0 -
      zeroShapeUValue lam k) 1 := by
  have h := rationalPoleU_congr lam hu hone hferm hp4 _ _
    (Li2.zeroShapeRegular_integral k)
    (Li2.zeroShapeResidue_integral hp4 k)
  simpa only [coeff_sub, coeff_zero_eq_eval_zero, eval_sub, zeroShapeUValue] using h 0

theorem lowShape_V_congr (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : Li2.VG p (lam^p-lam) 1)
    (hp4 : 3 < p) (k : Fin 3) :
    Li2.VG p ((Li2.rationalPoleV (lam^p)
      (Li2.zeroShapeRegular ⟨k.val+2, by omega⟩)
      (Li2.zeroShapeResidue ⟨k.val+2, by omega⟩)).eval 0 -
      lowShapeVValue lam k) 1 := by
  have h := rationalPoleV_congr lam hu hone hferm hp4 _ _
    (Li2.zeroShapeRegular_integral ⟨k.val+2, by omega⟩)
    (Li2.zeroShapeResidue_integral hp4 ⟨k.val+2, by omega⟩)
  simpa only [coeff_sub, coeff_zero_eq_eval_zero, eval_sub, lowShapeVValue] using h 0

theorem highShape_V_congr (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : Li2.VG p (lam^p-lam) 1)
    (hp4 : 3 < p) (k : Fin 3) :
    Li2.VG p ((Li2.rationalPoleV (lam^p)
      (Li2.highShapeRegular k) (Li2.highShapeResidue k)).eval 0 -
      highShapeVValue lam k) 1 := by
  have h := rationalPoleV_congr lam hu hone hferm hp4 _ _
    (Li2.highShapeRegular_integral k)
    (Li2.highShapeResidue_integral (p := p) k)
  simpa only [coeff_sub, coeff_zero_eq_eval_zero, eval_sub, highShapeVValue] using h 0

end
end Li2Unified.LambdaLift

end

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterPowerRatio_integral (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) : VG p (lam^p/(1-lam^p)) 0 := by
  have hup := parameter_power_unit lam hu
  have hop := one_sub_parameter_power_unit lam hone hferm
  exact Li2Unified.ParameterFamily.moment_ratio_integral_of_units
    (p := p) (lam^p) hup.1 hup.2 hop.1 hop.2

theorem parameterZeroShape_U_value_norm (lam : ℚ) (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (k : Fin 5) :
    let g := integralPoleMulRegular (primePoleCenters p)
      ((X^k.val : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) 0 (primeZeroShapeResidue hp4)
    let s := integralPoleMulResidue (primePoleCenters p)
      ((X^k.val : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) (primeZeroShapeResidue hp4)
    ‖(((parameterFourPoleU (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 g s).eval 0:ℤ_[p]):ℚ_[p]) -
      ((zeroShapeUValue lam k):ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  apply integralPolynomial_eval_zero_norm_of_rational
  · exact (parameterZeroShape_monomial_rational (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 k 0).1
  · exact zeroShape_U_congr lam hu hone hferm hp4 k

theorem parameterLowShape_V_value_norm (lam : ℚ) (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (k : Fin 3) :
    let g := integralPoleMulRegular (primePoleCenters p)
      ((X^k.val : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) 0 (primeLowShapeResidue hp4)
    let s := integralPoleMulResidue (primePoleCenters p)
      ((X^k.val : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) (primeLowShapeResidue hp4)
    ‖(((parameterFourPoleV (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 g s).eval 0:ℤ_[p]):ℚ_[p]) -
      ((lowShapeVValue lam k):ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  apply integralPolynomial_eval_zero_norm_of_rational
  · exact (parameterLowShape_monomial_rational (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 k 0).2
  · exact lowShape_V_congr lam hu hone hferm hp4 k

theorem parameterHighShape_V_value_norm (lam : ℚ) (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (k : Fin 3) :
    let g := integralPoleMulRegular (primePoleCenters p)
      ((X^k.val : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) 1 primeHighShapeResidue
    let s := integralPoleMulResidue (primePoleCenters p)
      ((X^k.val : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) primeHighShapeResidue
    ‖(((parameterFourPoleV (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 g s).eval 0:ℤ_[p]):ℚ_[p]) -
      ((highShapeVValue lam k):ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  apply integralPolynomial_eval_zero_norm_of_rational
  · exact (parameterHighShape_monomial_rational (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 k 0).2
  · exact highShape_V_congr lam hu hone hferm hp4 k

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterZeroShape_U_value_norm
#print axioms Li2Unified.Proofs.PrimeEdge.parameterLowShape_V_value_norm
#print axioms Li2Unified.Proofs.PrimeEdge.parameterHighShape_V_value_norm

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterDiscPole_U_error (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : ℕ) (ha : a < p)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin 4 → ℤ_[p]) (n : ℕ) :
    ‖(parameterFourPoleU z hu hreg hp4
        (integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a ha) f r)
        (integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a ha) r) -
      C (primeDiscUnitConstant a ha)*parameterFourPoleU z hu hreg hp4 f r).coeff n‖ ≤ ‖(p:ℤ_[p])‖ :=
  restrictedPoleFunctional_multiplier_error _ primePoleCenters_injective _ _ _ _
    (primeDiscUnit_isRestricted a ha) hf r _ _ (norm_nonneg _) (primeDiscUnit_constant_error a ha) n

theorem parameterDiscPole_V_error (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : ℕ) (ha : a < p)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin 4 → ℤ_[p]) (n : ℕ) :
    ‖(parameterFourPoleV z hu hreg hp4
        (integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a ha) f r)
        (integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a ha) r) -
      C (primeDiscUnitConstant a ha)*parameterFourPoleV z hu hreg hp4 f r).coeff n‖ ≤ ‖(p:ℤ_[p])‖ :=
  restrictedPoleFunctional_multiplier_error _ primePoleCenters_injective _ _ _ _
    (primeDiscUnit_isRestricted a ha) hf r _ _ (norm_nonneg _) (primeDiscUnit_constant_error a ha) n

theorem parameterDiscPole_U_substituted_leading (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : ℕ) (ha : a < p)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin 4 → ℤ_[p]) (eta : ℤ_[p]) (n : ℕ) :
    ‖((parameterFourPoleU z hu hreg hp4
        (integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a ha) f r)
        (integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a ha) r)).comp
          (C ((p:ℤ_[p])^2)*(X-C eta)) -
      C (primeDiscUnitConstant a ha*(parameterFourPoleU z hu hreg hp4 f r).eval 0)).coeff n‖ ≤ ‖(p:ℤ_[p])‖ := by
  have hs : ‖(p:ℤ_[p])^2‖ ≤ ‖(p:ℤ_[p])‖ := by
    simpa only [pow_two] using integral_coeff_mul_norm_le (p:ℤ_[p]) (p:ℤ_[p])
  simpa only [eval_mul, eval_C] using integralPolynomial_leading_substitution
    _ (C (primeDiscUnitConstant a ha)*parameterFourPoleU z hu hreg hp4 f r) ((p:ℤ_[p])^2) eta
    ‖(p:ℤ_[p])‖ (norm_nonneg _) hs (parameterDiscPole_U_error z hu hreg hp4 a ha f hf r) n

theorem parameterDiscPole_V_substituted_leading (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : ℕ) (ha : a < p)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin 4 → ℤ_[p]) (eta : ℤ_[p]) (n : ℕ) :
    ‖((parameterFourPoleV z hu hreg hp4
        (integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a ha) f r)
        (integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a ha) r)).comp
          (C ((p:ℤ_[p])^2)*(X-C eta)) -
      C (primeDiscUnitConstant a ha*(parameterFourPoleV z hu hreg hp4 f r).eval 0)).coeff n‖ ≤ ‖(p:ℤ_[p])‖ := by
  have hs : ‖(p:ℤ_[p])^2‖ ≤ ‖(p:ℤ_[p])‖ := by
    simpa only [pow_two] using integral_coeff_mul_norm_le (p:ℤ_[p]) (p:ℤ_[p])
  simpa only [eval_mul, eval_C] using integralPolynomial_leading_substitution
    _ (C (primeDiscUnitConstant a ha)*parameterFourPoleV z hu hreg hp4 f r) ((p:ℤ_[p])^2) eta
    ‖(p:ℤ_[p])‖ (norm_nonneg _) hs (parameterDiscPole_V_error z hu hreg hp4 a ha f hf r) n
theorem parameterDiscPole_U_substituted_rational (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : ℕ) (ha : a < p)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin 4 → ℤ_[p]) (eta : ℤ_[p]) (q : ℚ_[p])
    (hq : ‖(((parameterFourPoleU z hu hreg hp4 f r).eval 0:ℤ_[p]):ℚ_[p])-q‖ ≤ ‖(p:ℚ_[p])‖) (n : ℕ) :
    ‖(((parameterFourPoleU z hu hreg hp4
        (integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a ha) f r)
        (integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a ha) r)).comp
          (C ((p:ℤ_[p])^2)*(X-C eta))).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((primeDiscUnitConstant a ha:ℚ_[p])*q)).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  apply integralPolynomial_rational_constant_bound
    _ (primeDiscUnitConstant a ha*(parameterFourPoleU z hu hreg hp4 f r).eval 0) _
    (parameterDiscPole_U_substituted_leading z hu hreg hp4 a ha f hf r eta)
  have hmul : ‖(primeDiscUnitConstant a ha:ℚ_[p]) *
      ((((parameterFourPoleU z hu hreg hp4 f r).eval 0:ℤ_[p]):ℚ_[p])-q)‖ ≤ ‖(p:ℚ_[p])‖ := by
    rw [norm_mul]
    exact (mul_le_mul (PadicInt.norm_le_one _) hq (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul _)
  simpa only [PadicInt.coe_mul, mul_sub] using hmul

theorem parameterDiscPole_V_substituted_rational (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (a : ℕ) (ha : a < p)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin 4 → ℤ_[p]) (eta : ℤ_[p]) (q : ℚ_[p])
    (hq : ‖(((parameterFourPoleV z hu hreg hp4 f r).eval 0:ℤ_[p]):ℚ_[p])-q‖ ≤ ‖(p:ℚ_[p])‖) (n : ℕ) :
    ‖(((parameterFourPoleV z hu hreg hp4
        (integralPoleMulRegular (primePoleCenters p) (primeDiscUnit a ha) f r)
        (integralPoleMulResidue (primePoleCenters p) (primeDiscUnit a ha) r)).comp
          (C ((p:ℤ_[p])^2)*(X-C eta))).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((primeDiscUnitConstant a ha:ℚ_[p])*q)).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  apply integralPolynomial_rational_constant_bound
    _ (primeDiscUnitConstant a ha*(parameterFourPoleV z hu hreg hp4 f r).eval 0) _
    (parameterDiscPole_V_substituted_leading z hu hreg hp4 a ha f hf r eta)
  have hmul : ‖(primeDiscUnitConstant a ha:ℚ_[p]) *
      ((((parameterFourPoleV z hu hreg hp4 f r).eval 0:ℤ_[p]):ℚ_[p])-q)‖ ≤ ‖(p:ℚ_[p])‖ := by
    rw [norm_mul]
    exact (mul_le_mul (PadicInt.norm_le_one _) hq (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul _)
  simpa only [PadicInt.coe_mul, mul_sub] using hmul

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterDiscPole_U_substituted_rational
#print axioms Li2Unified.Proofs.PrimeEdge.parameterDiscPole_V_substituted_rational

end

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterDiscMonomial_zero_U_leading (lam : ℚ) (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (k : Fin 5)
    (eta : ℤ_[p]) (n : ℕ) :
    let a : Fin p := ⟨0,by omega⟩
    ‖(((parameterFourPoleU (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 (primeDiscMonomialRegular hp4 a k.val)
        (primeDiscMonomialResidue hp4 a k.val)).comp
        (C ((p:ℤ_[p])^2)*(X-C eta))).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((primeDiscUnitConstant (p := p) 0 (by omega):ℚ_[p]) *
        ((zeroShapeUValue lam k):ℚ_[p]))).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  dsimp only
  rw [(primeDiscMonomial_nested hp4 ⟨0,by omega⟩ k.val).1,
    (primeDiscMonomial_nested hp4 ⟨0,by omega⟩ k.val).2]
  simp only [primeDiscBaseRegular, primeDiscBaseResidue, if_pos rfl]
  apply parameterDiscPole_U_substituted_rational
  · exact integralPoleMulRegular_isRestricted _ _ _ (polynomial_isRestricted _)
      (PowerSeries.IsRestricted.zero 1) _
  · exact parameterZeroShape_U_value_norm lam hu hone hferm hp4 k

theorem parameterDiscMonomial_low_V_leading (lam : ℚ) (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (k : Fin 3) (eta : ℤ_[p]) (n : ℕ) :
    ‖(((parameterFourPoleV (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 (primeDiscMonomialRegular hp4 a k.val)
        (primeDiscMonomialResidue hp4 a k.val)).comp
        (C ((p:ℤ_[p])^2)*(X-C eta))).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((primeDiscUnitConstant a.val a.isLt:ℚ_[p]) *
        ((lowShapeVValue lam k):ℚ_[p]))).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  rw [(primeDiscMonomial_nested hp4 a k.val).1, (primeDiscMonomial_nested hp4 a k.val).2]
  simp only [primeDiscBaseRegular, primeDiscBaseResidue, if_neg (by omega : a.val ≠ 0), if_pos ha]
  apply parameterDiscPole_V_substituted_rational
  · exact integralPoleMulRegular_isRestricted _ _ _ (polynomial_isRestricted _)
      (PowerSeries.IsRestricted.zero 1) _
  · exact parameterLowShape_V_value_norm lam hu hone hferm hp4 k

theorem parameterDiscMonomial_high_V_leading (lam : ℚ) (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (a : Fin p)
    (ha : p-4 < a.val) (k : Fin 3) (eta : ℤ_[p]) (n : ℕ) :
    ‖(((parameterFourPoleV (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 (primeDiscMonomialRegular hp4 a k.val)
        (primeDiscMonomialResidue hp4 a k.val)).comp
        (C ((p:ℤ_[p])^2)*(X-C eta))).map (algebraMap ℤ_[p] ℚ_[p]) -
      C ((primeDiscUnitConstant a.val a.isLt:ℚ_[p]) *
        ((highShapeVValue lam k):ℚ_[p]))).coeff n‖ ≤ ‖(p:ℚ_[p])‖ := by
  rw [(primeDiscMonomial_nested hp4 a k.val).1, (primeDiscMonomial_nested hp4 a k.val).2]
  simp only [primeDiscBaseRegular, primeDiscBaseResidue, if_neg (by omega : a.val ≠ 0),
    if_neg (by omega : ¬a.val ≤ p-4)]
  apply parameterDiscPole_V_substituted_rational
  · exact integralPoleMulRegular_isRestricted _ _ _ (polynomial_isRestricted _)
      (PowerSeries.IsRestricted.one 1) _
  · exact parameterHighShape_V_value_norm lam hu hone hferm hp4 k

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterDiscMonomial_zero_U_leading
#print axioms Li2Unified.Proofs.PrimeEdge.parameterDiscMonomial_low_V_leading
#print axioms Li2Unified.Proofs.PrimeEdge.parameterDiscMonomial_high_V_leading

end


end
