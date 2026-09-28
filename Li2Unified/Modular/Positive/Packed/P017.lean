module
public import Li2Unified.Modular.Positive.Packed.P016
public import Li2Unified.Modular.Base.PoleWindowReversal
public import Li2Unified.Modular.Positive.Packed.P014
public import Li2Unified.Modular.Base.OriginalFunctionalAssembly
public import Li2Unified.Modular.Positive.Packed.P015

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- The actual rational pole factor, evaluated at the independently constructed
local window origin and its common affine coordinate. -/
theorem parameterPoleFactor_eval₂ (lam : ℚ)
    (hzne : lam ≠ 0) (hz0 : Li2.VG p (lam ^ p) 0)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0)
    (hz1 : lam ^ p ≠ 1) (Y : ℚ_[p]) (j : ℕ) :
    (C ((j : ℚ) * lam⁻¹ ^ j) *
        (X - C (Li2.parameterTau lam j)) : ℚ[X]).eval₂
          (Rat.castHom ℚ_[p])
          (parameterPoleEta lam hz + (p : ℚ_[p])⁻¹ ^ 2 * Y) =
      (j : ℚ_[p]) * parameterPoleWindow lam hz Y j := by
  rw [parameterPoleWindow_affine lam hzne hz0 hz hz1 Y j]
  simp only [eval₂_mul, eval₂_C, eval₂_sub, eval₂_X,
    Rat.coe_castHom, Rat.cast_mul, Rat.cast_pow, Rat.cast_inv]
  push_cast
  ring

/-- The pole contribution in the literal parameter numerator, with its original
residues and original finite pole range, equals a sum of local windows. -/
theorem rawPoleFiber_eval₂ (lam : ℚ) (m : ℕ) (a : Fin p) (F : ℚ[X])
    (hzne : lam ≠ 0) (hz0 : Li2.VG p (lam ^ p) 0)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0)
    (hz1 : lam ^ p ≠ 1) (Y : ℚ_[p]) :
    (rawPoleFiber lam m p a F).eval₂ (Rat.castHom ℚ_[p])
        (parameterPoleEta lam hz + (p : ℚ_[p])⁻¹ ^ 2 * Y) =
      ∑ j ∈ (Finset.Icc 1 m).filter (fun j => j % p = a.val),
        ((F.eval (-(j : ℚ)) /
          ∏ l ∈ (Finset.Icc 1 m).erase j, ((l : ℚ) - (j : ℚ)) : ℚ) : ℚ_[p]) *
          ((j : ℚ_[p]) * parameterPoleWindow lam hz Y j) := by
  unfold rawPoleFiber
  rw [eval₂_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [eval₂_mul, eval₂_C, Rat.coe_castHom]
  rw [parameterPoleFactor_eval₂ lam hzne hz0 hz hz1 Y j]

/-- A single affine coordinate shared by every pole disc. -/
def parameterPoleShiftY (lam : ℚ)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0)
    (x : ℚ_[p]) : ℚ_[p] :=
  (p : ℚ_[p]) ^ 2 * (x - parameterPoleEta lam hz)

theorem parameterPoleShiftY_recover (lam : ℚ)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0)
    (x : ℚ_[p]) :
    parameterPoleEta lam hz +
      (p : ℚ_[p])⁻¹ ^ 2 * parameterPoleShiftY lam hz x = x := by
  unfold parameterPoleShiftY
  have hp : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp [hp]
  ring

theorem parameterPoleFactor_eval₂_at (lam : ℚ)
    (hzne : lam ≠ 0) (hz0 : Li2.VG p (lam ^ p) 0)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0)
    (hz1 : lam ^ p ≠ 1) (x : ℚ_[p]) (j : ℕ) :
    (C ((j : ℚ) * lam⁻¹ ^ j) *
        (X - C (Li2.parameterTau lam j)) : ℚ[X]).eval₂
          (Rat.castHom ℚ_[p]) x =
      (j : ℚ_[p]) * parameterPoleWindow lam hz
        (parameterPoleShiftY lam hz x) j := by
  simpa only [parameterPoleShiftY_recover] using
    (parameterPoleFactor_eval₂ lam hzne hz0 hz hz1
      (parameterPoleShiftY lam hz x) j)

theorem rawPoleFiber_eval₂_at (lam : ℚ) (m : ℕ) (a : Fin p) (F : ℚ[X])
    (hzne : lam ≠ 0) (hz0 : Li2.VG p (lam ^ p) 0)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0)
    (hz1 : lam ^ p ≠ 1) (x : ℚ_[p]) :
    (rawPoleFiber lam m p a F).eval₂ (Rat.castHom ℚ_[p]) x =
      ∑ j ∈ (Finset.Icc 1 m).filter (fun j => j % p = a.val),
        ((F.eval (-(j : ℚ)) /
          ∏ l ∈ (Finset.Icc 1 m).erase j, ((l : ℚ) - (j : ℚ)) : ℚ) : ℚ_[p]) *
          ((j : ℚ_[p]) * parameterPoleWindow lam hz
            (parameterPoleShiftY lam hz x) j) := by
  simpa only [parameterPoleShiftY_recover] using
    (rawPoleFiber_eval₂ lam m a F hzne hz0 hz hz1
      (parameterPoleShiftY lam hz x))

/-- The literal parameter numerator, including its polynomial quotient and all
original residues, decomposed on the same affine coordinate. -/
theorem numeratorFunctional_eval₂_local (lam : ℚ) (m : ℕ) (F : ℚ[X])
    (hlam : |(lam : ℝ)| < 1) (hzne : lam ≠ 0)
    (hz0 : Li2.VG p (lam ^ p) 0)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0)
    (hz1 : lam ^ p ≠ 1) (x : ℚ_[p]) :
    (Li2Unified.ParameterFamily.numeratorFunctional lam m F).eval₂
        (Rat.castHom ℚ_[p]) x =
      ∑ a : Fin p,
        (
        (polynomialFiber lam m p a F).eval₂ (Rat.castHom ℚ_[p]) x +
          ∑ j ∈ (Finset.Icc 1 m).filter (fun j => j % p = a.val),
            ((F.eval (-(j : ℚ)) /
              ∏ l ∈ (Finset.Icc 1 m).erase j,
                ((l : ℚ) - (j : ℚ)) : ℚ) : ℚ_[p]) *
              ((j : ℚ_[p]) * parameterPoleWindow lam hz
                (parameterPoleShiftY lam hz x) j)) := by
  rw [numeratorFunctional_fiberwise lam m p hlam hzne
    (Fact.out : p.Prime).pos F]
  rw [eval₂_finset_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [localActualFunctional, eval₂_add,
    rawPoleFiber_eval₂_at lam m a F hzne hz0 hz hz1 x]

#print axioms parameterPoleFactor_eval₂_at
#print axioms rawPoleFiber_eval₂_at
#print axioms numeratorFunctional_eval₂_local

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- The independently constructed local square-pole value on disc `a`.
Every disc receives every original pole before the global sum. -/
def parameterPulledSimplePole (lam : ℚ)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0)
    (Y : ℚ_[p]) (j : ℕ) (a : Fin p) : ℚ_[p] :=
  (j : ℚ_[p]) * parameterDissectedSquare (lam ^ p) hz Y
    (j + (p - 1 - a.val))

theorem parameterPulledSimplePole_sum (lam : ℚ)
    (hzne : lam ≠ 0) (hz0 : Li2.VG p (lam ^ p) 0)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0)
    (hz1 : lam ^ p ≠ 1) (x : ℚ_[p]) (j : ℕ) :
    (∑ a : Fin p, (lam : ℚ_[p])⁻¹ ^ a.val *
      parameterPulledSimplePole lam hz (parameterPoleShiftY lam hz x) j a) =
      (j : ℚ_[p]) * (lam : ℚ_[p])⁻¹ ^ j *
        (x - (Li2.parameterTau lam j : ℚ_[p])) := by
  have hl : (lam : ℚ_[p]) ≠ 0 := by exact_mod_cast hzne
  have hr := Li2.poleDissectionWindow_reverse (lam : ℚ_[p]) hl p
    (parameterDissectedSquare (lam ^ p) hz (parameterPoleShiftY lam hz x)) j
  rw [← Fin.sum_univ_eq_sum_range] at hr
  have hw : parameterPoleWindow lam hz (parameterPoleShiftY lam hz x) j =
      ∑ a : Fin p, (lam : ℚ_[p])⁻¹ ^ a.val *
        parameterDissectedSquare (lam ^ p) hz
          (parameterPoleShiftY lam hz x) (j + (p - 1 - a.val)) := by
    simpa only [parameterPoleWindow] using hr
  calc
    _ = (j : ℚ_[p]) * parameterPoleWindow lam hz
          (parameterPoleShiftY lam hz x) j := by
      rw [hw, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [parameterPulledSimplePole]
      ring
    _ = _ := by
      rw [parameterPoleWindow_affine lam hzne hz0 hz hz1]
      rw [parameterPoleShiftY_recover]
      ring

#print axioms parameterPulledSimplePole_sum

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- The local value is assembled from the original polynomial quotient and
every original residue, with the independently constructed square-pole value. -/
def parameterPulledValue (lam : ℚ)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0)
    (Y : ℚ_[p]) (m : ℕ) (F : ℚ[X]) (a : Fin p) : ℚ_[p] :=
  let P := (F /ₘ Li2.D m).comp
    (C (p : ℚ) * X - C (a.val : ℚ))
  (Li2.parameterU (lam ^ p) P : ℚ_[p]) -
    (a.val : ℚ_[p]) / (p : ℚ_[p]) *
      (Li2.parameterV (lam ^ p) P : ℚ_[p]) +
    ∑ j ∈ Finset.Icc 1 m,
      ((F.eval (-(j : ℚ)) /
        ∏ l ∈ (Finset.Icc 1 m).erase j,
          ((l : ℚ) - (j : ℚ)) : ℚ) : ℚ_[p]) *
        parameterPulledSimplePole lam hz Y j a

theorem numeratorFunctional_pulled_eval (lam : ℚ) (m : ℕ) (F : ℚ[X])
    (hlam : |(lam : ℝ)| < 1) (hzne : lam ≠ 0)
    (hz0 : Li2.VG p (lam ^ p) 0)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0)
    (hz1 : lam ^ p ≠ 1) (x : ℚ_[p]) :
    (Li2Unified.ParameterFamily.numeratorFunctional lam m F).eval₂
        (Rat.castHom ℚ_[p]) x =
      ∑ a : Fin p, (lam : ℚ_[p])⁻¹ ^ a.val *
        parameterPulledValue lam hz (parameterPoleShiftY lam hz x) m F a := by
  have hnorm : ‖(lam : ℝ)‖ < 1 := by
    simpa [Real.norm_eq_abs] using hlam
  have hpoly := Li2.parameterU_dissection lam hnorm hzne p
    (Fact.out : p.Prime).pos (F /ₘ Li2.D m)
  have hpolyCast := congrArg (fun q : ℚ => (q : ℚ_[p])) hpoly
  push_cast at hpolyCast
  unfold Li2Unified.ParameterFamily.numeratorFunctional
  simp only [eval₂_add, eval₂_C, eval₂_finset_sum, eval₂_mul,
    eval₂_sub, eval₂_X, Rat.coe_castHom, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_pow, Rat.cast_inv]
  rw [hpolyCast]
  unfold parameterPulledValue
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hs := parameterPulledSimplePole_sum lam hzne hz0 hz hz1 x j
  rw [← hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  push_cast
  ring

#print axioms numeratorFunctional_pulled_eval

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2 Li2Unified.Proofs.Hermite
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem parameter_original_pulled_polynomial_UV (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (m : ℕ) (F : ℚ[X])
    (a : Fin p) (Y : ℚ_[p]) :
    (fieldParameterFourPoleU z hu hreg hp4
      (rationalPolynomialSeries ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ)))) 0).eval Y -
      (a.val:ℚ_[p])/(p:ℚ_[p])*(fieldParameterFourPoleV z hu hreg hp4
        (rationalPolynomialSeries ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ)))) 0).eval Y =
    (parameterU (z) ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ))):ℚ_[p]) -
      (a.val:ℚ_[p])/(p:ℚ_[p])*
        (parameterV (z) ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ))):ℚ_[p]) := by
  change (fieldParameterFourPoleU z hu hreg hp4
      (((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ))).map (Rat.castHom ℚ_[p]) :
        PowerSeries ℚ_[p]) 0).eval Y - (a.val:ℚ_[p])/(p:ℚ_[p])*
      (fieldParameterFourPoleV z hu hreg hp4
        (((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ))).map (Rat.castHom ℚ_[p]) :
          PowerSeries ℚ_[p]) 0).eval Y = _
  rw [fieldParameterFourPoleU_polynomial, fieldParameterFourPoleV_polynomial]


theorem parameter_original_pulled_simplePole_UV (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (Y : ℚ_[p])
    (j a : ℕ) (hj : j ≤ 4*p-4) (ha : a < p) :
    (j:ℚ_[p])*parameterDissectedSquare z hreg Y (j+(p-1-a)) =
      (fieldParameterFourPoleU z hu hreg hp4 (pulledPoleRegular j a)
        (pulledPoleResidue j a hj ha)).eval Y -
      (a:ℚ_[p])/(p:ℚ_[p])*(fieldParameterFourPoleV z hu hreg hp4
        (pulledPoleRegular j a) (pulledPoleResidue j a hj ha)).eval Y := by
  unfold pulledPoleRegular pulledPoleResidue
  by_cases hm : p ∣ j+(p-1-a)+1
  · simp only [dif_pos hm]
    rw [fieldParameterFourPoleU_single,fieldParameterFourPoleV_single]
    simp only [eval_mul,eval_C,eval_map]
    rw [parameterUPole_eval₂,parameterVPole_eval₂,
      ← parameter_matching_pole_contribution z hreg Y j a ha hm]
    dsimp only [primeMatchingPoleIndex]
    ring
  · simp only [dif_neg hm]
    rw [fieldParameterFourPoleU_regular,fieldParameterFourPoleV_regular,eval_C,eval_C,
      fieldRestrictedU_integral _ _ (padicReciprocalSeries_isRestricted _ _ _ _),
      fieldRestrictedV_integral _ _ (padicReciprocalSeries_isRestricted _ _ _ _)]
    exact (parameter_nonmatching_pole_contribution z hreg Y j a ha hm).symm

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameter_original_pulled_simplePole_UV

end

section
open Polynomial Li2 Li2Unified.Proofs.PrimeEdge
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalFieldPoleU_regular (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hreg : VG p (z / (1 - z)) 0)
    (f : PowerSeries ℚ_[p]) :
    generalFieldPoleU z hu hreg f 0 =
      C (fieldRestrictedU (integralParameterMoment z hreg) f) := by
  simp [generalFieldPoleU, fieldPoleFunctional, fieldRestrictedU]

theorem generalFieldPoleV_regular (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hreg : VG p (z / (1 - z)) 0)
    (f : PowerSeries ℚ_[p]) :
    generalFieldPoleV z hu hreg f 0 =
      C (fieldRestrictedV (integralParameterMoment z hreg) f) := by
  simp [generalFieldPoleV, fieldPoleFunctional, fieldRestrictedV]

theorem general_original_pulled_polynomial_UV (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hreg : VG p (z / (1 - z)) 0)
    (m : ℕ) (F : ℚ[X]) (a : Fin p) (Y : ℚ_[p]) :
    (generalFieldPoleU z hu hreg
      (rationalPolynomialSeries ((F /ₘ D m).comp (C (p : ℚ) * X - C (a.val : ℚ)))) 0).eval Y -
      (a.val : ℚ_[p]) / (p : ℚ_[p]) *
        (generalFieldPoleV z hu hreg
          (rationalPolynomialSeries ((F /ₘ D m).comp (C (p : ℚ) * X - C (a.val : ℚ)))) 0).eval Y =
    (parameterU z ((F /ₘ D m).comp (C (p : ℚ) * X - C (a.val : ℚ))) : ℚ_[p]) -
      (a.val : ℚ_[p]) / (p : ℚ_[p]) *
        (parameterV z ((F /ₘ D m).comp (C (p : ℚ) * X - C (a.val : ℚ))) : ℚ_[p]) := by
  change (generalFieldPoleU z hu hreg
      (((F /ₘ D m).comp (C (p : ℚ) * X - C (a.val : ℚ))).map (Rat.castHom ℚ_[p]) :
        PowerSeries ℚ_[p]) 0).eval Y - (a.val : ℚ_[p]) / (p : ℚ_[p]) *
      (generalFieldPoleV z hu hreg
        (((F /ₘ D m).comp (C (p : ℚ) * X - C (a.val : ℚ))).map (Rat.castHom ℚ_[p]) :
          PowerSeries ℚ_[p]) 0).eval Y = _
  rw [generalFieldPoleU_polynomial, generalFieldPoleV_polynomial]

theorem general_original_pulled_simplePole_UV (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z / (1 - z)) 0) (Y : ℚ_[p])
    (m j : ℕ) (hm : m < p * p) (hj : j ≤ m) (a : Fin p) :
    (j : ℚ_[p]) * parameterDissectedSquare z hreg Y (j + (p - 1 - a.val)) =
      (generalFieldPoleU z hu hreg (pulledPoleRegular j a.val)
        (generalPulledPoleResidue m j hm hj a)).eval Y -
      (a.val : ℚ_[p]) / (p : ℚ_[p]) *
        (generalFieldPoleV z hu hreg (pulledPoleRegular j a.val)
          (generalPulledPoleResidue m j hm hj a)).eval Y := by
  by_cases hs : p ∣ j + (p - 1 - a.val) + 1
  · have hmod := matching_shift_mod p j a hs
    rw [pulledPoleRegular, generalPulledPoleResidue_matching m j hm hj a hmod]
    simp only [dif_pos hs]
    rw [generalFieldPoleU_single, generalFieldPoleV_single]
    simp only [eval_mul, eval_C, eval_map]
    rw [Li2Unified.Proofs.PrimeEdge.parameterUPole_eval₂,
      Li2Unified.Proofs.PrimeEdge.parameterVPole_eval₂,
      ← parameter_matching_pole_contribution z hreg Y j a.val a.isLt hs]
    have hidx := pulled_shift_index p m j a (Fact.out : p.Prime).pos hm hj hmod
    rw [hidx]
    ring
  · have hmod : j % p ≠ a.val := by
      intro h
      exact hs ((matching_shift_dvd_iff p j a).2 h)
    rw [pulledPoleRegular, generalPulledPoleResidue_nonmatching m j hm hj a hmod]
    simp only [dif_neg hs]
    rw [generalFieldPoleU_regular, generalFieldPoleV_regular, eval_C, eval_C,
      fieldRestrictedU_integral _ _ (padicReciprocalSeries_isRestricted _ _ _ _),
      fieldRestrictedV_integral _ _ (padicReciprocalSeries_isRestricted _ _ _ _)]
    exact (parameter_nonmatching_pole_contribution z hreg Y j a.val a.isLt hs).symm

#print axioms general_original_pulled_polynomial_UV
#print axioms general_original_pulled_simplePole_UV

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterPulledValue_generalField (lam : ℚ)
    (hunit : lam ^ p ≠ 0 ∧ padicValRat p (lam ^ p) = 0)
    (hreg : VG p (lam ^ p / (1 - lam ^ p)) 0) (Y : ℚ_[p])
    (m : ℕ) (hm : m < p * p) (F : ℚ[X]) (a : Fin p) :
    parameterPulledValue lam hreg Y m F a =
      (generalFieldPoleU (lam ^ p) hunit hreg (originalPulledRegular m F a)
        (generalOriginalPulledResidue m hm F a)).eval Y -
      (a.val : ℚ_[p]) / (p : ℚ_[p]) *
        (generalFieldPoleV (lam ^ p) hunit hreg (originalPulledRegular m F a)
          (generalOriginalPulledResidue m hm F a)).eval Y := by
  have hu := generalOriginal_fieldPoleFunctional
    (fun n : ℕ => ((n + 1 : ℕ) : ℤ_[p]) * integralParameterMoment (lam ^ p) hreg n)
    (fun k : Fin p =>
      (integralUPole (lam ^ p) hunit.1 hunit.2 k.val k.isLt).map
        (algebraMap ℤ_[p] ℚ_[p])) m hm F a
  have hv := generalOriginal_fieldPoleFunctional
    (derivativeMoments (integralParameterMoment (lam ^ p) hreg))
    (fun k : Fin p =>
      (integralVPole (lam ^ p) hunit.1 hunit.2 k.val k.isLt).map
        (algebraMap ℤ_[p] ℚ_[p])) m hm F a
  change _ = (fieldPoleFunctional _ _ _ _).eval Y -
    _ * (fieldPoleFunctional _ _ _ _).eval Y
  rw [hu, hv]
  simp only [eval_add, eval_finset_sum, eval_mul, eval_C]
  rw [mul_add, add_sub_add_comm]
  unfold parameterPulledValue
  dsimp only
  rw [← general_original_pulled_polynomial_UV (lam ^ p) hunit hreg m F a Y]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro j _
  unfold parameterPulledSimplePole
  rw [general_original_pulled_simplePole_UV (lam ^ p) hunit hreg Y
    m j.val hm (Finset.mem_Icc.mp j.property).2 a]
  simp only [originalResidue, Rat.cast_div, generalFieldPoleU, generalFieldPoleV]
  ring

#print axioms parameterPulledValue_generalField

end
end Li2Unified.Proofs.Hermite

end


end
